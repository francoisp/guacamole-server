/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */

#include "display-plan.h"
#include "display-priv.h"
#include "guacamole/client.h"
#include "guacamole/display.h"
#include "guacamole/fifo.h"
#include "guacamole/layer.h"
#include "guacamole/protocol-types.h"
#include "guacamole/protocol.h"
#include "guacamole/rect.h"
#include "guacamole/rwlock.h"
#include "guacamole/socket.h"
#include "guacamole/timestamp.h"
#include "guacamole/recording.h"

#include <inttypes.h>
#include <limits.h>
#include <cairo/cairo.h>
#include <pthread.h>
#include <stdlib.h> /* getenv */
#include <stdio.h>  /* snprintf */
#include <dirent.h>
#include <errno.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

/**
 * Represents a discovered screenshot file with parsed timestamp.
 */
typedef struct guac_screenshot_file {
    char path[4096];
    uint64_t ts_ms;
    unsigned frame_seq;
} guac_screenshot_file;

/**
 * Basic dynamic array for 64-bit bucket keys with associated counts.
 */
typedef struct bucket_count_entry {
    uint64_t key;
    int count;
} bucket_count_entry;

static int bucket_count_get_index(bucket_count_entry* entries, int used, uint64_t key) {
    for (int i = 0; i < used; i++) {
        if (entries[i].key == key) return i;
    }
    return -1;
}

/**
 * Compares two screenshot files by timestamp descending, then frame_seq descending.
 */
static int compare_sshot_desc(const void* a, const void* b) {
    const guac_screenshot_file* fa = (const guac_screenshot_file*) a;
    const guac_screenshot_file* fb = (const guac_screenshot_file*) b;
    if (fa->ts_ms < fb->ts_ms) return 1;
    if (fa->ts_ms > fb->ts_ms) return -1;
    if (fa->frame_seq < fb->frame_seq) return 1;
    if (fa->frame_seq > fb->frame_seq) return -1;
    return 0;
}

/**
 * Prunes screenshots in the given directory based on the following policy:
 * - For age <= 60s: keep up to 20 per second (newest 20 per-second bucket)
 * - For 60s < age <= 1h: keep at most 1 per minute (newest per-minute bucket)
 * - For 1h < age <= 24h: keep at most 1 per 5 minutes (newest per 5-minute bucket)
 * - For 24h < age <= 30d: keep at most 1 per hour (newest per-hour bucket)
 * - For age > 30d: delete
 */
static bucket_count_entry* upsert_bucket(bucket_count_entry** arr, int* used, int* cap, uint64_t key) {
    int idx = bucket_count_get_index(*arr, *used, key);
    if (idx >= 0) return &((*arr)[idx]);
    if (*used == *cap) {
        int new_cap = (*cap == 0) ? 64 : (*cap * 2);
        bucket_count_entry* na = (bucket_count_entry*) realloc(*arr, new_cap * sizeof(**arr));
        if (!na) return NULL;
        *arr = na; *cap = new_cap;
    }
    bucket_count_entry* e = &((*arr)[(*used)++]);
    e->key = key; e->count = 0;
    return e;
}

static void guac_prune_screenshots(const char* dir, guac_timestamp now_ms) {

    if (!dir || !*dir) return;

    DIR* d = opendir(dir);
    if (!d) return;

    guac_screenshot_file* files = NULL;
    size_t files_cap = 0, files_len = 0;

    struct dirent* ent;
    while ((ent = readdir(d)) != NULL) {
        const char* name = ent->d_name;
        if (!name) continue;
        if (strncmp(name, "frame-", 6) != 0) continue;
        size_t len = strlen(name);
        if (len < 10 || strcmp(name + len - 4, ".png") != 0) continue;

        // Parse pattern: frame-<ts>-<frame>.png
        unsigned long long ts_val = 0ULL;
        unsigned frame_seq = 0U;
        if (sscanf(name, "frame-%llu-%u.png", &ts_val, &frame_seq) != 2)
            continue;

        // Append to list
        if (files_len == files_cap) {
            size_t new_cap = files_cap ? files_cap * 2 : 128;
            guac_screenshot_file* new_arr = (guac_screenshot_file*) realloc(files, new_cap * sizeof(*files));
            if (!new_arr) break;
            files = new_arr;
            files_cap = new_cap;
        }
        guac_screenshot_file* f = &files[files_len++];
        int n = snprintf(f->path, sizeof(f->path), "%s/%s", dir, name);
        if (n <= 0 || (size_t)n >= sizeof(f->path)) { files_len--; continue; }
        f->ts_ms = (uint64_t) ts_val;
        f->frame_seq = frame_seq;
    }
    closedir(d);

    if (!files || files_len == 0) { free(files); return; }

    qsort(files, files_len, sizeof(*files), compare_sshot_desc);

    // Bucket maps for tiers
    bucket_count_entry* sec_buckets = NULL; int sec_used = 0, sec_cap = 0; // up to 20 per second
    bucket_count_entry* min_buckets = NULL; int min_used = 0, min_cap = 0; // 1 per minute
    bucket_count_entry* min5_buckets = NULL; int min5_used = 0, min5_cap = 0; // 1 per 5 minutes
    bucket_count_entry* hour_buckets = NULL; int hour_used = 0, hour_cap = 0; // 1 per hour

    const uint64_t MS_1S = 1000ULL;
    const uint64_t MS_1M = 60ULL * MS_1S;
    const uint64_t MS_1H = 60ULL * MS_1M;
    const uint64_t MS_24H = 24ULL * MS_1H;
    const uint64_t MS_30D = 30ULL * 24ULL * MS_1H;

    // Track deletions lazily
    for (size_t i = 0; i < files_len; i++) {
        guac_screenshot_file* f = &files[i];
        uint64_t age = (now_ms > f->ts_ms) ? (now_ms - f->ts_ms) : 0ULL;

        if (age > MS_30D) {
            unlink(f->path);
            continue;
        }

        if (age > MS_24H) {
            uint64_t key = f->ts_ms / MS_1H; // hourly
            bucket_count_entry* e = upsert_bucket(&hour_buckets, &hour_used, &hour_cap, key);
            if (!e) continue; // out of mem: abort pruning softly
            if (e->count >= 1) { unlink(f->path); }
            else { e->count++; }
            continue;
        }

        if (age > MS_1H) {
            uint64_t key = f->ts_ms / (5ULL * MS_1M); // 5-min buckets
            bucket_count_entry* e = upsert_bucket(&min5_buckets, &min5_used, &min5_cap, key);
            if (!e) continue;
            if (e->count >= 1) { unlink(f->path); }
            else { e->count++; }
            continue;
        }

        if (age > MS_1M) {
            uint64_t key = f->ts_ms / MS_1M; // per-minute
            bucket_count_entry* e = upsert_bucket(&min_buckets, &min_used, &min_cap, key);
            if (!e) continue;
            if (e->count >= 1) { unlink(f->path); }
            else { e->count++; }
            continue;
        }

        // <= 60s: keep up to 20 per second
        uint64_t key = f->ts_ms / MS_1S; // per-second
        bucket_count_entry* e = upsert_bucket(&sec_buckets, &sec_used, &sec_cap, key);
        if (!e) continue;
        if (e->count >= 20) { unlink(f->path); }
        else { e->count++; }
    }

    free(files);
    free(sec_buckets);
    free(min_buckets);
    free(min5_buckets);
    free(hour_buckets);
}

/**
 * Returns a new Cairo surface representing the contents of the given dirty
 * rectangle from the given layer. The returned surface must eventually be
 * freed with a call to cairo_surface_destroy(). The graphical contents will be
 * referenced from the layer's last_frame buffer. If sending the contents of a
 * pending frame, that pending frame must have been copied over to the
 * last_frame buffer before calling this function.
 *
 * @param display_layer
 *     The layer whose data should be referenced by the returned Cairo surface.
 *
 * @param dirty
 *     The region of the layer that should be referenced by the returned Cairo
 *     surface.
 *
 * @return
 *     A new Cairo surface that points to the given rectangle of image data
 *     from the last_frame buffer of the given layer. This surface must
 *     eventually be freed with a call to cairo_surface_destroy().
 */
static cairo_surface_t* LFR_guac_display_layer_cairo_rect(guac_display_layer* display_layer,
        guac_rect* dirty) {

    /* Get Cairo surface covering dirty rect */
    unsigned char* buffer = GUAC_DISPLAY_LAYER_STATE_MUTABLE_BUFFER(display_layer->last_frame, *dirty);
    cairo_surface_t* rect;

    /* Use RGB24 if the image is fully opaque */
    if (display_layer->opaque)
        rect = cairo_image_surface_create_for_data(buffer,
                CAIRO_FORMAT_RGB24, guac_rect_width(dirty),
                guac_rect_height(dirty), display_layer->last_frame.buffer_stride);

    /* Otherwise ARGB32 is needed, and the destination must be cleared */
    else
        rect = cairo_image_surface_create_for_data(buffer,
                CAIRO_FORMAT_ARGB32, guac_rect_width(dirty),
                guac_rect_height(dirty), display_layer->last_frame.buffer_stride);

    return rect;

}

/**
 * Sends instructions over the Guacamole connection to clear the given
 * rectangle of the given layer if that layer is non-opaque. This is necessary
 * prior to sending image data to layers with alpha transparency, as image data
 * from multiple updates will otherwise be composited together.
 *
 * @param display_layer
 *     The layer that should possibly be cleared in preparation for a future
 *     drawing operation.
 *
 * @param dirty
 *     The rectangular region of the drawing operation.
 */
static void guac_display_layer_clear_non_opaque(guac_display_layer* display_layer,
        guac_rect* dirty) {

    guac_display* display = display_layer->display;
    const guac_layer* layer = display_layer->layer;

    guac_client* client = display->client;
    guac_socket* socket = client->socket;

    /* Clear destination region only if necessary due to the relevant layer
     * being non-opaque */
    if (!display_layer->opaque) {

        guac_protocol_send_rect(socket, layer, dirty->left, dirty->top,
                guac_rect_width(dirty), guac_rect_height(dirty));

        guac_protocol_send_cfill(socket, GUAC_COMP_ROUT, layer,
                0x00, 0x00, 0x00, 0xFF);

    }

}

/**
 * Returns an appropriate quality between 0 and 100 for lossy encoding
 * depending on the current processing lag calculated for the given client.
 *
 * @param client
 *     The client for which the lossy quality is being calculated.
 *
 * @return
 *     A value between 0 and 100 inclusive which seems appropriate for the
 *     client based on lag measurements.
 */
static int guac_display_suggest_quality(guac_client* client) {

    int lag = guac_client_get_processing_lag(client);

    /* Scale quality linearly from 90 to 30 as lag varies from 20ms to 80ms */
    int quality = 90 - (lag - 20);

    /* Do not exceed 90 for quality */
    if (quality > 90)
        return 90;

    /* Do not go below 30 for quality */
    if (quality < 30)
        return 30;

    return quality;

}

/**
 * Guesses whether a rectangle within a particular layer would be better
 * compressed as PNG or using a lossy format like JPEG. Positive values
 * indicate PNG is likely to be superior, while negative values indicate the
 * opposite.
 *
 * @param layer
 *     The layer containing the image data to check.
 *
 * @param rect
 *     The rect to check within the given layer.
 *
 * @return
 *     Positive values if PNG compression is likely to perform better than
 *     lossy alternatives, or negative values if PNG is likely to perform
 *     worse.
 */
static int LFR_guac_display_layer_png_optimality(guac_display_layer* layer,
        const guac_rect* rect) {

    int x, y;

    int num_same = 0;
    int num_different = 1;

    /* Get buffer from layer */
    size_t stride = layer->last_frame.buffer_stride;
    const unsigned char* buffer = GUAC_DISPLAY_LAYER_STATE_CONST_BUFFER(layer->last_frame, *rect);

    /* Image must be at least 1x1 */
    if (rect->right - rect->left < 1 || rect->bottom - rect->top< 1)
        return 0;

    /* For each row */
    for (y = rect->top; y < rect->bottom; y++) {

        uint32_t* row = (uint32_t*) buffer;
        uint32_t last_pixel = *(row++) | 0xFF000000;

        /* For each pixel in current row */
        for (x = rect->left + 1; x < rect->right; x++) {

            /* Get next pixel */
            uint32_t current_pixel = *(row++) | 0xFF000000;

            /* Update same/different counts according to pixel value */
            if (current_pixel == last_pixel)
                num_same++;
            else
                num_different++;

            last_pixel = current_pixel;

        }

        /* Advance to next row */
        buffer += stride;

    }

    /* Return rough approximation of optimality for PNG compression. As PNG
     * leverages lossless DEFLATE compression (which works by reducing the
     * number of bytes required to represent repeated data), an approximation
     * of the amount of repeated image data within the image is a reasonable
     * approximation for how well an image will compress. */
    return 0x100 * num_same / num_different - 0x400;

}

/**
 * Returns whether the given rectangle would be optimally encoded as JPEG
 * rather than PNG.
 *
 * @param layer
 *     The layer to be queried.
 *
 * @param rect
 *     The rectangle to check.
 *
 * @param framerate
 *     The rate that the region covered by the given rectangle has historically
 *     been being updated within the given layer, in frames per second.
 *
 * @return
 *     Non-zero if the rectangle would be optimally encoded as JPEG, zero
 *     otherwise.
 */
static int LFR_guac_display_layer_should_use_jpeg(guac_display_layer* layer,
        const guac_rect* rect, int framerate) {

    /* Do not use JPEG if lossless quality is required */
    if (layer->last_frame.lossless)
        return 0;

    int rect_width = rect->right - rect->left;
    int rect_height = rect->bottom - rect->top;
    int rect_size = rect_width * rect_height;

    /* JPEG is preferred if:
     * - frame rate is high enough
     * - image size is large enough
     * - PNG is not more optimal based on image contents */
    return framerate >= GUAC_DISPLAY_JPEG_FRAMERATE
        && rect_size > GUAC_DISPLAY_JPEG_MIN_BITMAP_SIZE
        && LFR_guac_display_layer_png_optimality(layer, rect) < 0;

}

/**
 * Returns whether the given rectangle would be optimally encoded as WebP
 * rather than PNG.
 *
 * @param layer
 *     The layer to be queried.
 *
 * @param rect
 *     The rectangle to check.
 *
 * @param framerate
 *     The rate that the region covered by the given rectangle has historically
 *     been being updated within the given layer, in frames per second.
 *
 * @return
 *     Non-zero if the rectangle would be optimally encoded as WebP, zero
 *     otherwise.
 */
static int LFR_guac_display_layer_should_use_webp(guac_display_layer* layer,
        const guac_rect* rect, int framerate) {

    /* Do not use WebP if not supported */
    if (!guac_client_supports_webp(layer->display->client))
        return 0;

    /* WebP is preferred if:
     * - frame rate is high enough
     * - PNG is not more optimal based on image contents */
    return framerate >= GUAC_DISPLAY_JPEG_FRAMERATE
        && LFR_guac_display_layer_png_optimality(layer, rect) < 0;

}

void* guac_display_worker_thread(void* data) {

    int framerate;
    int has_outstanding_frames = 0;

    guac_display* display = (guac_display*) data;
    guac_client* client = display->client;
    guac_socket* socket = client->socket;

    guac_display_plan_operation op;
    while (guac_fifo_dequeue_and_lock(&display->ops, &op)) {

        /* Notify any watchers of render_state that a frame is now in progress */
        guac_flag_set_and_lock(&display->render_state, GUAC_DISPLAY_RENDER_STATE_FRAME_IN_PROGRESS);
        guac_flag_clear(&display->render_state, GUAC_DISPLAY_RENDER_STATE_FRAME_NOT_IN_PROGRESS);
        guac_flag_unlock(&display->render_state);

        /* NOTE: Any thread that locks the operation queue can know that there
         * are no pending operations in progress if the queue is empty and
         * there are no active workers */
        display->active_workers++;
        guac_fifo_unlock(&display->ops);

        guac_rwlock_acquire_read_lock(&display->last_frame.lock);
        guac_display_layer* display_layer = op.layer;
        switch (op.type) {

            case GUAC_DISPLAY_PLAN_OPERATION_IMG:

                framerate = INT_MAX;
                if (op.current_frame > op.last_frame)
                    framerate = 1000 / (op.current_frame - op.last_frame);

                guac_rect* dirty = &op.dest;

                /* TODO: Determine whether to use PNG/WebP/JPEG purely
                 * based on whether lossless encoding is required, the
                 * expected time until another frame is received (time
                 * since last frame), and estimated encoding times. The
                 * time allowed per update should be divided up
                 * proportionately based on the dirty_size of the update. */

                /* TODO: Stream PNG/WebP/JPEG using progressive encoding such
                 * that a frame that is currently being encoded can be
                 * preempted by the next frame, with the connected client then
                 * simply receiving a lower-quality intermediate frame. If
                 * necessary, progressive encoding can be achieved by manually
                 * dividing images into multiple reduced-resolution stages,
                 * such that each image streamed is actually only one quarter
                 * the size of the original image. Compositing via Guacamole
                 * protocol instructions can reassemble those stages. */

                cairo_surface_t* rect = LFR_guac_display_layer_cairo_rect(display_layer, dirty);
                const guac_layer* layer = display_layer->layer;

                /* Clear relevant rect of destination layer if necessary to
                 * ensure fresh data is not drawn on top of old data for layers
                 * with alpha transparency */
                guac_display_layer_clear_non_opaque(display_layer, dirty);

                /* Prefer WebP when reasonable */
                if (LFR_guac_display_layer_should_use_webp(display_layer, dirty, framerate))
                    guac_client_stream_webp(client, socket, GUAC_COMP_OVER, layer,
                            dirty->left, dirty->top, rect,
                            guac_display_suggest_quality(client),
                            display_layer->last_frame.lossless ? 1 : 0);

                /* If not WebP, JPEG is the next best (lossy) choice */
                else if (display_layer->opaque && LFR_guac_display_layer_should_use_jpeg(display_layer, dirty, framerate))
                    guac_client_stream_jpeg(client, socket, GUAC_COMP_OVER, layer,
                            dirty->left, dirty->top, rect,
                            guac_display_suggest_quality(client));

                /* Use PNG if no lossy formats are appropriate */
                else
                    guac_client_stream_png(client, socket, GUAC_COMP_OVER,
                            layer, dirty->left, dirty->top, rect);

                cairo_surface_destroy(rect);
                break;

            case GUAC_DISPLAY_PLAN_OPERATION_COPY:
            case GUAC_DISPLAY_PLAN_OPERATION_RECT:
                guac_client_log(client, GUAC_LOG_DEBUG, "Operation type %i "
                        "should NOT be present in the set of operations given "
                        "to guac_display worker thread. All operations except "
                        "IMG and NOP are handled during the initial, "
                        "single-threaded flush step. This is likely a bug.",
                        op.type);
                break;

            case GUAC_DISPLAY_PLAN_OPERATION_NOP:
                /* Do nothing */
                break;

        }

        guac_fifo_lock(&display->ops);

        /* If we're the only active worker and there are no further operations
         * pending, we've reached the end of the frame, and this is the worker
         * that will be sending that boundary to connected users */
        if (!(display->ops.state.value & GUAC_FIFO_STATE_NONEMPTY) && display->active_workers == 1) {

            /* Update the mouse cursor if it's been changed since the
             * last frame */
            guac_display_layer* cursor = display->cursor_buffer;
            if (!guac_rect_is_empty(&cursor->last_frame.dirty)) {
                guac_protocol_send_cursor(client->socket,
                        display->last_frame.cursor_hotspot_x,
                        display->last_frame.cursor_hotspot_y,
                        cursor->layer, 0, 0,
                        cursor->last_frame.width,
                        cursor->last_frame.height);
            }

            /* Allow connected clients to move forward with rendering */
            guac_client_end_multiple_frames(client, display->last_frame.frames);

            /* While connected clients moves forward with rendering,
             * commit any changed contents to client-side backing buffer */
            guac_display_layer* current = display->last_frame.layers;
            while (current != NULL) {

                /* Save a copy of the changed region if the layer has
                 * been modified since the last frame */
                guac_rect* dirty = &current->last_frame.dirty;
                if (!guac_rect_is_empty(dirty)) {

                    int x = dirty->left;
                    int y = dirty->top;
                    int width = guac_rect_width(dirty);
                    int height = guac_rect_height(dirty);

                    /* Ensure destination region is cleared out first if the alpha channel need be considered,
                     * as GUAC_COMP_OVER is significantly faster than GUAC_COMP_SRC on the browser side */
                    if (!current->opaque) {
                        guac_protocol_send_rect(client->socket, current->last_frame_buffer, x, y, width, height);
                        guac_protocol_send_cfill(client->socket, GUAC_COMP_RATOP, current->last_frame_buffer,
                                0x00, 0x00, 0x00, 0x00);
                    }

                    guac_protocol_send_copy(client->socket,
                            current->layer, x, y, width, height,
                            GUAC_COMP_OVER, current->last_frame_buffer, x, y);

                }

                current = current->last_frame.next;

            }

            /* This is now absolutely everything for the current frame,
             * and it's safe to flush any outstanding data */
            guac_socket_flush(client->socket);

            /* If a recording is active, write a PNG snapshot into the
             * a screenshots subdirectory directory of where the recording.
             * we should prolly have a limit to the number of screenshots to keep... */
            if (client->__recording && client->__recording->screenshot_path[0] != '\0') {
                char filename[4096];
                int n = snprintf(filename, sizeof(filename), "%s/frame-%" PRIu64 "-%u.png",
                        client->__recording->screenshot_path,
                        (uint64_t) display->last_frame.timestamp,
                        display->last_frame.frames);
                if (n > 0 && (size_t)n < sizeof(filename)) {
                    if (guac_display_write_png(display, filename) == 0) {
                        // After successful write, enforce retention policy
                        guac_prune_screenshots(client->__recording->screenshot_path,
                                               guac_timestamp_current());
                    }
                }
            }

            /* Notify any watchers of render_state that a frame is no longer in progress */
            guac_flag_set_and_lock(&display->render_state, GUAC_DISPLAY_RENDER_STATE_FRAME_NOT_IN_PROGRESS);
            guac_flag_clear(&display->render_state, GUAC_DISPLAY_RENDER_STATE_FRAME_IN_PROGRESS);
            guac_flag_unlock(&display->render_state);

            has_outstanding_frames = display->frame_deferred;

        }

        display->active_workers--;
        guac_fifo_unlock(&display->ops);

        guac_rwlock_release_lock(&display->last_frame.lock);

        /* Trigger additional flush if frames were completed while we were
         * still processing the previous frame */
        if (has_outstanding_frames) {
            guac_display_end_multiple_frames(display, 0);
            has_outstanding_frames = 0;
        }

    }

    return NULL;

}
