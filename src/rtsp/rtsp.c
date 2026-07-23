/*
 * RTSP/RTP server for Divinus, built on Compy (gtxaspec/compy) for RTSP
 * protocol handling and libevent-openipc for the event loop.
 *
 * Replaces the previous hand-rolled `rtsp/*` module (rtsp.c/rtp.c/mime.c +
 * bufpool/list/hash/thread/rfc helpers). The public API in rtsp_server.h is
 * unchanged so main.c and media.c require no changes.
 *
 * Architecture:
 *  - rtsp_create() spins one thread running a libevent event_base. Accepted
 *    connections become `Client` objects implementing Compy_Controller.
 *  - Encoder threads (media.c: save_video_stream/aenc_thread) call
 *    rtp_send_h26x()/rtp_send_mp3() directly, off the event-loop thread.
 *    Every bufferevent is created with BEV_OPT_THREADSAFE and the event_base
 *    is made lock-aware via evthread_use_pthreads(), so writing into a
 *    client's transport from an encoder thread while the event-loop thread
 *    concurrently parses that same client's incoming requests is safe.
 *  - `h->clients[]` is a fixed-size table of live connections guarded by
 *    `h->mutex`. Because encoder threads can be mid-send against a Client
 *    while the event-loop thread wants to tear it down (peer disconnect,
 *    TEARDOWN), Client uses a refcount: the table itself holds one
 *    reference, each in-flight send holds another, and the struct is only
 *    freed once both the table reference is dropped and the refcount hits
 *    zero. This is a deliberately small, direct replacement for the old
 *    module's bufpool-based deferred-free scheme.
 *  - RTP timestamps use Compy_RtpTimestamp_SysClockUs (wall-clock derived),
 *    not a hand-kept per-connection timestamp accumulator. Checked against
 *    the firmware repo's ssc30kq substream pacing fixes (119dd8de/41db8e9e,
 *    which just move the pinned Divinus commit through ffab5fb/ba9d94a/
 *    c69b558): ffab5fb (VPE->VENC bind uses the real sensor rate instead of
 *    the reduced output rate on both sides) and ba9d94a (lower substream
 *    bitrate default) are HAL/config fixes below this file, already in this
 *    branch's ancestry and untouched by the rewrite. c69b558 (3-byte
 *    Annex-B start code support) was RTSP-layer, but its behavior is
 *    subsumed here: compy_determine_start_code() (used throughout this
 *    file) natively tests both the 3- and 4-byte start codes (see compy's
 *    src/nal.c), so there is nothing left to re-derive at the code level.
 *    Wall-clock timestamps are an intentional, arguably more correct choice
 *    now that ffab5fb fixed the actual source of the frame-delivery
 *    unevenness -- what remains is hardware validation (step 4), not a code
 *    gap.
 *  - SPS/PPS/VPS extraction for sprop-parameter-sets and Basic auth are
 *    reimplemented directly (not part of Compy's public API surface for the
 *    former; Compy only ships Digest for the latter, and Basic is kept here
 *    to match current production client compatibility -- no concrete reason
 *    to prefer Digest has come up, so this stays Basic).
 */

#include "rtsp_server.h"

#include "compy_libevent.h"

#include <compy.h>

#include <event2/buffer.h>
#include <event2/bufferevent.h>
#include <event2/event.h>
#include <event2/listener.h>
#include <event2/thread.h>
#include <event2/util.h>

#include <arpa/inet.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <sys/socket.h>

#include <errno.h>
#include <inttypes.h>
#include <pthread.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include "../app_config.h"
#include "../hal/macros.h"
#include "../hal/types.h"

/******************************************************************************
 *              DEFINITIONS
 ******************************************************************************/

#define RTSP_STREAM_MAIN 0
#define RTSP_STREAM_SUB  1
#define RTSP_STREAM_COUNT 2

#define RTSP_TRACK_VIDEO 0
#define RTSP_TRACK_AUDIO 1

#define RTSP_VIDEO_PAYLOAD_TYPE 96
#define RTSP_VIDEO_CLOCK_RATE   90000
#define RTSP_AUDIO_PAYLOAD_TYPE 14 /* MPA, RFC 2250 */
#define RTSP_AUDIO_CLOCK_RATE   90000 /* MPA always uses a 90kHz clock */

#define RTSP_RTCP_INTERVAL_SEC 5

/* Compy_TcpTransport_is_full() reports full whenever the connection's
 * unflushed output exceeds this. TCP-interleaved video and audio share one
 * connection/bufferevent per client, and the event-loop thread drains that
 * buffer to the kernel asynchronously -- with a max_buffer of 0 (Compy's own
 * example uses 0 too), *any* momentary backlog from a video send (e.g. an
 * I-frame's worth of NAL fragments still draining) makes the very next
 * packet on that connection -- audio included -- get silently skipped, even
 * though the client is draining fine. A few tens of KB of slack absorbs that
 * without meaningfully adding latency, while still tripping for a client
 * that's actually stalled. */
#define RTSP_TCP_TRANSPORT_MAX_BUFFER (64 * 1024)

#define RTSP_MAX_SDP_SIZE 2048

/* RTSP_LOG_ERROR() bakes in `return EXIT_FAILURE;`, which only type-checks in
 * functions returning int -- several call sites here return rtsp_handle or
 * void*, so log the same way HAL_ERROR does without its forced return. */
#define RTSP_LOG_ERROR(mod, x, ...) \
    do { \
        fprintf(stderr, "\033[0m[%s] \033[31m", (mod)); \
        fprintf(stderr, (x), ##__VA_ARGS__); \
        fprintf(stderr, "\033[0m"); \
    } while (0)

/******************************************************************************
 *              BASE64 (for sprop-parameter-sets)
 ******************************************************************************/

static size_t rtsp_base64_encode(const uint8_t *src, size_t len, char *out, size_t out_size) {
    static const char charmap[64] =
        "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    size_t i = 0, o = 0;

    while (i + 3 <= len) {
        if (o + 4 >= out_size) break;
        out[o++] = charmap[(src[i] >> 2) & 0x3F];
        out[o++] = charmap[((src[i] & 0x03) << 4) | ((src[i + 1] & 0xF0) >> 4)];
        out[o++] = charmap[((src[i + 1] & 0x0F) << 2) | ((src[i + 2] & 0xC0) >> 6)];
        out[o++] = charmap[src[i + 2] & 0x3F];
        i += 3;
    }

    if (len - i == 1 && o + 4 < out_size) {
        out[o++] = charmap[(src[i] >> 2) & 0x3F];
        out[o++] = charmap[(src[i] & 0x03) << 4];
        out[o++] = '=';
        out[o++] = '=';
    } else if (len - i == 2 && o + 4 < out_size) {
        out[o++] = charmap[(src[i] >> 2) & 0x3F];
        out[o++] = charmap[((src[i] & 0x03) << 4) | ((src[i + 1] & 0xF0) >> 4)];
        out[o++] = charmap[(src[i + 1] & 0x0F) << 2];
        out[o++] = '=';
    }

    out[o] = '\0';
    return o;
}

static void hex_encode(const uint8_t *src, size_t len, char *out) {
    static const char charmap[16] = "0123456789ABCDEF";
    for (size_t i = 0; i < len; i++) {
        out[i * 2] = charmap[(src[i] & 0xF0) >> 4];
        out[i * 2 + 1] = charmap[src[i] & 0x0F];
    }
    out[len * 2] = '\0';
}

/******************************************************************************
 *              PER-STREAM (MAIN/SUB) SDP STATE
 ******************************************************************************/

struct stream_state_t {
    pthread_mutex_t lock;
    bool isH265;
    bool have_vps, have_sps, have_pps;
    char vps_b64[256];
    char sps_b64[256];
    char pps_b64[64];
    char profile_level_id[8];
};

/******************************************************************************
 *              PER-CONNECTION (CLIENT) STATE
 ******************************************************************************/

typedef struct {
    Compy_RtpTransport *rtp;
    Compy_NalTransport *nal; /* video only; NULL for audio */
    Compy_Rtcp *rtcp;
    struct event *rtcp_ev;
    uint64_t session_id;
    bool set_up;
    bool playing;
} Track;

typedef struct Client {
    struct event_base *base;
    struct bufferevent *bev;
    void *libevent_ctx;

    struct sockaddr_in addr;

    int stream_id; /* RTSP_STREAM_MAIN or RTSP_STREAM_SUB, chosen from the
                     * request URI ("/sub" => substream), like the previous
                     * module. -1 until the first request arrives. */

    pthread_mutex_t lock; /* guards the two Track slots + refcount below */
    Track tracks[2]; /* indexed by RTSP_TRACK_VIDEO / RTSP_TRACK_AUDIO */

    int refcount;   /* table reference (1) + one per in-flight sender */
    bool closing;

    rtsp_handle server;
} Client;

declImpl(Compy_Controller, Client);

/******************************************************************************
 *              RTSP SERVER HANDLE
 ******************************************************************************/

struct __rtsp_obj_t {
    pthread_t thread;
    pthread_mutex_t mutex;

    struct event_base *base;
    struct evconnlistener *listener;
    struct event *quit_ev;

    unsigned short port;
    unsigned char max_con;
    int priority;

    volatile int quit;
    volatile int started;

    Client *clients[RTSP_MAXIMUM_CONNECTIONS];
    int con_num;

    struct stream_state_t stream[RTSP_STREAM_COUNT];

    char isAuthOn;
    char user[32];
    char pass[32];

    unsigned char audioPt;
};

/******************************************************************************
 *              CLIENT LIFETIME
 ******************************************************************************/

static void client_track_teardown(Client *c, int track) {
    Track *t = &c->tracks[track];

    if (t->rtcp_ev) {
        event_del(t->rtcp_ev);
        event_free(t->rtcp_ev);
        t->rtcp_ev = NULL;
    }
    if (t->rtcp) {
        int bye_ret __attribute__((unused)) = Compy_Rtcp_send_bye(t->rtcp);
        VCALL(DYN(Compy_Rtcp, Compy_Droppable, t->rtcp), drop);
        t->rtcp = NULL;
    }
    if (t->nal) {
        VTABLE(Compy_NalTransport, Compy_Droppable).drop(t->nal);
        t->nal = NULL;
        t->rtp = NULL; /* owned by the NalTransport, already dropped */
    } else if (t->rtp) {
        VTABLE(Compy_RtpTransport, Compy_Droppable).drop(t->rtp);
        t->rtp = NULL;
    }
    t->set_up = false;
    t->playing = false;
}

/* Called with refcount already at 0 and closing == true: no other thread can
 * still be holding a pointer to `c`. */
static void client_free(Client *c) {
    pthread_mutex_lock(&c->lock);
    client_track_teardown(c, RTSP_TRACK_VIDEO);
    client_track_teardown(c, RTSP_TRACK_AUDIO);
    pthread_mutex_unlock(&c->lock);

    pthread_mutex_destroy(&c->lock);

    if (c->bev)
        bufferevent_free(c->bev);
    if (c->libevent_ctx)
        compy_libevent_ctx_free(c->libevent_ctx); /* also drops the Controller */

    free(c);
}

/* Drop one reference. Must be called without h->mutex held. */
static void client_unref(rtsp_handle h, Client *c) {
    bool should_free = false;

    pthread_mutex_lock(&h->mutex);
    c->refcount--;
    if (c->refcount <= 0 && c->closing)
        should_free = true;
    pthread_mutex_unlock(&h->mutex);

    if (should_free)
        client_free(c);
}

/* Removes `c` from the live-connections table and drops the table's own
 * reference. Safe to call from the event-loop thread only (on_event_cb,
 * TEARDOWN). */
static void client_unregister(rtsp_handle h, Client *c) {
    bool should_free = false;

    pthread_mutex_lock(&h->mutex);
    for (int i = 0; i < RTSP_MAXIMUM_CONNECTIONS; i++) {
        if (h->clients[i] == c) {
            h->clients[i] = NULL;
            h->con_num--;
            break;
        }
    }
    c->closing = true;
    c->refcount--;
    if (c->refcount <= 0)
        should_free = true;
    pthread_mutex_unlock(&h->mutex);

    if (should_free)
        client_free(c);
}

static void Client_drop(VSelf) {
    VSELF(Client);
    (void)self;
    /* Actual teardown happens in client_free(), driven by the refcount; the
     * Compy_Droppable protocol still requires an impl for the interface. */
}

impl(Compy_Droppable, Client);

/******************************************************************************
 *              AUTH (Basic, to match the previous module's behaviour)
 ******************************************************************************/

static bool client_check_auth(rtsp_handle h, Compy_Context *ctx, const Compy_Request *req) {
    if (!h->isAuthOn)
        return true;

    CharSlice99 auth_hdr;
    if (Compy_HeaderMap_find(&req->header_map, COMPY_HEADER_AUTHORIZATION, &auth_hdr)) {
        char hdr_buf[256];
        size_t n = auth_hdr.len < sizeof hdr_buf - 1 ? auth_hdr.len : sizeof hdr_buf - 1;
        memcpy(hdr_buf, auth_hdr.ptr, n);
        hdr_buf[n] = '\0';

        if (strncmp(hdr_buf, "Basic ", 6) == 0) {
            char expected[96];
            char creds[128];
            snprintf(creds, sizeof creds, "%s:%s", h->user, h->pass);

            /* Encode expected creds and compare against the base64 the
             * client sent, avoiding a base64-decode implementation. */
            rtsp_base64_encode((const uint8_t *)creds, strlen(creds), expected, sizeof expected);

            if (strcmp(hdr_buf + 6, expected) == 0)
                return true;
        }
    }

    compy_header(ctx, COMPY_HEADER_WWW_AUTHENTICATE, "Basic realm=\"Access the camera streams\"");
    compy_respond(ctx, COMPY_STATUS_UNAUTHORIZED, "Unauthorized");
    return false;
}

/******************************************************************************
 *              SPS/PPS/VPS EXTRACTION (per stream_id)
 ******************************************************************************/

static void stream_state_ingest(struct stream_state_t *state, bool isH265, const uint8_t *data, size_t len) {
    U8Slice99 slice = U8Slice99_new((uint8_t *)data, len);
    Compy_NalStartCodeTester tester = compy_determine_start_code(slice);
    if (!tester)
        return;

    pthread_mutex_lock(&state->lock);
    state->isH265 = isH265;
    pthread_mutex_unlock(&state->lock);

    while (!U8Slice99_is_empty(slice)) {
        size_t sc = tester(slice);
        if (!sc) {
            slice = U8Slice99_advance(slice, 1);
            continue;
        }
        slice = U8Slice99_advance(slice, sc);

        /* Find the end of this NAL (start of the next start code, or EOF). */
        U8Slice99 rest = slice;
        size_t nal_len = 0;
        while (!U8Slice99_is_empty(rest)) {
            size_t inner_sc = tester(rest);
            if (inner_sc)
                break;
            rest = U8Slice99_advance(rest, 1);
            nal_len++;
        }
        if (nal_len < 2) {
            slice = rest;
            continue;
        }

        uint8_t unit_type = isH265 ? ((slice.ptr[0] >> 1) & 0x3F) : (slice.ptr[0] & 0x1F);
        bool is_vps = isH265 && unit_type == COMPY_H265_NAL_UNIT_VPS_NUT;
        bool is_sps = isH265 ? unit_type == COMPY_H265_NAL_UNIT_SPS_NUT
                              : unit_type == COMPY_H264_NAL_UNIT_SPS;
        bool is_pps = isH265 ? unit_type == COMPY_H265_NAL_UNIT_PPS_NUT
                              : unit_type == COMPY_H264_NAL_UNIT_PPS;

        pthread_mutex_lock(&state->lock);
        if (is_vps && !state->have_vps) {
            rtsp_base64_encode(slice.ptr, nal_len, state->vps_b64, sizeof state->vps_b64);
            state->have_vps = true;
        } else if (is_sps && !state->have_sps) {
            rtsp_base64_encode(slice.ptr, nal_len, state->sps_b64, sizeof state->sps_b64);
            /* profile-level-id: 3 bytes following the NAL header(s). */
            size_t header_size = isH265 ? 2 : 1;
            if (nal_len >= header_size + 3)
                hex_encode(slice.ptr + header_size, 3, state->profile_level_id);
            state->have_sps = true;
        } else if (is_pps && !state->have_pps) {
            rtsp_base64_encode(slice.ptr, nal_len, state->pps_b64, sizeof state->pps_b64);
            state->have_pps = true;
        }
        pthread_mutex_unlock(&state->lock);

        slice = rest;
    }
}

/******************************************************************************
 *              CONTROLLER: OPTIONS / DESCRIBE
 ******************************************************************************/

static void Client_options(VSelf, Compy_Context *ctx, const Compy_Request *req) {
    VSELF(Client);
    (void)self;
    (void)req;
    compy_header(ctx, COMPY_HEADER_PUBLIC, "OPTIONS, DESCRIBE, SETUP, PLAY, PAUSE, TEARDOWN, GET_PARAMETER");
    compy_respond_ok(ctx);
}

static void Client_describe(VSelf, Compy_Context *ctx, const Compy_Request *req) {
    VSELF(Client);
    (void)req;

    rtsp_handle h = self->server;
    struct stream_state_t *state = &h->stream[self->stream_id];

    char sdp_buf[RTSP_MAX_SDP_SIZE] = {0};
    Compy_Writer sdp = compy_string_writer(sdp_buf);
    ssize_t ret = 0;

    const char *ip_any = "0.0.0.0";

    // clang-format off
    COMPY_SDP_DESCRIBE(
        ret, sdp,
        (COMPY_SDP_VERSION, "0"),
        (COMPY_SDP_ORIGIN, "- 0 0 IN IP4 %s", ip_any),
        (COMPY_SDP_SESSION_NAME, "Divinus"),
        (COMPY_SDP_CONNECTION, "IN IP4 %s", ip_any),
        (COMPY_SDP_TIME, "0 0"),
        (COMPY_SDP_ATTR, "range:npt=0-"));
    // clang-format on

    pthread_mutex_lock(&state->lock);
    bool isH265 = state->isH265;
    bool have_video_sprop = state->have_sps && state->have_pps && (!isH265 || state->have_vps);
    char sps_b64[256], pps_b64[64], vps_b64[256], profile_level_id[8];
    strncpy(sps_b64, state->sps_b64, sizeof sps_b64);
    strncpy(pps_b64, state->pps_b64, sizeof pps_b64);
    strncpy(vps_b64, state->vps_b64, sizeof vps_b64);
    strncpy(profile_level_id, state->profile_level_id, sizeof profile_level_id);
    pthread_mutex_unlock(&state->lock);

    // clang-format off
    COMPY_SDP_DESCRIBE(
        ret, sdp,
        (COMPY_SDP_MEDIA, "video 0 RTP/AVP %d", RTSP_VIDEO_PAYLOAD_TYPE),
        (COMPY_SDP_ATTR, "control:track=0"),
        (COMPY_SDP_ATTR, "rtpmap:%d %s/%d", RTSP_VIDEO_PAYLOAD_TYPE, isH265 ? "H265" : "H264", RTSP_VIDEO_CLOCK_RATE));
    // clang-format on

    if (have_video_sprop) {
        if (isH265)
            ret += compy_sdp_printf(sdp, COMPY_SDP_ATTR,
                "fmtp:%d sprop-vps=%s;sprop-sps=%s;sprop-pps=%s",
                RTSP_VIDEO_PAYLOAD_TYPE, vps_b64, sps_b64, pps_b64);
        else
            ret += compy_sdp_printf(sdp, COMPY_SDP_ATTR,
                "fmtp:%d packetization-mode=1;profile-level-id=%s;sprop-parameter-sets=%s,%s",
                RTSP_VIDEO_PAYLOAD_TYPE, profile_level_id, sps_b64, pps_b64);
    } else {
        ret += compy_sdp_printf(sdp, COMPY_SDP_ATTR, "fmtp:%d packetization-mode=1", RTSP_VIDEO_PAYLOAD_TYPE);
    }

    if (h->audioPt != 255) {
        // clang-format off
        COMPY_SDP_DESCRIBE(
            ret, sdp,
            (COMPY_SDP_MEDIA, "audio 0 RTP/AVP %d", RTSP_AUDIO_PAYLOAD_TYPE),
            (COMPY_SDP_ATTR, "control:track=1"),
            (COMPY_SDP_ATTR, "rtpmap:%d MPA/%d", RTSP_AUDIO_PAYLOAD_TYPE, RTSP_AUDIO_CLOCK_RATE));
        // clang-format on
    }

    if (ret <= 0) {
        compy_respond_internal_error(ctx);
        return;
    }

    compy_header(ctx, COMPY_HEADER_CONTENT_TYPE, "application/sdp");
    compy_body(ctx, CharSlice99_from_str(sdp_buf));
    compy_respond_ok(ctx);
}

/******************************************************************************
 *              CONTROLLER: SETUP
 ******************************************************************************/

static int setup_tcp_transport(Compy_Context *ctx, const Compy_Request *req, Compy_Transport *t, Compy_Transport *rtcp_t, Compy_TransportConfig config) {
    (void)req;
    ifLet(config.interleaved, Compy_ChannelPair_Some, interleaved) {
        *t = compy_transport_tcp(Compy_Context_get_writer(ctx), interleaved->rtp_channel,
            RTSP_TCP_TRANSPORT_MAX_BUFFER);
        *rtcp_t = compy_transport_tcp(Compy_Context_get_writer(ctx), interleaved->rtcp_channel, 0);

        compy_header(ctx, COMPY_HEADER_TRANSPORT,
            "RTP/AVP/TCP;unicast;interleaved=%" PRIu8 "-%" PRIu8,
            interleaved->rtp_channel, interleaved->rtcp_channel);
        return 0;
    }

    compy_respond(ctx, COMPY_STATUS_BAD_REQUEST, "`interleaved' not found");
    return -1;
}

static int setup_udp_transport(Client *self, Compy_Context *ctx, Compy_Transport *t, Compy_Transport *rtcp_t, Compy_TransportConfig config) {
    ifLet(config.client_port, Compy_PortPair_Some, client_port) {
        int fd = compy_dgram_socket(AF_INET, &self->addr.sin_addr, client_port->rtp_port);
        if (fd == -1) {
            compy_respond_internal_error(ctx);
            return -1;
        }
        int rtcp_fd = compy_dgram_socket(AF_INET, &self->addr.sin_addr, client_port->rtcp_port);
        if (rtcp_fd == -1) {
            close(fd);
            compy_respond_internal_error(ctx);
            return -1;
        }

        uint16_t server_rtp_port = 0, server_rtcp_port = 0;
        struct sockaddr_in local = {0};
        socklen_t local_len = sizeof local;
        if (getsockname(fd, (struct sockaddr *)&local, &local_len) == 0)
            server_rtp_port = ntohs(local.sin_port);
        local_len = sizeof local;
        if (getsockname(rtcp_fd, (struct sockaddr *)&local, &local_len) == 0)
            server_rtcp_port = ntohs(local.sin_port);

        *t = compy_transport_udp(fd);
        *rtcp_t = compy_transport_udp(rtcp_fd);

        compy_header(ctx, COMPY_HEADER_TRANSPORT,
            "RTP/AVP/UDP;unicast;client_port=%" PRIu16 "-%" PRIu16 ";server_port=%" PRIu16 "-%" PRIu16,
            client_port->rtp_port, client_port->rtcp_port, server_rtp_port, server_rtcp_port);
        return 0;
    }

    compy_respond(ctx, COMPY_STATUS_BAD_REQUEST, "`client_port' not found");
    return -1;
}

static void Client_setup(VSelf, Compy_Context *ctx, const Compy_Request *req) {
    VSELF(Client);

    CharSlice99 transport_val;
    if (!Compy_HeaderMap_find(&req->header_map, COMPY_HEADER_TRANSPORT, &transport_val)) {
        compy_respond(ctx, COMPY_STATUS_BAD_REQUEST, "`Transport' not present");
        return;
    }

    Compy_TransportConfig config;
    if (compy_parse_transport(&config, transport_val) == -1) {
        compy_respond(ctx, COMPY_STATUS_BAD_REQUEST, "Malformed `Transport'");
        return;
    }

    /* URI ends in ".../track=1" for the audio track, ".../track=0" (or the
     * base URL, for aggregate control) otherwise -- matches the SDP
     * a=control lines advertised in DESCRIBE above. */
    char uri_buf[256];
    size_t uri_n = req->start_line.uri.len < sizeof uri_buf - 1 ? req->start_line.uri.len : sizeof uri_buf - 1;
    memcpy(uri_buf, req->start_line.uri.ptr, uri_n);
    uri_buf[uri_n] = '\0';
    int track = strstr(uri_buf, "track=1") ? RTSP_TRACK_AUDIO : RTSP_TRACK_VIDEO;

    Compy_Transport transport, rtcp_transport;
    int rc;
    switch (config.lower) {
    case Compy_LowerTransport_TCP:
        rc = setup_tcp_transport(ctx, req, &transport, &rtcp_transport, config);
        break;
    case Compy_LowerTransport_UDP:
        rc = setup_udp_transport(self, ctx, &transport, &rtcp_transport, config);
        break;
    default:
        rc = -1;
        break;
    }
    if (rc == -1)
        return;

    uint64_t session_id;
    bool has_session = Compy_HeaderMap_contains_key(&req->header_map, COMPY_HEADER_SESSION);
    if (has_session) {
        if (compy_scanf_header(&req->header_map, COMPY_HEADER_SESSION, "%" SCNu64, &session_id) != 1) {
            VCALL_SUPER(rtcp_transport, Compy_Droppable, drop);
            VCALL_SUPER(transport, Compy_Droppable, drop);
            compy_respond(ctx, COMPY_STATUS_BAD_REQUEST, "Malformed `Session'");
            return;
        }
    } else {
        FILE *f = fopen("/dev/urandom", "r");
        if (f) {
            if (fread(&session_id, sizeof session_id, 1, f) != 1)
                session_id = (uint64_t)random() << 32 | (uint64_t)random();
            fclose(f);
        } else {
            session_id = (uint64_t)random() << 32 | (uint64_t)random();
        }
    }

    pthread_mutex_lock(&self->lock);
    Track *t = &self->tracks[track];
    if (t->set_up)
        client_track_teardown(self, track);

    if (track == RTSP_TRACK_VIDEO) {
        t->rtp = Compy_RtpTransport_new(transport, RTSP_VIDEO_PAYLOAD_TYPE, RTSP_VIDEO_CLOCK_RATE);
        t->nal = Compy_NalTransport_new(t->rtp);
    } else {
        t->rtp = Compy_RtpTransport_new(transport, RTSP_AUDIO_PAYLOAD_TYPE, RTSP_AUDIO_CLOCK_RATE);
        t->nal = NULL;
    }
    t->rtcp = Compy_Rtcp_new(t->rtp, rtcp_transport, "divinus@camera");
    t->session_id = session_id;
    t->set_up = true;
    t->playing = false;
    pthread_mutex_unlock(&self->lock);

    compy_header(ctx, COMPY_HEADER_SESSION, "%" PRIu64, session_id);
    compy_respond_ok(ctx);
}

/******************************************************************************
 *              CONTROLLER: PLAY / PAUSE / TEARDOWN / GET_PARAMETER
 ******************************************************************************/

static void send_rtcp_sr_cb(evutil_socket_t fd, short events, void *arg) {
    (void)fd;
    (void)events;
    int sr_ret __attribute__((unused)) = Compy_Rtcp_send_sr((Compy_Rtcp *)arg);
}

static void Client_play(VSelf, Compy_Context *ctx, const Compy_Request *req) {
    VSELF(Client);

    uint64_t session_id;
    if (compy_scanf_header(&req->header_map, COMPY_HEADER_SESSION, "%" SCNu64, &session_id) != 1) {
        compy_respond(ctx, COMPY_STATUS_BAD_REQUEST, "Malformed `Session'");
        return;
    }

    bool played = false;
    pthread_mutex_lock(&self->lock);
    for (int i = 0; i < 2; i++) {
        Track *t = &self->tracks[i];
        if (t->set_up && t->session_id == session_id) {
            t->playing = true;
            if (t->rtcp && !t->rtcp_ev) {
                t->rtcp_ev = event_new(self->base, -1, EV_PERSIST | EV_TIMEOUT, send_rtcp_sr_cb, t->rtcp);
                if (t->rtcp_ev)
                    event_add(t->rtcp_ev, &(const struct timeval){.tv_sec = RTSP_RTCP_INTERVAL_SEC});
            }
            played = true;
        }
    }
    pthread_mutex_unlock(&self->lock);

    if (!played) {
        compy_respond(ctx, COMPY_STATUS_SESSION_NOT_FOUND, "Invalid Session ID");
        return;
    }

    compy_header(ctx, COMPY_HEADER_RANGE, "npt=now-");
    compy_respond_ok(ctx);
}

static void Client_pause_method(VSelf, Compy_Context *ctx, const Compy_Request *req) {
    VSELF(Client);

    uint64_t session_id;
    if (compy_scanf_header(&req->header_map, COMPY_HEADER_SESSION, "%" SCNu64, &session_id) != 1) {
        compy_respond(ctx, COMPY_STATUS_BAD_REQUEST, "Malformed `Session'");
        return;
    }

    pthread_mutex_lock(&self->lock);
    for (int i = 0; i < 2; i++) {
        Track *t = &self->tracks[i];
        if (t->set_up && t->session_id == session_id)
            t->playing = false;
    }
    pthread_mutex_unlock(&self->lock);

    compy_respond_ok(ctx);
}

static void Client_teardown(VSelf, Compy_Context *ctx, const Compy_Request *req) {
    VSELF(Client);

    uint64_t session_id;
    if (compy_scanf_header(&req->header_map, COMPY_HEADER_SESSION, "%" SCNu64, &session_id) != 1) {
        compy_respond(ctx, COMPY_STATUS_BAD_REQUEST, "Malformed `Session'");
        return;
    }

    bool torn_down = false;
    pthread_mutex_lock(&self->lock);
    for (int i = 0; i < 2; i++) {
        Track *t = &self->tracks[i];
        if (t->set_up && t->session_id == session_id) {
            client_track_teardown(self, i);
            torn_down = true;
        }
    }
    pthread_mutex_unlock(&self->lock);

    if (!torn_down) {
        compy_respond(ctx, COMPY_STATUS_SESSION_NOT_FOUND, "Invalid Session ID");
        return;
    }

    compy_respond_ok(ctx);
}

static void Client_get_parameter(VSelf, Compy_Context *ctx, const Compy_Request *req) {
    VSELF(Client);
    (void)self;
    (void)req;
    compy_respond_ok(ctx);
}

static void Client_unknown(VSelf, Compy_Context *ctx, const Compy_Request *req) {
    VSELF(Client);
    (void)self;
    (void)req;
    compy_respond(ctx, COMPY_STATUS_NOT_IMPLEMENTED, "Not Implemented");
}

static Compy_ControlFlow Client_before(VSelf, Compy_Context *ctx, const Compy_Request *req) {
    VSELF(Client);

    if (self->stream_id < 0) {
        char uri_buf[256];
        size_t uri_n = req->start_line.uri.len < sizeof uri_buf - 1 ? req->start_line.uri.len : sizeof uri_buf - 1;
        memcpy(uri_buf, req->start_line.uri.ptr, uri_n);
        uri_buf[uri_n] = '\0';
        self->stream_id = strstr(uri_buf, "/sub") ? RTSP_STREAM_SUB : RTSP_STREAM_MAIN;
    }

    if (!client_check_auth(self->server, ctx, req))
        return Compy_ControlFlow_Break;

    return Compy_ControlFlow_Continue;
}

static void Client_after(VSelf, ssize_t ret, Compy_Context *ctx, const Compy_Request *req) {
    VSELF(Client);
    (void)self;
    (void)ctx;
    (void)req;
    if (ret < 0)
        HAL_WARNING("rtsp", "Failed to write RTSP response: %s\n", strerror(errno));
}

impl(Compy_Controller, Client);

/******************************************************************************
 *              LIBEVENT GLUE: ACCEPT / TEARDOWN
 ******************************************************************************/

/* bufferevent only carries one callback arg shared across read/write/event
 * callbacks; Compy's compy_libevent_cb() wants its own LibeventCtx* while
 * on_event_cb() wants the owning Client*, so the shared arg is the Client
 * and this trampoline forwards to Compy with the right pointer. */
static void client_read_cb(struct bufferevent *bev, void *arg) {
    Client *c = arg;
    compy_libevent_cb(bev, c->libevent_ctx);
}

static void on_event_cb(struct bufferevent *bev, short events, void *arg) {
    (void)bev;
    Client *c = arg;

    if (events & (BEV_EVENT_EOF | BEV_EVENT_ERROR))
        client_unregister(c->server, c);
}

static void listener_cb(struct evconnlistener *listener, evutil_socket_t fd, struct sockaddr *sa, int socklen, void *arg) {
    (void)listener;
    rtsp_handle h = arg;

    pthread_mutex_lock(&h->mutex);
    bool at_capacity = h->con_num >= h->max_con;
    pthread_mutex_unlock(&h->mutex);
    if (at_capacity) {
        HAL_WARNING("rtsp", "Rejecting connection: %d connections already active\n", h->max_con);
        close(fd);
        return;
    }

    int one = 1;
    setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);

    struct bufferevent *bev = bufferevent_socket_new(h->base, fd, BEV_OPT_CLOSE_ON_FREE | BEV_OPT_THREADSAFE);
    if (!bev) {
        close(fd);
        return;
    }

    Client *c = calloc(1, sizeof *c);
    if (!c) {
        bufferevent_free(bev);
        return;
    }
    c->base = h->base;
    c->bev = bev;
    c->server = h;
    c->stream_id = -1;
    c->refcount = 1; /* table reference */
    pthread_mutex_init(&c->lock, NULL);
    if (socklen > 0 && (size_t)socklen <= sizeof c->addr)
        memcpy(&c->addr, sa, (size_t)socklen);

    Compy_Controller controller = DYN(Client, Compy_Controller, c);
    c->libevent_ctx = compy_libevent_ctx(controller);

    bufferevent_setcb(bev, client_read_cb, NULL, on_event_cb, c);
    bufferevent_enable(bev, EV_READ | EV_WRITE);

    pthread_mutex_lock(&h->mutex);
    bool placed = false;
    for (int i = 0; i < RTSP_MAXIMUM_CONNECTIONS; i++) {
        if (!h->clients[i]) {
            h->clients[i] = c;
            h->con_num++;
            placed = true;
            break;
        }
    }
    pthread_mutex_unlock(&h->mutex);

    if (!placed) {
        /* Raced past the capacity check above; drop it. */
        bufferevent_free(bev);
        compy_libevent_ctx_free(c->libevent_ctx);
        pthread_mutex_destroy(&c->lock);
        free(c);
    }
}

static void quit_cb(evutil_socket_t fd, short events, void *arg) {
    (void)fd;
    (void)events;
    rtsp_handle h = arg;
    event_base_loopexit(h->base, NULL);
}

/******************************************************************************
 *              EVENT-LOOP THREAD
 ******************************************************************************/

static void *rtsp_thread_fn(void *arg) {
    rtsp_handle h = arg;

    evthread_use_pthreads();

    h->base = event_base_new();
    if (!h->base) {
        RTSP_LOG_ERROR("rtsp", "event_base_new failed\n");
        return NULL;
    }

    struct sockaddr_in addr = {0};
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_ANY);
    addr.sin_port = htons(h->port);

    h->listener = evconnlistener_new_bind(h->base, listener_cb, h,
        LEV_OPT_REUSEABLE | LEV_OPT_CLOSE_ON_FREE, -1, (struct sockaddr *)&addr, sizeof addr);
    if (!h->listener) {
        RTSP_LOG_ERROR("rtsp", "Failed to bind RTSP port %u\n", h->port);
        event_base_free(h->base);
        h->base = NULL;
        return NULL;
    }

    h->quit_ev = event_new(h->base, -1, 0, quit_cb, h);

    h->started = 1;
    event_base_dispatch(h->base);

    evconnlistener_free(h->listener);
    h->listener = NULL;
    event_free(h->quit_ev);
    h->quit_ev = NULL;

    /* rtsp_finish() is called before main.c stops the encoder/SDK threads
     * (see main.c), so rtp_send_h26x()/rtp_send_mp3() can still be mid-send
     * against a table entry while this teardown runs. Null out h->base
     * first so any send that checks it from here on bails out immediately
     * via its own `if (!h->base) return -1;` guard, and -- for a send that
     * already passed that check -- decide should-free atomically with the
     * refcount decrement, under h->mutex, exactly like client_unref() and
     * client_unregister() do. Deciding should-free from a read of
     * c->refcount taken *after* unlocking (as this loop used to) races a
     * concurrent client_unref() and can double-free the same Client. */
    struct event_base *base = h->base;
    h->base = NULL;

    pthread_mutex_lock(&h->mutex);
    for (int i = 0; i < RTSP_MAXIMUM_CONNECTIONS; i++) {
        Client *c = h->clients[i];
        h->clients[i] = NULL;
        bool should_free = false;
        if (c) {
            c->closing = true;
            c->refcount--;
            should_free = c->refcount <= 0;
        }
        pthread_mutex_unlock(&h->mutex);
        if (should_free)
            client_free(c);
        pthread_mutex_lock(&h->mutex);
    }
    pthread_mutex_unlock(&h->mutex);

    event_base_free(base);

    return NULL;
}

/******************************************************************************
 *              PUBLIC API (rtsp_server.h)
 ******************************************************************************/

rtsp_handle rtsp_create(unsigned char max_con, unsigned int port, int priority) {
    if (max_con > RTSP_MAXIMUM_CONNECTIONS) {
        RTSP_LOG_ERROR("rtsp", "maximum number of connections should be within %d\n", RTSP_MAXIMUM_CONNECTIONS);
        return NULL;
    }

    rtsp_handle h = calloc(1, sizeof *h);
    if (!h)
        return NULL;

    h->max_con = max_con;
    h->port = (unsigned short)port;
    h->priority = priority;
    h->audioPt = 255;
    pthread_mutex_init(&h->mutex, NULL);
    for (int s = 0; s < RTSP_STREAM_COUNT; s++)
        pthread_mutex_init(&h->stream[s].lock, NULL);

    srand((unsigned)time(NULL));

    if (pthread_create(&h->thread, NULL, rtsp_thread_fn, h) != 0) {
        pthread_mutex_destroy(&h->mutex);
        free(h);
        return NULL;
    }

    /* Wait for the listener to come up (or fail) before returning, matching
     * the previous module's synchronous rtsp_create() contract. */
    for (int waited = 0; !h->started && waited < 2000; waited++)
        usleep(1000);

    return h;
}

void rtsp_configure_auth(rtsp_handle h, const char *user, const char *pass) {
    if (!h)
        return;
    if (user && pass) {
        h->isAuthOn = 1;
        strncpy(h->user, user, sizeof(h->user) - 1);
        strncpy(h->pass, pass, sizeof(h->pass) - 1);
    } else {
        h->isAuthOn = 0;
    }
}

int rtsp_tick(rtsp_handle h) {
    /* RTP timestamps are derived from the wall clock (SysClockUs) rather
     * than accumulated here, so there is nothing left to do periodically;
     * kept as a no-op for API compatibility with main.c's call site. */
    (void)h;
    return 0;
}

void rtsp_finish(rtsp_handle h) {
    if (!h)
        return;

    if (h->quit_ev)
        event_active(h->quit_ev, 0, 0);

    pthread_join(h->thread, NULL);

    for (int s = 0; s < RTSP_STREAM_COUNT; s++)
        pthread_mutex_destroy(&h->stream[s].lock);
    pthread_mutex_destroy(&h->mutex);
    free(h);
}

void rtp_disable_audio(rtsp_handle h) {
    if (h)
        h->audioPt = 255;
}

int rtp_send_h26x(rtsp_handle h, hal_vidstream *stream, char isH265, int stream_id) {
    if (!h || stream_id < 0 || stream_id >= RTSP_STREAM_COUNT)
        return -1;
    if (!h->base) /* event loop not up yet, or already torn down */
        return -1;

    for (unsigned i = 0; i < stream->count; i++) {
        hal_vidpack *pack = &stream->pack[i];
        stream_state_ingest(&h->stream[stream_id], isH265, pack->data + pack->offset, pack->length - pack->offset);
    }

    /* Snapshot + ref matching clients under h->mutex, then send outside the
     * lock so a slow client can't stall the whole table. */
    Client *targets[RTSP_MAXIMUM_CONNECTIONS];
    int n = 0;

    pthread_mutex_lock(&h->mutex);
    for (int i = 0; i < RTSP_MAXIMUM_CONNECTIONS; i++) {
        Client *c = h->clients[i];
        if (c && !c->closing && c->stream_id == stream_id) {
            c->refcount++;
            targets[n++] = c;
        }
    }
    pthread_mutex_unlock(&h->mutex);

    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    uint64_t now_us = (uint64_t)ts.tv_sec * 1000000ULL + (uint64_t)ts.tv_nsec / 1000;
    Compy_RtpTimestamp rtp_ts = Compy_RtpTimestamp_SysClockUs(now_us);

    for (int ci = 0; ci < n; ci++) {
        Client *c = targets[ci];

        pthread_mutex_lock(&c->lock);
        Track *t = &c->tracks[RTSP_TRACK_VIDEO];
        if (t->set_up && t->playing && t->nal && !Compy_NalTransport_is_full(t->nal)) {
            for (unsigned i = 0; i < stream->count; i++) {
                hal_vidpack *pack = &stream->pack[i];
                uint8_t *data = pack->data + pack->offset;
                size_t len = pack->length - pack->offset;

                U8Slice99 slice = U8Slice99_new(data, len);
                Compy_NalStartCodeTester tester = compy_determine_start_code(slice);
                if (!tester)
                    continue;

                while (!U8Slice99_is_empty(slice)) {
                    size_t sc = tester(slice);
                    if (!sc) {
                        slice = U8Slice99_advance(slice, 1);
                        continue;
                    }
                    slice = U8Slice99_advance(slice, sc);

                    U8Slice99 rest = slice;
                    size_t nal_len = 0;
                    while (!U8Slice99_is_empty(rest) && !tester(rest)) {
                        rest = U8Slice99_advance(rest, 1);
                        nal_len++;
                    }
                    if (nal_len < 2) {
                        slice = rest;
                        continue;
                    }

                    Compy_NalUnit nalu;
                    if (isH265) {
                        nalu.header = Compy_NalHeader_H265(Compy_H265NalHeader_parse(slice.ptr));
                        nalu.payload = U8Slice99_new(slice.ptr + 2, nal_len - 2);
                    } else {
                        nalu.header = Compy_NalHeader_H264(Compy_H264NalHeader_parse(slice.ptr[0]));
                        nalu.payload = U8Slice99_new(slice.ptr + 1, nal_len - 1);
                    }

                    int send_ret __attribute__((unused)) = Compy_NalTransport_send_packet(t->nal, rtp_ts, nalu);

                    slice = rest;
                }
            }
        }
        pthread_mutex_unlock(&c->lock);

        client_unref(h, c);
    }

    return 0;
}

int rtp_send_mp3(rtsp_handle h, unsigned char *buf, size_t len) {
    if (!h)
        return -1;
    if (!h->base)
        return -1;

    h->audioPt = RTSP_AUDIO_PAYLOAD_TYPE;

    Client *targets[RTSP_MAXIMUM_CONNECTIONS];
    int n = 0;

    pthread_mutex_lock(&h->mutex);
    for (int i = 0; i < RTSP_MAXIMUM_CONNECTIONS; i++) {
        Client *c = h->clients[i];
        if (c && !c->closing) {
            c->refcount++;
            targets[n++] = c;
        }
    }
    pthread_mutex_unlock(&h->mutex);

    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    uint64_t now_us = (uint64_t)ts.tv_sec * 1000000ULL + (uint64_t)ts.tv_nsec / 1000;
    Compy_RtpTimestamp rtp_ts = Compy_RtpTimestamp_SysClockUs(now_us);

    /* RFC 2250 MPEG audio-specific header: 4 zero bytes (MBZ + fragment
     * offset), no fragmentation since one RTP packet carries one frame. */
    static const uint8_t mpa_header[4] = {0, 0, 0, 0};
    U8Slice99 header = U8Slice99_new((uint8_t *)mpa_header, sizeof mpa_header);
    U8Slice99 payload = U8Slice99_new(buf, len);

    for (int ci = 0; ci < n; ci++) {
        Client *c = targets[ci];

        pthread_mutex_lock(&c->lock);
        Track *t = &c->tracks[RTSP_TRACK_AUDIO];
        if (t->set_up && t->playing && t->rtp && !Compy_RtpTransport_is_full(t->rtp)) {
            int send_ret __attribute__((unused)) = Compy_RtpTransport_send_packet(t->rtp, rtp_ts, true, header, payload);
        }
        pthread_mutex_unlock(&c->lock);

        client_unref(h, c);
    }

    return 0;
}
