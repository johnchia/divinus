#ifndef _RTSP_RTP_H
#define _RTSP_RTP_H

#if defined (__cplusplus)
extern "C" {
#endif

#include "../hal/tools.h"

/******************************************************************************
 *              DEFINITIONS 
 ******************************************************************************/
#define __RTP_MAXPAYLOADSIZE 1460

/******************************************************************************
 *              DATA STRUCTURES
 ******************************************************************************/
/*
 * RTP data header
 */
typedef struct {
#ifdef __RTSP_BIG_ENDIAN
    unsigned int version:2;   /* protocol version */
    unsigned int p:1;         /* padding flag */
    unsigned int x:1;         /* header extension flag */
    unsigned int cc:4;        /* CSRC count */
    unsigned int m:1;         /* marker bit */
    unsigned int pt:7;        /* payload type */
#else
    unsigned int cc:4;        /* CSRC count */
    unsigned int x:1;         /* header extension flag */
    unsigned int p:1;         /* padding flag */
    unsigned int version:2;   /* protocol version */
    unsigned int pt:7;        /* payload type */
    unsigned int m:1;         /* marker bit */
#endif
    unsigned int seq:16;      /* sequence number */
    unsigned int ts;          /* timestamp */
    unsigned int ssrc;        /* synchronization source */
    //unsigned int csrc[1];     /* optional CSRC list */
} rtp_hdr_t;

struct nal_rtp_t {
    struct {
        rtp_hdr_t header;
        unsigned char payload[__RTP_MAXPAYLOADSIZE];
    } packet;
    int    rtpsize;
    struct list_t list_entry;
};

/******************************************************************************
 *              DECLARATIONS
 ******************************************************************************/
static inline int __split_nal(unsigned char *buf, unsigned char **nalptr, size_t *p_len, size_t max_len);
static inline int __annexb_start_code(const unsigned char *buf, size_t len);

/******************************************************************************
 *              INLINE FUNCTIONS
 ******************************************************************************/
static inline int __annexb_start_code(const unsigned char *buf, size_t len)
{
    if (len >= 4 && buf[0] == 0 && buf[1] == 0 && buf[2] == 0 && buf[3] == 1)
        return 4;
    if (len >= 3 && buf[0] == 0 && buf[1] == 0 && buf[2] == 1)
        return 3;
    return 0;
}

static inline int __split_nal(unsigned char *buf, unsigned char **nalptr, size_t *p_len, size_t max_len)
{
    size_t search = (size_t)(*nalptr - buf) + *p_len;
    size_t start_code = max_len;
    int start_code_len = 0;

    for (size_t i = search; i + 3 <= max_len; i++) {
        int len = __annexb_start_code(buf + i, max_len - i);
        if (len) {
            start_code = i;
            start_code_len = len;
            break;
        }
    }

    if (!start_code_len)
        return FAILURE;

    size_t start = start_code + start_code_len;
    size_t end = max_len;
    for (size_t i = start; i + 3 <= max_len; i++) {
        if (__annexb_start_code(buf + i, max_len - i)) {
            end = i;
            while (end > start && buf[end - 1] == 0)
                end--;
            break;
        }
    }

    if (end <= start)
        return FAILURE;

    *nalptr = buf + start;
    *p_len = end - start;
    return SUCCESS;
}

#if defined (__cplusplus)
}
#endif

#endif
