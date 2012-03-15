/* HIM.C        (c) Copyright Thomas J. Valerio, 2012                */
/*              (c) Copyright Michael T. Alexander, 2012             */
/*              ESA/390 Host Interface Machine Device Handler        */
/*                                                                   */
/*   Released under "The Q Public License Version 1"                 */
/*   (http://www.hercules-390.org/herclic.html) as modifications to  */
/*   Hercules.                                                       */

// $Id$

/*-------------------------------------------------------------------*/
/* This module contains device handling functions for emulated       */
/* System/390 Host Interface Machine devices.                        */
/*                                                                   */
/* a "Host Interface Machine" or HIM was a homegrown subchannel      */
/* addressable Internet Protocol device that allowed the Michigan    */
/* Terminal System, a.k.a. MTS to communicate with the outside world */
/* over the Internet.                                                */
/*-------------------------------------------------------------------*/

#include "hstdinc.h"
#include "hercules.h"
#include "devtype.h"

#undef  __USE_BSD
#define __USE_BSD
#undef  __FAVOR_BSD
#define __FAVOR_BSD

#include <netinet/ip.h>
#include <netinet/tcp.h>
#include <netinet/udp.h>

#include <poll.h>


/*-------------------------------------------------------------------*/
/* Internal macro definitions                                        */
/*-------------------------------------------------------------------*/
#define BUFLEN 	        (2048 - 4)
#define QLEN            5


/*-------------------------------------------------------------------*/
/* This header is at the front of every subchannel read and write    */
/* operation for non-3270 devices.  It is used to communicate        */
/* between the HIM Device Support Processor code in MTS and this     */
/* HIM device emulation.  The bits are reversed from where they      */
/* appear in memory because this is a little-endian architecture     */
/*-------------------------------------------------------------------*/
 
struct buff_hdr {
    unsigned int unused         : 3;
    unsigned int tn3270_flag    : 1;   /* Switch to TN3270 mode      */
    unsigned int init_flag      : 1;   /* Data is configuration info */
    unsigned int finished_flag  : 1;   /* Interface disconnect       */
    unsigned int rnr_flag       : 1;   /* Read-Not-Ready             */
    unsigned int urgent_flag    : 1;   /* Urgent data to be read     */
    u_char buffer_number;              /* Sequential buffer number   */
    u_short buffer_length;             /* buffer length              */
};
 
/*-------------------------------------------------------------------*/
/*  This is the full packet header for all of the subchannel read    */
/*  and write operations for non-3270 devices.  It includes the HIM  */
/*  DSP buffer header defined above, as well as the IP packet header */
/*  and the TCP or UDP packet header.                                */
/*-------------------------------------------------------------------*/
 
struct packet_hdr {
    struct buff_hdr him_hdr;
    struct ip ip_header;
    union {
        struct tcphdr tcp_header;
        struct udphdr udp_header;
    } sh;
    u_char tcp_optcode;
    u_char tcp_optlen;
    u_short tcp_optval;
};

/*-------------------------------------------------------------------*/
/* This is the format of the *reply* to the configuration command    */
/* that MTS sends out when it wants to start using a particular      */
/* subchannel. The configuration command itself is an EBCDIC string. */
/*-------------------------------------------------------------------*/
 
struct config_reply {
    struct buff_hdr him_hdr;
    unsigned char config_ok[2];        /* EBCDIC "Ok"                */
    u_char family;                     /* Protocol family            */
    u_char protocol;                   /* Actual Protocol            */
    u_short local_port;                /* Local port number          */
    u_char local_ip[4];                /* Local IP address           */
    char unused[2];
    u_short remote_port;
    u_char remote_ip[4];
};

 
/*
 *  The I/O control block
 */
 
struct io_cb {
    int sock;
    u_char protocol, buf_count;
    enum {SHUTDOWN, INITIALIZED, CONNECTED, CLOSING} state;
    unsigned int passive    : 1;     /* Passive port listener        */
    unsigned int server     : 1;     /* Accepting calls on any port  */
    unsigned int rnr        : 1;     /* Read Not Ready flag          */
    unsigned int watch_sock : 1;     /* Socket watcher thread active */
    unsigned int tn3270     : 1;     /* In use by TN3270             */
    unsigned int unused_0   : 1;
    unsigned int unused_1   : 1;
    unsigned int unused_2   : 1;
    struct sockaddr_in sin;
    struct packet_hdr mts_header;
    enum {EMPTY, CONFIG, MSS, ACK, FIN, FINISHED} read_q[16];
};


static void config_subchan ( struct io_cb *iocb_ptr, BYTE *config_data );
static int parse_config_data ( struct io_cb *iocb_ptr, char *config_string, int cs_len );
static int get_socket ( int protocol, int port, struct sockaddr_in *sin, int qlen );
static int return_mss ( struct io_cb * iocb_ptr, struct packet_hdr *mss );
static int start_sock_thread ( DEVBLK* dev );
static void* skt_thread ( DEVBLK* dev );
static void  debug_pf ( __const char *__restrict __fmt, ... );
static void  dumpdata ( char *label, BYTE *data, int len );


/*-------------------------------------------------------------------*/
/* Initialize the device handler                                     */
/*-------------------------------------------------------------------*/
static int him_init_handler (DEVBLK *dev, int argc, char *argv[])
{
int     i;                              /* Array subscript           */

    /* The first argument is the file name *
    if ( argc == 0 )
    {
        WRMSG (HHC01208, "E", SSID_TO_LCSS(dev->ssid), dev->devnum);
        return -1;
    }

    if (strlen(argv[0]) >= sizeof(dev->filename))
    {
        WRMSG (HHC01201, "E", SSID_TO_LCSS(dev->ssid), dev->devnum, argv[0], (int)sizeof(dev->filename) - 1);
        return -1;
    }

    * Save the file name in the device block *
    hostpath(dev->filename, argv[0], sizeof(dev->filename)); */

    /* Initialize device dependent fields *
    dev->fd = -1;
    dev->ascii = 0;
    dev->crlf = 0;
    dev->cardpos = 0;
    dev->cardrem = CARD_LENGTH;
    dev->notrunc = 0;
    dev->stopdev = FALSE;

    dev->excps = 0;

    if(!sscanf(dev->typname,"%hx",&(dev->devtype)))
        dev->devtype = 0x3525; */

    /* Set length of buffer */
    dev->bufsize = 2048 - 4;

    /* Set number of sense bytes */
    dev->numsense = 1;

    /* Initialize the device identifier bytes */
    dev->devid[0] = 0xFF;
    dev->devid[1] = 0x32; /* Control unit type is 3274-1d */
    dev->devid[2] = 0x74;
    dev->devid[3] = 0x1d;
    dev->devid[4] = dev->devtype >> 8;
    dev->devid[5] = dev->devtype & 0xFF;
    dev->devid[6] = 0x01;
    dev->numdevid = 7;

    dev->dev_data = malloc(sizeof(struct io_cb));
    memset ((char *) dev->dev_data, '\0', sizeof(struct io_cb));

    debug_pf("Device %s at %04X initialized, version = %s %s\n",
        dev->typname, dev->devnum, __TIME__, __DATE__);

    /* Activate I/O tracing */
//  dev->ccwtrace = 1;

    return 0;
} /* end function him_init_handler */

/*-------------------------------------------------------------------*/
/* Query the device definition                                       */
/*-------------------------------------------------------------------*/
static void him_query_device (DEVBLK *dev, char **devclass,
                int buflen, char *buffer)
{

    BEGIN_DEVICE_CLASS_QUERY( "HIM", dev, devclass, buflen, buffer );

    snprintf (buffer, buflen-1, "%s%s%s%s%s IO[%" I64_FMT "u]",
                dev->filename,
                (dev->ascii ? " ascii" : " ebcdic"),
                ((dev->ascii && dev->crlf) ? " crlf" : ""),
                (dev->notrunc ? " notrunc" : ""),
                (dev->stopdev    ? " (stopped)"    : ""),
                dev->excps );

} /* end function him_query_device */


/*-------------------------------------------------------------------*/
/* Close the device                                                  */
/*-------------------------------------------------------------------*/
static int him_close_device ( DEVBLK *dev )
{
    dev->stopdev = FALSE;

    /* Free the I/O Control Block */
    free(dev->dev_data);

    debug_pf("Device termination successful\n");

    return 0;
} /* end function him_close_device */


/*-------------------------------------------------------------------*/
/* Execute a Channel Command Word                                    */
/*-------------------------------------------------------------------*/
static void him_execute_ccw (DEVBLK *dev, BYTE code, BYTE flags,
        BYTE chained, U16 count, BYTE prevcode, int ccwseq,
        BYTE *iobuf, BYTE *more, BYTE *unitstat, U16 *residual)
{
int             rc;                     /* Return code               */
int             i;                      /* Loop counter              */
int             num;                    /* Number of bytes to move   */
int             open_flags;             /* File open flags           */
struct io_cb *  cb_ptr;                 /* I/O Control Block pointer */
int             readlen, writelen, offset, window, ack_seq, temp_sock;
struct packet_hdr *buff_ptr;
struct pollfd   read_chk;
unsigned int    sinlen = sizeof (struct sockaddr_in);
struct          timeval tv;
char            buf[64];

    UNREFERENCED(flags);
    UNREFERENCED(chained);
    UNREFERENCED(prevcode);
    UNREFERENCED(ccwseq);

    /* Copy I/O Control Block and Channel I/O buffer pointers to local variables */
    cb_ptr = (struct io_cb *) dev->dev_data;
    buff_ptr = (struct packet_hdr *) iobuf;

    /* if (code == 1 || code == 2)
    { */
        gettimeofday(&tv, NULL);
        strftime(buf, sizeof buf, "%H:%M:%S", localtime(&tv.tv_sec));
        debug_pf(" %s.%06d -- devnum %04X opcode %02X\n", buf, tv.tv_usec, dev->devnum, code);
    /* } */

    /* Process depending on CCW opcode */
    switch (code) {

    case 0x01:
    /*---------------------------------------------------------------*/
    /* WRITE - process data from channel                             */
    /*---------------------------------------------------------------*/

        *residual = 0;

        debug_pf("data from MTS       DevNum = %04X\n", dev->devnum);
        dumpdata("", iobuf, (count < 96 ? count : 96));
        if (count > 44 && cb_ptr->protocol == IPPROTO_TCP)
            debug_pf("%.*s\n", count - 44, &((char *) iobuf)[44]);

        if ( buff_ptr->him_hdr.finished_flag )
        {
            for ( i = 0; cb_ptr->read_q[i] != EMPTY; i++ ) ;
            cb_ptr->read_q[i] = FINISHED;

            *unitstat = CSW_CE | CSW_DE;

        }
        else if ( cb_ptr->state == CONNECTED && buff_ptr->him_hdr.rnr_flag )
        {
            /* FD_CLR(cb_ptr->sock, readfds); */
            debug_pf("-----  RNR Flag = ON received.\n");
            cb_ptr->watch_sock = 0;

            cb_ptr->rnr = 1;
            *unitstat = CSW_CE | CSW_DE | CSW_UX;

        }
        else if ( cb_ptr->rnr && !buff_ptr->him_hdr.rnr_flag )
        {
            /* FD_SET(cb_ptr->sock, readfds); */
            debug_pf("-----  RNR Flag = OFF received.\n");

            start_sock_thread(dev);

            cb_ptr->rnr = 0;
            *unitstat = CSW_CE | CSW_DE;

        }
        else if ( buff_ptr->him_hdr.init_flag )
        {
            config_subchan(cb_ptr, iobuf);

            /* Copy the config reply to dev->buf so it will be there when
               MTS next hangs a read on the HIM device. */
            readlen = 
                ntohs( ((struct buff_hdr *) iobuf)->buffer_length ) + sizeof(struct buff_hdr);

            for ( i = 0; cb_ptr->read_q[i] != EMPTY; i++ ) ;
            cb_ptr->read_q[i] = CONFIG;
            memcpy(dev->buf, iobuf, readlen);

            *unitstat = CSW_CE | CSW_DE | CSW_ATTN;

        }
        else if ( cb_ptr->protocol == IPPROTO_UDP )
        {
            if ( ntohs( buff_ptr->him_hdr.buffer_length ) > 4 )
            {
                cb_ptr->sin.sin_port = buff_ptr->sh.udp_header.uh_dport;
                cb_ptr->sin.sin_addr = buff_ptr->ip_header.ip_dst;
                writelen = ntohs( buff_ptr->him_hdr.buffer_length ) - 28;
 
                if (sendto(cb_ptr->sock, &((char *) buff_ptr)[32],
                    writelen, 0, &cb_ptr->sin, sizeof(struct sockaddr_in)) < 0)
                    debug_pf("sendto");

                *unitstat = CSW_CE | CSW_DE;
            }

        }
        else           /* must be a TCP packet */
        {
            /*
             *  If this is an unconnected TCP subchannel then the first packet
             *  is the signal that we should get connected.  The first packet
             *  also contains the destination address that we need to connect.
             */
 
            if (cb_ptr->state == INITIALIZED)
            {
                cb_ptr->mts_header.ip_header.ip_src = buff_ptr->ip_header.ip_dst;
                cb_ptr->sin.sin_addr = buff_ptr->ip_header.ip_dst;
                cb_ptr->mts_header.sh.tcp_header.source =
                    cb_ptr->sin.sin_port = buff_ptr->sh.tcp_header.dest;

                if (connect(cb_ptr->sock, &cb_ptr->sin, sizeof(struct sockaddr_in)) < 0) 
                    debug_pf("----- Call to connect, rc = %i\n", errno);
 
                cb_ptr->state = CONNECTED;

                /* Queue an MSS acknowledgement */
                for ( i = 0; cb_ptr->read_q[i] != EMPTY; i++ ) ;
                cb_ptr->read_q[i] = MSS;

                *unitstat = CSW_CE | CSW_DE | CSW_ATTN;

            }
            else if (ntohs( buff_ptr->him_hdr.buffer_length ) > 4)
            {
                offset = ((buff_ptr->ip_header.ip_hl +
                    buff_ptr->sh.tcp_header.doff) * 4) + 4;
 
                writelen = ntohs( buff_ptr->him_hdr.buffer_length ) - offset + 4;
                cb_ptr->mts_header.sh.tcp_header.ack_seq =
                    htonl( ntohl( cb_ptr->mts_header.sh.tcp_header.ack_seq ) + writelen );
 
                if (writelen > 0)
                {
                    if (cb_ptr->state == CONNECTED)
                    {
                        i = write(cb_ptr->sock, &((char *) buff_ptr)[offset], writelen);

                        if ( writelen == 1460 )
                            cb_ptr->watch_sock = 0;
 
                        window = ntohs( cb_ptr->mts_header.sh.tcp_header.window );
                        ack_seq = ntohl( cb_ptr->mts_header.sh.tcp_header.ack_seq );

                        if ( (window - (ack_seq % window)) < (writelen + 4096) )
                        {
                            for ( i = 0; cb_ptr->read_q[i] != EMPTY; i++ ) ;
                            cb_ptr->read_q[i] = ACK;
                        }
                    }
                }
                /* else */ if (buff_ptr->sh.tcp_header.fin)
                {
                    if ( cb_ptr->state == CONNECTED )
                    {
                        for ( i = 0; cb_ptr->read_q[i] != EMPTY; i++ ) ;
                        cb_ptr->read_q[i] = FIN;
                        /* cb_ptr->state = CLOSING; */

                        for ( i = 0; cb_ptr->read_q[i] != EMPTY; i++ ) ;
                        cb_ptr->read_q[i] = FINISHED;

                    }
                    else
                    {
                        for ( i = 0; cb_ptr->read_q[i] != EMPTY; i++ ) ;
                        cb_ptr->read_q[i] = FINISHED;

                    }
                }

                *unitstat = CSW_CE | CSW_DE;
            }
        }
 
        break;


    case 0x02:
    case 0x06:
    case 0x0B:
    /*---------------------------------------------------------------*/
    /* READ - Send data to channel                                   */
    /*---------------------------------------------------------------*/

        readlen = 0;
 
        read_chk.fd = cb_ptr->sock;
        read_chk.events = POLLIN;

        if ( cb_ptr->read_q[0] != EMPTY )
        {       /* Data that needs to be sent to MTS has been queued */
            debug_pf(" READ_Q = %d, %d, %d, %d, %d, %d, %d, %d, %d, %d\n",
                cb_ptr->read_q[0], cb_ptr->read_q[1], cb_ptr->read_q[2], cb_ptr->read_q[3],
                cb_ptr->read_q[4], cb_ptr->read_q[5], cb_ptr->read_q[6], cb_ptr->read_q[7],
                cb_ptr->read_q[8], cb_ptr->read_q[9]);

            switch ( cb_ptr->read_q[0] ) {
            case CONFIG:    /* The config command reply was left in dev->buf */
                readlen = ntohs( ((struct buff_hdr *) dev->buf)->buffer_length )
                    + sizeof(struct buff_hdr);

                memcpy(iobuf, dev->buf, readlen);
                break;

            case MSS:
                readlen = return_mss( cb_ptr, (struct packet_hdr *) iobuf );
                break;

            case ACK:
                cb_ptr->mts_header.him_hdr.buffer_number++;
                cb_ptr->mts_header.ip_header.ip_id =
                    htons( ntohs( cb_ptr->mts_header.ip_header.ip_id ) + 1 );
                memcpy(iobuf, &cb_ptr->mts_header, 44);
                readlen = 44;
                break;

            case FIN:
                cb_ptr->mts_header.him_hdr.buffer_number++;
                cb_ptr->mts_header.ip_header.ip_id =
                    htons( ntohs( cb_ptr->mts_header.ip_header.ip_id ) + 1 );
                memcpy(iobuf, &cb_ptr->mts_header, 44);
                ((struct packet_hdr *) iobuf)->sh.tcp_header.fin = 1;
                readlen = 44;

                if ( cb_ptr->state == CONNECTED )
                    cb_ptr->state = CLOSING;

                break;

            case FINISHED:
                cb_ptr->mts_header.him_hdr.buffer_number++;
                cb_ptr->mts_header.him_hdr.finished_flag = 1;
                cb_ptr->mts_header.him_hdr.buffer_length = 0;
                memcpy(iobuf, &cb_ptr->mts_header, 4);
                readlen = 4;

                (void) close(cb_ptr->sock);
                memset ((char *) cb_ptr, '\0', sizeof(struct io_cb));
                cb_ptr->sock = -1;

            default: ;

            }

            if (cb_ptr->protocol == IPPROTO_TCP && cb_ptr->state == INITIALIZED)
                start_sock_thread(dev);

            /* Remove first entry from queue, a NOP on a closed connection */
            for ( i = 0; i < 15; i++ )
                cb_ptr->read_q[i] = cb_ptr->read_q[i+1];

            *residual = count - readlen;
            *unitstat = CSW_CE | CSW_DE;

        }
        else if ( cb_ptr->state == CLOSING )
        {
            *residual = count;
            *unitstat = CSW_CE | CSW_DE | CSW_UX;

            debug_pf(" ------ READ ccw, STATE = CLOSING\n");

        }
        else if ( !poll(&read_chk, 1, 50) )  /* i.e. no data available from the socket */
        {
            if ( !cb_ptr->watch_sock )
                start_sock_thread(dev);

            *residual = count;
            *unitstat = CSW_CE | CSW_DE | CSW_UX;

        }
        else if ( cb_ptr->protocol == IPPROTO_UDP )
        {
            cb_ptr->mts_header.him_hdr.buffer_number++;
            cb_ptr->mts_header.ip_header.ip_id =
                htons( ntohs( cb_ptr->mts_header.ip_header.ip_id ) + 1);
            memcpy(buff_ptr, &cb_ptr->mts_header, 32);

            readlen = recvfrom(cb_ptr->sock,
                &((char *) buff_ptr)[32], 1460, 0, &cb_ptr->sin, &sinlen);
 
            buff_ptr->him_hdr.buffer_length = 
                buff_ptr->ip_header.ip_len = htons( readlen + 28 );

            buff_ptr->ip_header.ip_src = cb_ptr->sin.sin_addr;
            buff_ptr->sh.udp_header.uh_sport = cb_ptr->sin.sin_port;

            *residual = count - (readlen + 32);
            *unitstat = CSW_CE | CSW_DE;

        }
        else if ( cb_ptr->passive && cb_ptr->state == INITIALIZED )
        {
            temp_sock = cb_ptr->sock;
            cb_ptr->sock = accept(temp_sock, &cb_ptr->sin, &sinlen);
 
            (void) close(temp_sock);
            cb_ptr->state = CONNECTED;
 
            getpeername(cb_ptr->sock, &cb_ptr->sin, &sinlen);
            cb_ptr->mts_header.ip_header.ip_src = cb_ptr->sin.sin_addr;
            cb_ptr->mts_header.sh.tcp_header.source = cb_ptr->sin.sin_port;

            *residual = count - return_mss( cb_ptr, (struct packet_hdr *) iobuf );
            *unitstat = CSW_CE | CSW_DE;

            debug_pf("just accepted call on socket %d for socket %d\n", temp_sock, cb_ptr->sock);

        }
        else if ( cb_ptr->state == CONNECTED ) /* A UDP connection will never be in this state */
        {
            cb_ptr->mts_header.him_hdr.buffer_number++;
            cb_ptr->mts_header.ip_header.ip_id =
                htons( ntohs( cb_ptr->mts_header.ip_header.ip_id ) + 1);
            memcpy(iobuf, &cb_ptr->mts_header, 44);
 
            buff_ptr->sh.tcp_header.psh = 1;    /* th_flags |= TH_PUSH; */ 
            readlen = read(cb_ptr->sock, &((char *) iobuf)[44], 1460);
 
            if (readlen > 0) {
                cb_ptr->mts_header.sh.tcp_header.seq =
                    htonl( ntohl( cb_ptr->mts_header.sh.tcp_header.seq ) + readlen);
                buff_ptr->him_hdr.buffer_length =
                    buff_ptr->ip_header.ip_len = htons( readlen + 40 );

                *residual = count - (readlen + 44);
                *unitstat = CSW_CE | CSW_DE;

            }
            else if (readlen == 0) {
                buff_ptr->sh.tcp_header.fin = 1;  /* th_flags |= TH_FIN; */ 
                cb_ptr->state = CLOSING;

                *residual = count - 44;
                *unitstat = CSW_CE | CSW_DE;

            }
            else {
                debug_pf(" --- cb_ptr->state == CONNECTED, read rc = %i\n", readlen);
                dumpdata("I/O cb", (BYTE *)cb_ptr, sizeof(struct io_cb));
 
                buff_ptr->sh.tcp_header.rst = 1;  /* sh_flags |= TH_RST; */ 
                *residual = count - 44;
                *unitstat = CSW_CE | CSW_DE | CSW_UC;

            }
        }
        else
        {
            *residual = count;
            *unitstat = CSW_CE | CSW_DE | CSW_UX;

            debug_pf(" ------ Unexpected READ ccw, STATE = %d\n", cb_ptr->state);
        }

        if ( *residual != count) /* i.e. we are returning data */
        {
            debug_pf("data  to  MTS       DevNum = %04X\n", dev->devnum);
            dumpdata("", iobuf, 44);
            if (readlen > 0 && cb_ptr->protocol == IPPROTO_TCP)
                debug_pf("%.*s\n", readlen, &((char *) iobuf)[44]);
        }

        break;


    case 0x03:
    case 0x1B:
    case 0x4B:
    /*---------------------------------------------------------------*/
    /* CONTROL NO-OPERATION                                          */
    /*---------------------------------------------------------------*/

        *residual = 0;
        *unitstat = CSW_CE | CSW_DE;
        break;


    case 0x04:
    /*---------------------------------------------------------------*/
    /* SENSE                                                         */
    /*---------------------------------------------------------------*/

        /* Calculate residual byte count */
        num = (count < dev->numsense) ? count : dev->numsense;
        *residual = count - num;
        if (count < dev->numsense) *more = 1;

        /* Copy device sense bytes to channel I/O buffer */
        memcpy (iobuf, dev->sense, num);

        /* Clear the device sense bytes */
        memset (dev->sense, 0, sizeof(dev->sense));

        /* Return unit status */
        *unitstat = CSW_CE | CSW_DE;
        break;


    case 0xE4:
    /*---------------------------------------------------------------*/
    /* SENSE ID                                                      */
    /*---------------------------------------------------------------*/

        /* Calculate residual byte count */
        num = (count < dev->numdevid) ? count : dev->numdevid;
        *residual = count - num;
        if (count < dev->numdevid) *more = 1;

        /* Copy device identifier bytes to channel I/O buffer */
        memcpy (iobuf, dev->devid, num);

        /* Return unit status */
        *unitstat = CSW_CE | CSW_DE;
        break;


    default:
    /*---------------------------------------------------------------*/
    /* INVALID OPERATION                                             */
    /*---------------------------------------------------------------*/

        /* Set command reject sense byte, and unit check status */
        dev->sense[0] = SENSE_CR;
        *unitstat = CSW_CE | CSW_DE | CSW_UC;


    } /* end switch(code) */

 /* debug_pf("------- devnum: %04X, Returning status = %02X, after call = %02X\n",
        dev->devnum, *unitstat, code); */

} /* end function him_execute_ccw */


#if defined(OPTION_DYNAMIC_LOAD)
static
#endif
DEVHND him_device_hndinfo = {
        &him_init_handler,             /* Device Initialisation      */
        &him_execute_ccw,              /* Device CCW execute         */
        &him_close_device,             /* Device Close               */
        &him_query_device,             /* Device Query               */
        NULL,                          /* Device Extended Query      */
        NULL,                          /* Device Start channel pgm   */
        NULL,                          /* Device End channel pgm     */
        NULL,                          /* Device Resume channel pgm  */
        NULL,                          /* Device Suspend channel pgm */
        NULL,                          /* Device Halt channel pgm    */
        NULL,                          /* Device Read                */
        NULL,                          /* Device Write               */
        NULL,                          /* Device Query used          */
        NULL,                          /* Device Reserve             */
        NULL,                          /* Device Release             */
        NULL,                          /* Device Attention           */
        NULL,                          /* Immediate CCW Codes        */
        NULL,                          /* Signal Adapter Input       */
        NULL,                          /* Signal Adapter Output      */
        NULL,                          /* Signal Adapter Sync        */
        NULL,                          /* Signal Adapter Output Mult */
        NULL,                          /* QDIO subsys desc           */
        NULL,                          /* QDIO set subchan ind       */
        NULL,                          /* Hercules suspend           */
        NULL                           /* Hercules resume            */
};

/* Libtool static name colision resolution */
/* note : lt_dlopen will look for symbol & modulename_LTX_symbol */
#if !defined(HDL_BUILD_SHARED) && defined(HDL_USE_LIBTOOL)
#define hdl_ddev hdttcph_LTX_hdl_ddev
#define hdl_depc hdttcph_LTX_hdl_depc
#define hdl_reso hdttcph_LTX_hdl_reso
#define hdl_init hdttcph_LTX_hdl_init
#define hdl_fini hdttcph_LTX_hdl_fini
#endif


#if defined(OPTION_DYNAMIC_LOAD)
HDL_DEPENDENCY_SECTION;
{
    HDL_DEPENDENCY(HERCULES);
    HDL_DEPENDENCY(DEVBLK);
    HDL_DEPENDENCY(SYSBLK);
}
END_DEPENDENCY_SECTION


HDL_DEVICE_SECTION;
{
    HDL_DEVICE(AUSC, him_device_hndinfo );
    HDL_DEVICE(UDPH, him_device_hndinfo );
    HDL_DEVICE(TLNT, him_device_hndinfo );
    HDL_DEVICE(TCPH, him_device_hndinfo );
}
END_DEVICE_SECTION
#endif

 
/*
 *  When MTS wants to start using a particular subchannel it sends out an 
 *  EBCDIC character string that indicates how the subchannel will be used.
 *  This configuration command indicates the type of connection, the protocol,
 *  whether it will be an active or passive connection, address information
 *  for the local and foreign sockets, and whether this is a telnet server
 *  subchannel or not.  This routine uses this information to initialize
 *  the subchannel for further use.
 */
 
static void config_subchan ( struct io_cb *iocb_ptr, BYTE *config_data )
{
    int cd_len;
    struct config_reply *reply_ptr;
    static unsigned char Ok[] = {0xd6, 0x92},           /* in EBCDIC */
        Failed[] = {0xc6, 0x81, 0x89, 0x93, 0x85, 0x84};
 
    cd_len = ntohs( ((struct buff_hdr *) config_data)->buffer_length );
 
    /* Build the reply right on top of the configuration data */
    reply_ptr = (struct config_reply *) config_data;

    if ( iocb_ptr->state != SHUTDOWN  ||
         !parse_config_data(iocb_ptr, (char *) &config_data[4], cd_len) )
    {
        (void) close(iocb_ptr->sock);
        memset ((char *) iocb_ptr, '\0', sizeof(struct io_cb));
        iocb_ptr->sock = -1;

        reply_ptr->him_hdr.init_flag = 1;
        reply_ptr->him_hdr.buffer_number = 1;
        reply_ptr->him_hdr.buffer_length = htons(6);
        memcpy(reply_ptr->config_ok, Failed, 6);  /* EBCDIC "Failed" */
    }
    else
    {                              /* Set up socket for non-servers. */
        if (!iocb_ptr->server &&
            (!iocb_ptr->passive || iocb_ptr->mts_header.sh.tcp_header.dest == 0))
        {
            iocb_ptr->sock =
                get_socket(iocb_ptr->protocol, iocb_ptr->mts_header.sh.tcp_header.dest,
                    &iocb_ptr->sin, iocb_ptr->passive ? QLEN : 0);

            /*  Set the destination port in the MTS header as well */
            iocb_ptr->mts_header.sh.tcp_header.dest = iocb_ptr->sin.sin_port;
        }
 
        /* Finish initializing the configuration command reply */
        memset((char *) reply_ptr, '\0', sizeof (struct config_reply));
        reply_ptr->him_hdr.init_flag = 1;
        reply_ptr->him_hdr.buffer_number = 1;
        reply_ptr->him_hdr.buffer_length =
            htons( sizeof(struct config_reply) - sizeof(struct buff_hdr) );

        memcpy(reply_ptr->config_ok, Ok, 2);          /* EBCDIC "Ok" */
        reply_ptr->family = AF_LOCAL;
        reply_ptr->protocol = iocb_ptr->protocol;
        reply_ptr->local_port = iocb_ptr->mts_header.sh.tcp_header.dest;
        /* reply_ptr->local_ip = iocb_ptr->mts_header.ip_header.ip_dst; */
        memcpy(reply_ptr->local_ip, &iocb_ptr->mts_header.ip_header.ip_dst, 4);

        iocb_ptr->state = INITIALIZED;
    }

} /* end function config_subchan */
 
/*
 *  This routine uses the configuration string that MTS sends to initialize
 *  the TCP/IP header in the I/O control block.  An example configuration
 *  string might look like this:
 *
 *     type=internet protocol=tcp active local_socket=(0,0.0.0.0)
 */
 
static int parse_config_data ( struct io_cb *iocb_ptr, char *config_string, int cs_len )
{
    char *lhs_token, *rhs_token, *echo_rhs = NULL;
    int port, i, j, success = 1;
    u_int32_t ip_addr = 0, our_ipaddr = 0;
    char host_name[64];
    struct hostent *hostent_ptr;
 
    enum lhs_codes {LHS_TYPE, LHS_PROTOCOL, LHS_ACTIVE, LHS_PASSIVE,
                    LHS_LOCALSOCK, LHS_FOREIGNSOCK, LHS_SERVER};
 
    static char *lhs_tbl[] = {
      "type",         "protocol",       "active",    "passive",
      "local_socket", "foreign_socket", "server"};
 
    /*
     *  Get our IP address
     */
 
    gethostname(host_name, sizeof host_name);

    if ( (hostent_ptr = gethostbyname(host_name)) )
    {
        /* our_ipaddr = -970268084; * current ADSL address 76.226.42.198 */
        our_ipaddr = *(u_int *)hostent_ptr->h_addr;
        debug_pf("Our IP address = %08X\n", ntohl( (u_int)our_ipaddr ) );
    }
    else
        debug_pf("Excuse me?,  What is our IP address?\n");
 
 
    /*
     *  Build an MTS TCP/IP header
     */
 
    iocb_ptr->mts_header.him_hdr.buffer_number = 1;
    iocb_ptr->mts_header.him_hdr.buffer_length = htons(40);

    iocb_ptr->mts_header.ip_header.ip_v = IPVERSION;
    iocb_ptr->mts_header.ip_header.ip_hl = 5;
    iocb_ptr->mts_header.ip_header.ip_len = htons(40);
    iocb_ptr->mts_header.ip_header.ip_id = htons(1);
    iocb_ptr->mts_header.ip_header.ip_ttl = 58;
    iocb_ptr->mts_header.ip_header.ip_p = IPPROTO_TCP;
    iocb_ptr->mts_header.ip_header.ip_dst.s_addr = our_ipaddr;

    iocb_ptr->mts_header.sh.tcp_header.seq = htonl(1);
    iocb_ptr->mts_header.sh.tcp_header.doff = 5;
    iocb_ptr->mts_header.sh.tcp_header.ack = 1;
    iocb_ptr->mts_header.sh.tcp_header.window = htons(6 * 4096);
 
    /*
     *  Now, convert the EBCDIC configuration command that MTS just sent to ASCII,
     *  parse the string and use that information to update the MTS TCP/IP header.
     */

    config_string[cs_len] = '\0';

    while (--cs_len >= 0)
        config_string[cs_len] = tolower( guest_to_host( (u_char)config_string[cs_len] ) );

    lhs_token = strtok(config_string, " =");
 
    do {
        for (i = 0; (strcmp(lhs_token, lhs_tbl[i]) != 0) && i < LHS_SERVER; i++);
 
        switch (i)
        {
        case LHS_TYPE:
            echo_rhs = rhs_token = strtok(NULL, " =");
            break;
 
        case LHS_PROTOCOL:
            echo_rhs = rhs_token = strtok(NULL, " =");
            iocb_ptr->mts_header.ip_header.ip_p = iocb_ptr->protocol =
                strcmp(rhs_token, "udp") == 0 ? IPPROTO_UDP : IPPROTO_TCP;
            break;
 
        case LHS_ACTIVE:
        case LHS_PASSIVE:
            echo_rhs = rhs_token = NULL;
            iocb_ptr->passive = (i == LHS_PASSIVE);
            break;
 
        case LHS_LOCALSOCK:
        case LHS_FOREIGNSOCK:
            echo_rhs = rhs_token = strtok(NULL, " =");
            rhs_token++;
            port = strtol(rhs_token, &rhs_token, 10);
 
            for (j = 0; j < 4; j++)
            {
                rhs_token++;
                ip_addr = (ip_addr << 8) | strtol(rhs_token, &rhs_token, 10);
            }
 
            if (i == LHS_LOCALSOCK)          /* Set local socket values */
            {
                iocb_ptr->mts_header.ip_header.ip_dst.s_addr = 
                   (ip_addr != INADDR_ANY ? ip_addr : our_ipaddr);
                iocb_ptr->mts_header.sh.tcp_header.dest = htons(port);
            }
            else                           /* Set foreign socket values */
            {
                iocb_ptr->mts_header.ip_header.ip_src.s_addr = ip_addr;
                iocb_ptr->mts_header.sh.tcp_header.source = htons(port);
            }
            break;
 
        case LHS_SERVER:
            echo_rhs = rhs_token = NULL;
            iocb_ptr->server = 1;
            break;
        }
 
        if (echo_rhs == NULL)
            debug_pf(" %s, no right hand side\n", lhs_token);

        else
            debug_pf(" %s = %s\n", lhs_token, echo_rhs);
 
    } while ( (lhs_token = strtok(NULL, " =")) );

    return success;
} /* end function parse_config_data */
 
 
/*
 *  Get_Socket - allocate & bind a socket using TCP or UDP
 */
 
static int get_socket ( int protocol, int port, struct sockaddr_in *sin, int qlen )
{
    /* int protocol;              * protocol to use ("IPPROTO_TCP" or "IPPROTO_UDP") *
       int port;                  * Port number to use or 0 for any port       *
       struct sockaddr_in *sin;   * will be returned with assigned port        *
       int qlen;                  * maximum length of the server request queue */
 
    int s, socktype, optval;  /* socket descriptor and socket type          */
    struct sockaddr_in our_sin;
    unsigned int sinlen = sizeof (struct sockaddr_in);
 
 
    memset((char *)&our_sin, '\0', sizeof(struct sockaddr_in));
    our_sin.sin_family = AF_INET;
    our_sin.sin_port = port;
    our_sin.sin_addr.s_addr = INADDR_ANY;
 
    /* Use protocol to choose a socket type */
    socktype = protocol == IPPROTO_UDP ? SOCK_DGRAM : SOCK_STREAM;


    /* Allocate a socket */
    s = socket(PF_INET, socktype, 0);
    if (s < 0)
        debug_pf("can't create socket\n");
 
    /* Set REUSEADDR option */
    optval = 4;
    if (setsockopt(s, SOL_SOCKET, SO_REUSEADDR, &optval, sizeof optval) < 0)
        debug_pf("setsockopt\n");
 
    /* Bind the socket */
    if (bind(s, &our_sin, sizeof(struct sockaddr_in)) < 0)
        debug_pf("can't bind to port\n");
 
    /* Retrieve complete socket info */
    if (getsockname(s, &our_sin, &sinlen) < 0)
        debug_pf("getsockname\n");
 
    if (socktype == SOCK_STREAM && qlen && listen(s, qlen) < 0)
        debug_pf("can't listen on port");
 
    if (sin != NULL)
        memcpy(sin, (char *)&our_sin, sizeof (struct sockaddr_in));
 
    return s;
} /* end function get_socket */


/*
 *  Set up a Maximum Segment Size (MSS) acknowledgement
 */
 
static int return_mss ( struct io_cb * iocb_ptr, struct packet_hdr *mss )
{
    iocb_ptr->mts_header.him_hdr.buffer_number++;
    iocb_ptr->mts_header.ip_header.ip_id =
        htons( ntohs( iocb_ptr->mts_header.ip_header.ip_id ) + 1 );
    memcpy(mss, &iocb_ptr->mts_header, 44);
 
    mss->him_hdr.buffer_length = mss->ip_header.ip_len =
        htons( sizeof (struct packet_hdr) - sizeof (struct buff_hdr) );
    mss->ip_header.ip_ttl = MAXTTL;
    mss->sh.tcp_header.doff = 6;
    mss->sh.tcp_header.syn = 1;
    mss->tcp_optcode = TCPOPT_MAXSEG;
    mss->tcp_optlen = 4;
    mss->tcp_optval = htons(1460);

    return sizeof(struct packet_hdr);
}


/*-------------------------------------------------------------------*/
/* Sockdev "OnConnection" callback function                          */
/*-------------------------------------------------------------------*/
static int start_sock_thread (DEVBLK* dev)
{
    TID tid;
    int rc;

    ((struct io_cb *)dev->dev_data)->watch_sock = 1;

    rc = create_thread( &tid, DETACHED, skt_thread, dev, NULL );
    if(rc)
    {
        WRMSG( HHC00102, "E", strerror( rc ) );
        return 0;
    }
    return 1;
}

/*-------------------------------------------------------------------*/
/* Thread to monitor the sockdev remote print spooler connection     */
/*-------------------------------------------------------------------*/
static void* skt_thread (DEVBLK* dev)
{
    int rc, poll_timer, sleep_timer;
    struct pollfd read_chk;

    /* Fix thread name */
    {
        char thread_name[32];
        thread_name[sizeof(thread_name)-1] = 0;
        snprintf( thread_name, sizeof(thread_name)-1,
            "skt_thread %1d:%04X", SSID_TO_LCSS(dev->ssid), dev->devnum );
        SET_THREAD_NAME( thread_name );
    }

    read_chk.fd = ((struct io_cb *)dev->dev_data)->sock;
    read_chk.events = POLLIN;
    poll_timer = 20;       /* milliseconds */
    sleep_timer = 20000;   /* microseconds */

    while ( ((struct io_cb *)dev->dev_data)->watch_sock )
        if ( !((struct io_cb *)dev->dev_data)->rnr && poll(&read_chk, 1, poll_timer) > 0 )
            rc = device_attention (dev, CSW_ATTN);

        else
            usleep( sleep_timer );

/*
    while ( ((struct io_cb *)dev->dev_data)->watch_sock && poll_timer < 32000)
        if ( !((struct io_cb *)dev->dev_data)->rnr && poll(&read_chk, 1, poll_timer) > 0 )
        {
            rc = device_attention (dev, CSW_ATTN);
            poll_timer = 20;
            sleep_timer = 20000;
        }
        else
        {
            usleep( sleep_timer );

            if ( !((struct io_cb *)dev->dev_data)->rnr )   * Still no data, lengthen wait *
            {
                poll_timer *= 2;
                sleep_timer *= 2;
            }
        }

    if ( poll_timer > 32000 )
        debug_pf("----- Poll timer TIMEOUT, should probably close connection\n");
*/

    /* obtain_lock( &dev->lock );

    // PROGRAMMING NOTE: the following tells us whether we detected
    // the error or if the device thread already did. If the device
    // thread detected it while we were sleeping (and subsequently
    // closed the connection) then we don't need to do anything at
    // all; just exit. If we were the ones that detected the error
    // however, then we need to close the connection so the device
    // thread can learn of it...

    if (dev->fd == fd)
    {
        dev->fd = -1;
        close_socket( fd );
        WRMSG (HHC01100, "I", SSID_TO_LCSS(dev->ssid), dev->devnum,
               dev->bs->clientname, dev->bs->clientip, dev->bs->spec);
    }

    release_lock( &dev->lock ); */

    return NULL;

} /* end function skt_thread */


/*
 *  Used for writing debug output on stream 5
 */

static void debug_pf ( __const char *__restrict __fmt, ... )
{
    char write_buf[2000];             /* big enough for an IP packet */
    va_list arglist;

    va_start( arglist, __fmt );
    write( 5, write_buf, vsprintf( write_buf, __fmt, arglist ) );

    va_end( arglist );

} /* end function debug_pf */


/*
 *  Used for dumping debugging data in a formatted hexadecimal form
 */

static void dumpdata ( char *label, BYTE *data, int len )
{
    char *hex = "0123456789ABCDEF", write_buf[100], ascii_hex[80];
    int index = 0, space_chk = 0;
 
    if ( strlen(label) > 0 )
        write( 5, write_buf, sprintf(write_buf, "%s: \n", label) );

    if ( len > 256 )
    {
        write( 5, write_buf, sprintf(write_buf, "Dumpdata len = %i, will be truncated\n", len) );
        len = 256;
    }   

    while ( len-- > 0 )
    {
        ascii_hex[index++] = hex[(*data >> 4) & 0xF];
        ascii_hex[index++] = hex[*data & 0xF];

        space_chk++;
        if ( space_chk % 4 == 0 )
            ascii_hex[index++] = ' ';

        if ( index > 71 )
        {
            ascii_hex[index] = '\0';
            write( 5, write_buf, sprintf(write_buf, " %s\n", ascii_hex) );
            index = space_chk = 0;
        }
        data++;
    }
 
    ascii_hex[index] = '\0';
    if ( strlen(ascii_hex) > 0 )
        write( 5, write_buf, sprintf(write_buf, " %s\n", ascii_hex) );

} /* end function dumpdata */
