/*
 * This is the main module of the CNTLM
 *
 * CNTLM is free software; you can redistribute it and/or modify it under the
 * terms of the GNU General Public License as published by the Free Software
 * Foundation; either version 2 of the License, or (at your option) any later
 * version.
 *
 * CNTLM is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
 * details.
 *
 * You should have received a copy of the GNU General Public License along with
 * this program; if not, write to the Free Software Foundation, Inc., 51 Franklin
 * St, Fifth Floor, Boston, MA 02110-1301, USA.
 *
 * Copyright (c) 2007 David Kubicek
 *
 */

#include <sys/types.h>
#include <sys/time.h>
#include <sys/select.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <pthread.h>
#include <limits.h>
#include <stdio.h>
#include <errno.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <signal.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <netdb.h>
#include <ctype.h>
#include <pwd.h>
#include <fcntl.h>
#include <syslog.h>
#include <termios.h>
#include <fnmatch.h>
#include <assert.h>

#ifdef __CYGWIN__
#include <windows.h>
#endif

/*
 * Some helping routines like linked list manipulation substr(), memory
 * allocation, NTLM authentication routines, etc.
 */
#include "config/config.h"
#include "socket.h"
#include "utils.h"
#include "ntlm.h"
#include "swap.h"
#include "config.h"
#include "auth.h"
#include "http.h"
#include "globals.h"
#include "forward.h"                /* code serving via parent proxy */
#include "direct.h"                /* code serving directly without proxy */
#include "sys.h"

#ifdef __CYGWIN__
#include "sspi.h"				/* code for SSPI management */
#endif

#ifdef ENABLE_KERBEROS
#include "kerberos.h"
#endif
#ifdef ENABLE_PACPARSER
#include <pacparser.h>
#endif

#define STACK_SIZE    sizeof(void *)*8*1024

typedef struct config_vars_s {
    char *cauth;
    char *cdomain;
    char *head;
    char *cpassword;
    char *cpassntlm2;
    char *cpassnt;
    char *cpasslm;
    char *cuser;
    char *cworkstation;
    char *cuid;
    char *cpidfile;
    char *magic_detect;
    char *myconfig;
    plist_t tunneld_list;
    plist_t proxyd_list;
    plist_t socksd_list;
    plist_t rules;
} config_vars_t;
/*
 * Global "read-only" data initialized in main(). Comments list funcs. which use
 * them. Having these global avoids the need to pass them to each thread and
 * from there again a few times to inner calls.
 */
int debug = 0;                    /* all debug printf's and possibly external modules */

/**
 * Values and their meaning:
 * 0 - no requests are logged - default
 * 1 - requests are logged (old behavior)
 */
int request_logging_level = 0;

struct auth_s *g_creds = NULL;            /* throughout the whole module */

void parse_option(int opt, config_vars_t);

int show_help(char **argv);

void clean_memory(config_vars_t);

void change_ids(char *);

void run_poll_loop(config_vars_t);

void parse_config(config_t , config_vars_t);

int quit = 0;                    /* sighandler() */
int ntlmbasic = 0;                /* forward_request() */
int serialize = 0;
int scanner_plugin = 0;
long scanner_plugin_maxsize = 0;

/*
 * List of finished threads. Each forward_request() thread adds itself to it when
 * finished. Main regularly joins and removes all tid's in there.
 */
plist_t threads_list = NULL;
pthread_mutex_t threads_mtx = PTHREAD_MUTEX_INITIALIZER;

/*
 * List of cached connections. Accessed by each thread forward_request().
 */
plist_t connection_list = NULL;
pthread_mutex_t connection_mtx = PTHREAD_MUTEX_INITIALIZER;

/*
 * List of available proxies and current proxy id for proxy_connect().
 */
int parent_count = 0;
plist_t parent_list = NULL;

/*
 * List of custom header substitutions, SOCKS5 proxy users and
 * UserAgents for the scanner plugin.
 */
hlist_t header_list = NULL;            /* forward_request() */
hlist_t users_list = NULL;            /* socks5_thread() */
plist_t scanner_agent_list = NULL;        /* scanner_hook() */
plist_t noproxy_list = NULL;            /* proxy_thread() */

#ifdef ENABLE_PACPARSER
/* 1 = Pacparser engine is initialized and in use. */
int pacparser_initialized = 0;

/*
 * Pacparser Mutex
 */
pthread_mutex_t pacparser_mtx = PTHREAD_MUTEX_INITIALIZER;
#endif

/*
 * General signal handler. If in debug mode, quit immediately.
 */
void sighandler(int p) {
    if (!quit) {
        syslog(LOG_INFO, "Signal %d received, issuing clean shutdown\n", p);
#ifdef ENABLE_PACPARSER
        if (pacparser_initialized) {
            pacparser_cleanup();
        }
#endif
    } else
        syslog(LOG_INFO, "Signal %d received, forcing shutdown\n", p);

    if (quit++ || debug)
        quit++;
}

/*
 * Parse proxy parameter and add it to the global list.
 */
int parent_add(const char *parent, int port) {
    char *spec;
    char *tmp;
    proxy_t *aux;
    struct addrinfo *addresses;

    /*
     * Check format and parse it.
     */
    spec = strdup(parent);
    const char *q = strrchr(spec, ':');
    if (q != NULL) {
        int p;
        p = (int) (q - spec);
        if (spec[0] == '[' && spec[p - 1] == ']') {
            tmp = substr(spec, 1, p - 2);
        } else {
            tmp = substr(spec, 0, p);
        }

        port = atoi(spec + p + 1);
        if (!port || !so_resolv(&addresses, tmp, port)) {
            syslog(LOG_ERR, "Cannot resolve listen address %s\n", spec);
            myexit(1);
        }
    } else {
        syslog(LOG_ERR, "Cannot resolve listen address %s\n", spec);
        myexit(1);
    }

    aux = (proxy_t *) zmalloc(sizeof(proxy_t));
#ifdef ENABLE_PACPARSER
    aux->type = PROXY;
#endif
    strlcpy(aux->hostname, tmp, sizeof(aux->hostname));
    aux->port = port;
    aux->resolved = 0;
    aux->addresses = NULL;
    parent_list = plist_add(parent_list, ++parent_count, (char *) aux);

    free(spec);
    free(tmp);
    return 1;
}

#ifdef ENABLE_PACPARSER
/*
 * Create list of proxy_t structs parsed from the PAC string returned
 * by Pacparser.
 * TODO: Harden against malformed pacp_str.
 */
plist_t pac_create_list(plist_t paclist, char *pacp_str) {
    int paclist_count = 0;
    char *pacp_tmp = NULL;
    char *cur_proxy = NULL;

    if (pacp_str == NULL) {
        paclist = NULL;
        return 0;
    }

    /* Make a copy of shared PAC string pacp_str (coming
     * from pacparser) to avoid manipulation by strsep.
     */
    pacp_tmp = zmalloc(sizeof(char) * strlen(pacp_str) + 1);
    strcpy(pacp_tmp, pacp_str);

    cur_proxy = strsep(&pacp_tmp, ";");

    if (debug)
        printf("Parsed PAC Proxies:\n");

    while (cur_proxy != NULL) {
        int type = DIRECT; // default is DIRECT
        char *type_str = NULL;
        char *hostname = NULL;
        char *port = NULL;
        proxy_t *aux;

        /* skip whitespace after semicolon */
        if (*cur_proxy == ' ')
            cur_proxy = cur_proxy + 1;

        type_str = strsep(&cur_proxy, " ");
        if (strcmp(type_str, "PROXY") == 0) {
            type = PROXY; // TODO: support more types
            hostname = strsep(&cur_proxy, ":");
            port = cur_proxy; // last token is always the port
        }

        if (debug) {
            if (type != DIRECT) {
                printf("   %s %s %s\n", type_str, hostname, port);
            } else {
                printf("   %s\n", type_str);
            }
        }

        aux = (proxy_t *)zmalloc(sizeof(proxy_t));
        aux->type = type;
        if (type == PROXY) {
            strlcpy(aux->hostname, hostname, sizeof(aux->hostname));
            aux->port = atoi(port);
            aux->resolved = 0;
        }
        paclist = plist_add(paclist, ++paclist_count, (char *)aux);
        cur_proxy = strsep(&pacp_tmp, ";"); /* get next proxy */
    }

    if (debug) {
        printf("Created PAC list with %d item(s):\n", paclist_count);
        plist_dump(paclist);
    }

    free(pacp_tmp);

    return paclist;
}
#endif

/*
 * Register and bind new proxy service port.
 */
void listen_add(const char *service, plist_t *list, char *spec, int gateway) {
    struct addrinfo *addresses;
    int p;
    int port;
    char *tmp;

    char *q = strrchr(spec, ':');
    if (q != NULL) {
        p = (int) (q - spec);
        if (spec[0] == '[' && spec[p - 1] == ']') {
            tmp = substr(spec, 1, p - 2);
        } else {
            tmp = substr(spec, 0, p);
        }

        port = atoi(spec + p + 1);
        if (!port || !so_resolv(&addresses, tmp, port)) {
            syslog(LOG_ERR, "Cannot resolve listen address %s\n", spec);
            myexit(1);
        }

        free(tmp);
    } else {
        port = atoi(spec);
        if (!port) {
            syslog(LOG_ERR, "Cannot resolve listen address %s\n", spec);
            myexit(1);
        }
        so_resolv_wildcard(&addresses, port, gateway);
    }

    so_listen(list, addresses, NULL);
    freeaddrinfo(addresses);
}

/*
 * Register a new tunnel definition, bind service port.
 */
void tunnel_add(plist_t *list, char *spec, int gateway) {
    struct addrinfo *addresses;
    int i;
    int len;
    int count;
    int pos;
    int port;
    char *field[4];
    char *tmp;

    spec = strdup(spec);
    len = strlen(spec);
    field[0] = spec;
    for (count = 1, i = 0; count < 4 && i < len; ++i)
        if (spec[i] == ':') {
            spec[i] = 0;
            field[count++] = spec + i + 1;
        }

    pos = 0;
    if (count == 4) {
        port = atoi(field[pos + 1]);
        if (!port || !so_resolv(&addresses, field[pos], port)) {
            syslog(LOG_ERR, "Cannot resolve tunnel bind address: %s:%s\n", field[pos], field[pos + 1]);
            myexit(1);
        }
        pos++;
    } else {
        port = atoi(field[pos]);
        if (!port) {
            syslog(LOG_ERR, "Invalid tunnel local port: %s\n", field[pos]);
            myexit(1);
        }
        so_resolv_wildcard(&addresses, port, gateway);
    }

    if (count - pos == 3) {
        if (!strlen(field[pos + 1]) || !strlen(field[pos + 2])) {
            syslog(LOG_ERR, "Invalid tunnel target: %s:%s\n", field[pos + 1], field[pos + 2]);
            myexit(1);
        }

        const size_t tmp_len = strlen(field[pos + 1]) + strlen(field[pos + 2]) + 2 + 1;
        tmp = zmalloc(tmp_len);
        strlcpy(tmp, field[pos + 1], tmp_len);
        strlcat(tmp, ":", tmp_len);
        strlcat(tmp, field[pos + 2], tmp_len);

        i = so_listen(list, addresses, tmp);
        if (i == 0) {
            syslog(LOG_INFO, "New tunnel to %s\n", tmp);
        } else {
            syslog(LOG_ERR, "Unable to bind tunnel");
            free(tmp);
        }
    } else {
        printf("Tunnel specification incorrect ([laddress:]lport:rserver:rport).\n");
        myexit(1);
    }

    free(spec);
    freeaddrinfo(addresses);
}

/*
 * Add no-proxy hostname/IP
 */
plist_t noproxy_add(plist_t list, char *spec) {
    char *tok;
    char *save;

    tok = strtok_r(spec, ", ", &save);
    while (tok != NULL) {
        if (debug)
            printf("Adding no-proxy for: '%s'\n", tok);
        list = plist_add(list, 0, strdup(tok));
        tok = strtok_r(NULL, ", ", &save);
    }

    return list;
}

int noproxy_match(const char *addr) {
    plist_const_t list;

    list = noproxy_list;
    while (list) {
        if (list->aux && strlen(list->aux)
            && fnmatch(list->aux, addr, 0) == 0) {
            if (debug)
                printf("MATCH: %s (%s)\n", addr, (char *) list->aux);
            return 1;
        } else if (debug)
            printf("   NO: %s (%s)\n", addr, (char *) list->aux);

        list = list->next;
    }

    return 0;
}

/*
 * Proxy thread - decide between direct and forward based on NoProxy
 * TODO: update
 */
void *proxy_thread(void *thread_data) {
    rr_data_t request;
    rr_data_t ret;
    int keep_alive;                /* Proxy-Connection */
#ifdef ENABLE_PACPARSER
    int pac_found = 0;
    char *pacp_str;

    plist_t pac_list = NULL;
#endif
    int cd = ((struct thread_arg_s *) thread_data)->fd;

    do {
        ret = NULL;
        keep_alive = 0;

        if (debug) {
            printf("\n******* Round 1 C: %d *******\n", cd);
            printf("Reading headers (%d)...\n", cd);
        }

        request = new_rr_data();
        if (!headers_recv(cd, request)) {
            free_rr_data(&request);
            break;
        }

#ifdef ENABLE_PACPARSER
        if (!pac_found) {
            pac_found = 1;

            /*
             * Create proxy list for request from PAC file.
             */
            pthread_mutex_lock(&pacparser_mtx);
            pacp_str = pacparser_find_proxy(request->url, request->hostname);
            pthread_mutex_unlock(&pacparser_mtx);

            pac_list = pac_create_list(pac_list, pacp_str);
        }
#endif

        do {
            /*
             * Are we being returned a request by forward_request or direct_request?
             */
            if (ret) {
                free_rr_data(&request);
                request = ret;

#ifdef ENABLE_PACPARSER
                /*
                 * Create proxy list for new request from PAC file.
                 */
                pthread_mutex_lock(&pacparser_mtx);
                pacp_str = pacparser_find_proxy(request->url, request->hostname);
                pthread_mutex_unlock(&pacparser_mtx);

                plist_free(pac_list);
                pac_list = NULL;
                pac_list = pac_create_list(pac_list, pacp_str);
#endif
            }

            keep_alive = hlist_subcmp(request->headers, "Proxy-Connection", "keep-alive");

            if (noproxy_match(request->hostname)) {
                /* No-proxy-list has highest precedence */
                ret = direct_request(thread_data, request);
#ifdef ENABLE_PACPARSER
                } else if (pacparser_initialized) {
                    /* If PAC is available, use it to serve request. */
                    ret = pac_forward_request(thread_data, request, pac_list);
                } else {
                    /* Else use statically configured proxies. */
                    ret = forward_request(thread_data, request, NULL);
                }
#else
            } else
                ret = forward_request(thread_data, request);
#endif

            if (debug)
                printf("proxy_thread: request rc = %p\n", (void *) ret);
#ifdef ENABLE_PACPARSER
            } while (ret != NULL && ret != (void *)-1 && ret != (void *)-2);
#else
        } while (ret != NULL && ret != (void *) -1);
#endif

        free_rr_data(&request);
        /*
         * If client asked for proxy keep-alive, loop unless the last server response
         * requested (Proxy-)Connection: close.
         */
#ifdef ENABLE_PACPARSER
        } while (keep_alive && ret != (void *)-1 && ret != (void *)-2 && !serialize);
#else
    } while (keep_alive && ret != (void *) -1 && !serialize);
#endif

    /*
     * Add ourselves to the "threads to join" list.
     */
    if (!serialize) {
        pthread_mutex_lock(&threads_mtx);
        pthread_t thread_id = pthread_self();
        threads_list = plist_add(threads_list, (unsigned long) thread_id, NULL);
        pthread_mutex_unlock(&threads_mtx);
    }

#ifdef ENABLE_PACPARSER
    plist_free(pac_list);
#endif
    free(thread_data);
    close(cd);

    return NULL;
}

/*
 * Tunnel/port forward thread - this method is obviously better solution than using extra
 * tools like "corkscrew" which after all require us for authentication and tunneling
 * their HTTP CONNECT in the first place.
 */
void *tunnel_thread(void *thread_data) {
    char *hostname;
    char *pos;

    assert(thread_data != NULL);
    const char *const thost = ((struct thread_arg_s *) thread_data)->target;

    hostname = strdup(thost);
    if ((pos = strchr(hostname, ':')) != NULL)
        *pos = 0;

    if (noproxy_match(hostname))
        direct_tunnel(thread_data);
    else
        forward_tunnel(thread_data);

    free(hostname);
    free(thread_data);

    /*
     * Add ourself to the "threads to join" list.
     */
    pthread_mutex_lock(&threads_mtx);
    pthread_t thread_id = pthread_self();
    threads_list = plist_add(threads_list, (unsigned long) thread_id, NULL);
    pthread_mutex_unlock(&threads_mtx);

    return NULL;
}

/*
 * SOCKS5 thread
 */
void *socks5_thread(void *thread_data) {
    static const uint8_t SOCKS5_AUTH_NO_AUTHENTICATION_REQUIRED = 0x00;
    static const uint8_t SOCKS5_AUTH_USERNAME_PASSWORD = 0x02;
    static const uint8_t SOCKS5_AUTH_NO_ACCEPTABLE_METHODS = 0xFF;
    char *thost;
    char *tport;
    char *uname;
    char *upass;
    unsigned short port;
    int ver;
    int r;
    int c;
    int i;
    int w;

    struct auth_s *tcreds = NULL;
    unsigned char *bs = NULL;
    unsigned char *auths = NULL;
    unsigned char *addr = NULL;
    int found = -1;
    int sd = -1;
    int open = !hlist_count(users_list);

    int cd = ((struct thread_arg_s *) thread_data)->fd;
    free(thread_data);

    /*
     * Check client's version, possibly fuck'em
     */
    bs = (unsigned char *) zmalloc(10);
    thost = zmalloc(MINIBUF_SIZE);
    tport = zmalloc(MINIBUF_SIZE);
    r = read(cd, bs, 2);
    if (r != 2 || bs[0] != 5)
        goto bailout;

    /*
     * Read offered auth schemes
     */
    c = bs[1];
    auths = (unsigned char *) zmalloc(c + 1);
    r = read(cd, auths, c);
    if (r != c)
        goto bailout;

    /*
     * Are we wide open and client is OK with no auth?
     */
    if (open) {
        for (i = 0; i < c && found < 0; ++i) {
            if (auths[i] == SOCKS5_AUTH_NO_AUTHENTICATION_REQUIRED) {
                found = auths[i];
            }
        }
    }

    /*
     * If not, accept plain auth if offered
     */
    if (found < 0) {
        for (i = 0; i < c && found < 0; ++i) {
            if (auths[i] == SOCKS5_AUTH_USERNAME_PASSWORD) {
                found = auths[i];
            }
        }
    }

    /*
     * If not open and no auth offered or open and auth requested, fuck'em
     * and complete the handshake
     */
    if (found < 0) {
        bs[0] = 5;
        bs[1] = SOCKS5_AUTH_NO_ACCEPTABLE_METHODS;
        (void) write_wrapper(cd, bs, 2); // We don't really care about the result
        goto bailout;
    } else {
        bs[0] = 5;
        bs[1] = found;
        w = write_wrapper(cd, bs, 2);
        if (w != 2) {
            syslog(LOG_ERR, "SOCKS5: write() for accepting AUTH method failed.\n");
        }
    }

    /*
     * Plain auth negotiated?
     */
    if (found != 0) {
        /*
         * Check ver and read username len
         */
        r = read(cd, bs, 2);
        if (r != 2) {
            bs[0] = 1;
            bs[1] = 0xFF;        /* Unsuccessful (not supported) */
            (void) write_wrapper(cd, bs, 2);
            goto bailout;
        }
        c = bs[1]; // ULEN

        /*
         * Read username and pass len
         */
        uname = zmalloc(c + 1);
        r = read(cd, uname, c + 1);
        if (r != c + 1) {
            free(uname);
            goto bailout;
        }
        i = uname[c]; // PLEN
        uname[c] = 0;
        c = i;

        /*
         * Read pass
         */
        upass = zmalloc(c + 1);
        r = read(cd, upass, c);
        if (r != c) {
            free(upass);
            free(uname);
            goto bailout;
        }
        upass[c] = 0;

        /*
         * Check credentials against the list
         */
        const char *tmp = hlist_get(users_list, uname);
        if (!hlist_count(users_list) || (tmp && !strcmp(tmp, upass))) {
            bs[0] = 1;
            bs[1] = 0;        /* Success */
        } else {
            bs[0] = 1;
            bs[1] = 0xFF;        /* Failed */
        }

        /*
         * Send response
         */
        w = write_wrapper(cd, bs, 2);
        if (w != 2) {
            syslog(LOG_ERR, "SOCKS5: write() for response of credentials check failed.\n");
        }
        free(upass);
        free(uname);

        /*
         * Fuck'em if auth failed
         */
        if (bs[1])
            goto bailout;
    }

    /*
     * Read request type
     */
    r = read(cd, bs, 4);
    if (r != 4)
        goto bailout;

    /*
     * Is it connect for supported address type (IPv4 or DNS)? If not, fuck'em
     */
    if (bs[1] != 1 || (bs[3] != 1 && bs[3] != 3)) {
        bs[0] = 5;
        bs[1] = 2;            /* Not allowed */
        bs[2] = 0;
        bs[3] = 1;            /* Dummy IPv4 */
        memset(bs + 4, 0, 6);
        (void) write_wrapper(cd, bs, 10);
        goto bailout;
    }

    /*
     * Ok, it's connect to a domain or IP
     * Let's read dest address
     */
    if (bs[3] == 1) {
        ver = 1;            /* IPv4, we know the length */
        c = 4;
    } else if (bs[3] == 3) {
        uint8_t string_length;
        ver = 2;            /* FQDN, get string length */
        r = read(cd, &string_length, 1);
        if (r != 1)
            goto bailout;
        c = string_length;
    } else
        goto bailout;

    addr = (unsigned char *) zmalloc(c + 10 + 1);
    r = read(cd, addr, c);
    if (r != c)
        goto bailout;
    addr[c] = 0;

    /*
     * Convert the address to character string
     */
    if (ver == 1) {
        snprintf(thost, MINIBUF_SIZE, "%d.%d.%d.%d", addr[0], addr[1], addr[2],
                 addr[3]);    /* It's in network byte order */
    } else {
        strlcpy(thost, (char *) addr, MINIBUF_SIZE);
    }

    /*
     * Read port number and convert to host byte order int
     */
    r = read(cd, &port, 2);
    if (r != 2)
        goto bailout;

    i = 0;
    if (noproxy_match(thost)) {
        sd = host_connect(thost, ntohs(port));
        i = (sd >= 0);
    } else {
        snprintf(tport, MINIBUF_SIZE, "%d", ntohs(port));
        strlcat(thost, ":", MINIBUF_SIZE);
        strlcat(thost, tport, MINIBUF_SIZE);

        tcreds = new_auth();
        sd = proxy_connect(tcreds);
        if (sd >= 0)
            i = prepare_http_connect(sd, tcreds, thost);
    }

    /*
     * Direct or proxy connect?
     */
    if (!i) {
        /*
         * Connect/tunnel failed, report
         */
        bs[0] = 5;
        bs[1] = 1;            /* General failure */
        bs[2] = 0;
        bs[3] = 1;            /* Dummy IPv4 */
        memset(bs + 4, 0, 6);
        (void) write_wrapper(cd, bs, 10);
        goto bailout;
    } else {
        /*
         * All right
         */
        bs[0] = 5;
        bs[1] = 0;            /* Success */
        bs[2] = 0;
        bs[3] = 1;            /* Dummy IPv4 */
        memset(bs + 4, 0, 6);
        w = write_wrapper(cd, bs, 10);
        if (w != 10) {
            syslog(LOG_ERR, "SOCKS5: write() for reporting success for connect failed.\n");
        }
    }


    /*
     * Let's give them bi-directional connection they asked for
     */
    tunnel(cd, sd);

    bailout:
    if (addr)
        free(addr);
    if (auths)
        free(auths);
    if (thost)
        free(thost);
    if (tport)
        free(tport);
    if (bs)
        free(bs);
    if (tcreds)
        free(tcreds);
    if (sd >= 0)
        close(sd);
    close(cd);

    return NULL;
}


int gateway = 0;
int help = 0;
int interactivepwd = 0;
int interactivehash = 0;
int tracefile = 0;
int cflags = 0;
int asdaemon = 1;

int main(int argc, char **argv) {
    int opt;
    config_vars_t config_vars;
    config_vars.myconfig = NULL;
    config_vars.magic_detect = NULL;
    config_vars.tunneld_list = NULL;
    config_vars.proxyd_list = NULL;
    config_vars.socksd_list = NULL;
    config_vars.rules = NULL;

    config_t cf = NULL;
#ifdef ENABLE_PACPARSER
    int pac = 0;
    char *pac_file;

    pac_file = zmalloc(PATH_MAX);
#endif

    g_creds = new_auth();
    config_vars.cuser = zmalloc(MINIBUF_SIZE);
    config_vars.cdomain = zmalloc(MINIBUF_SIZE);
    config_vars.cpassword = zmalloc(MINIBUF_SIZE);
    config_vars.cpassntlm2 = zmalloc(MINIBUF_SIZE);
    config_vars.cpassnt = zmalloc(MINIBUF_SIZE);
    config_vars.cpasslm = zmalloc(MINIBUF_SIZE);
    config_vars.cworkstation = zmalloc(MINIBUF_SIZE);
    config_vars.cpidfile = zmalloc(MINIBUF_SIZE);
    config_vars.cuid = zmalloc(MINIBUF_SIZE);
    config_vars.cauth = zmalloc(MINIBUF_SIZE);

    openlog("cntlm", LOG_CONS, LOG_DAEMON);

#if config_endian == 0
    syslog(LOG_INFO, "Starting cntlm version " VERSION " for BIG endian\n");
#else
    syslog(LOG_INFO, "Starting cntlm version " VERSION " for LITTLE endian\n");
#endif

    while ((opt = getopt(argc, argv, ":-:T:a:c:d:fghIl:p:r:su:vw:x:B:F:G:HL:M:N:O:P:R:S:U:X:q:")) != -1) {
        parse_option(opt, config_vars);
    }

    if (help > 0) {
        exit(show_help(argv));
    }

    if (debug) {
        printf("Cntlm debug trace, version " VERSION);
#ifdef __CYGWIN__
        printf(" windows/cygwin port");
#endif
        printf(".\nCommand line: ");
        for (int i = 0; i < argc; ++i)
            printf("%s ", argv[i]);
        printf("\n");
    }

    if (config_vars.myconfig) {
        if (!(cf = config_open(config_vars.myconfig))) {
            syslog(LOG_ERR, "Cannot access specified config file: %s\n", config_vars.myconfig);
            myexit(1);
        }
        free(config_vars.myconfig);
    }

    /*
     * More arguments on the command-line? Must be proxies.
     */

    int index = optind;
    while (index < argc) {
        char *tmp = strchr(argv[index], ':');
        parent_add(argv[index], !tmp && index + 1 < argc ? atoi(argv[index + 1]) : 0);
        index += (!tmp ? 2 : 1);
    }


    /*
     * No configuration file yet? Load the default.
     */
#ifdef SYSCONFDIR
    if (!cf) {
#ifdef __CYGWIN__
        tmp = getenv("PROGRAMFILES(X86)");
        if (tmp == NULL || strlen(tmp) == 0)
            tmp = getenv("PROGRAMFILES");
        if (tmp == NULL)
            tmp = "C:\\Program Files";

        head = zmalloc(MINIBUF_SIZE);
        strlcpy(head, tmp, MINIBUF_SIZE);
        strlcat(head, "\\Cntlm\\cntlm.ini", MINIBUF_SIZE);
        cf = config_open(head);
#else
        cf = config_open(SYSCONFDIR "/cntlm.conf");
#endif
        if (debug) {
            if (cf)
                printf("Default config file opened successfully\n");
            else
                syslog(LOG_ERR, "Could not open default config file\n");
        }
    }
#endif

#ifdef __CYGWIN__
    /*
     * Still no configuration file found?
     * Check if there is one in the same directory as the executable.
     */
    if (!cf) {
        const unsigned int path_size = PATH_MAX;
        char path[path_size];

        if (GetModuleFileNameA(NULL, path, path_size) > 0) {
            path[path_size - 1] = '\0';
            // Remove the *.exe part at the end
            for(unsigned int index = strlen(path); index > 0; --index) {
                if(path[index - 1] == '\\') {
                    path[index] = '\0';
                    break;
                }
            }
            strlcat(path, "cntlm.ini", path_size);
            path[path_size - 1] = '\0';
            cf = config_open(path);
            if (cf) {
                syslog(LOG_INFO, "Using config file %s\n", path);
            }
        }
    }
#endif

    /*
     * If any configuration file was successfully opened, parse it.
     */
    if (cf) {
        parse_config(cf, config_vars);
    }

    config_close(cf);


#ifdef ENABLE_PACPARSER
    /* Start Pacparser engine if pac_file available */
    /* TODO: pac file option in config file */
    if (pac) {
        /* Check if PAC file can be opened. */
        FILE *test_fd = NULL;
        if (!(test_fd = fopen(pac_file, "r"))) {
            syslog(LOG_ERR, "Cannot access specified PAC file: '%s'\n", pac_file);
            myexit(1);
        }
        fclose(test_fd);

        /* Initiailize Pacparser. */
        pacparser_init();
        pacparser_parse_pac(pac_file);
        if (debug)
            printf("Pacparser initialized with PAC file %s\n", pac_file);
        // TODO handle parsing errors from pacparser
        pacparser_initialized = 1;
    }

    if (!interactivehash && !parent_list && !pac)
#else
    if (!interactivehash && !parent_list)
#endif
        croak("Parent proxy address missing.\n", interactivepwd || config_vars.magic_detect);

    if (!interactivehash && !config_vars.magic_detect && !config_vars.proxyd_list)
        croak("No proxy service ports were successfully opened.\n", interactivepwd);

    /*
     * Set default value for the workstation. Hostname if possible.
     */
    if (!strlen(config_vars.cworkstation)) {
#if config_gethostname == 1
        gethostname(cworkstation, MINIBUF_SIZE);
#endif
        if (!strlen(config_vars.cworkstation))
            strlcpy(config_vars.cworkstation, "cntlm", MINIBUF_SIZE);

        syslog(LOG_INFO, "Workstation name used: %s\n", config_vars.cworkstation);
    }

    /*
     * Parse selected NTLM hash combination.
     */
    if (strlen(config_vars.cauth)) {
        if (!strcasecmp("ntlm", config_vars.cauth)) {
            g_creds->hashnt = 1;
            g_creds->hashlm = 1;
            g_creds->hashntlm2 = 0;
        } else if (!strcasecmp("nt", config_vars.cauth)) {
            g_creds->hashnt = 1;
            g_creds->hashlm = 0;
            g_creds->hashntlm2 = 0;
        } else if (!strcasecmp("lm", config_vars.cauth)) {
            g_creds->hashnt = 0;
            g_creds->hashlm = 1;
            g_creds->hashntlm2 = 0;
        } else if (!strcasecmp("ntlmv2", config_vars.cauth)) {
            g_creds->hashnt = 0;
            g_creds->hashlm = 0;
            g_creds->hashntlm2 = 1;
        } else if (!strcasecmp("ntlm2sr", config_vars.cauth)) {
            g_creds->hashnt = 2;
            g_creds->hashlm = 0;
            g_creds->hashntlm2 = 0;
#ifdef ENABLE_KERBEROS
            } else if (!strcasecmp("gss", cauth)) {
                g_creds->haskrb = KRB_FORCE_USE_KRB;
                g_creds->hashnt = 0;
                g_creds->hashlm = 0;
                g_creds->hashntlm2 = 0;
                syslog(LOG_INFO, "Forcing GSS auth.\n");
#endif
        } else {
            syslog(LOG_ERR, "Unknown NTLM auth combination.\n");
            myexit(1);
        }
    }

    if (config_vars.socksd_list && !users_list)
        syslog(LOG_WARNING, "SOCKS5 proxy will NOT require any authentication\n");

    if (!config_vars.magic_detect)
        syslog(LOG_INFO, "Using following NTLM hashes: NTLMv2(%d) NT(%d) LM(%d)\n",
               g_creds->hashntlm2, g_creds->hashnt, g_creds->hashlm);

    if (cflags) {
        syslog(LOG_INFO, "Using manual NTLM flags: 0x%X\n", swap32(cflags));
        g_creds->flags = cflags;
    }

    /*
     * Last chance to get password from the user
     */
    if (interactivehash || config_vars.magic_detect || (interactivepwd && !ntlmbasic)) {
        printf("Password: ");
        struct termios termold;
        tcgetattr(0, &termold);
        struct termios termnew = termold;
        termnew.c_lflag &= ~(ISIG | ECHO);
        tcsetattr(0, TCSADRAIN, &termnew);
        fgets(config_vars.cpassword, MINIBUF_SIZE, stdin);
        tcsetattr(0, TCSADRAIN, &termold);
        size_t i = strlen(config_vars.cpassword) - 1;
        if (config_vars.cpassword[i] == '\n') {
            config_vars.cpassword[i] = 0;
            if (config_vars.cpassword[i - 1] == '\r')
                config_vars.cpassword[i - 1] = 0;
        }
        printf("\n");
    }

    /*
     * Convert optional PassNT, PassLM and PassNTLMv2 strings to hashes
     * unless plaintext pass was used, which has higher priority.
     *
     * If plain password is present, calculate its NT and LM hashes
     * and remove it from the memory.
     */
    if (!strlen(config_vars.cpassword)) {
        if (strlen(config_vars.cpassntlm2)) {
            char *tmp = scanmem(config_vars.cpassntlm2, 8);
            if (!tmp) {
                syslog(LOG_ERR, "Invalid PassNTLMv2 hash, terminating\n");
                exit(1);
            }
            AUTH_MEMCPY(g_creds, passntlm2, tmp, 16)
            free(tmp);
        }
        if (strlen(config_vars.cpassnt)) {
            char *tmp = scanmem(config_vars.cpassnt, 8);
            if (!tmp) {
                syslog(LOG_ERR, "Invalid PassNT hash, terminating\n");
                exit(1);
            }
            AUTH_MEMCPY(g_creds, passnt, tmp, 16);
            free(tmp);
        }
        if (strlen(config_vars.cpasslm)) {
            char *tmp = scanmem(config_vars.cpasslm, 8);
            if (!tmp) {
                syslog(LOG_ERR, "Invalid PassLM hash, terminating\n");
                exit(1);
            }
            AUTH_MEMCPY(g_creds, passlm, tmp, 16);
            free(tmp);
        }
    } else {
        if (g_creds->hashnt || config_vars.magic_detect || interactivehash) {
            char *tmp = ntlm_hash_nt_password(config_vars.cpassword);
            AUTH_MEMCPY(g_creds, passnt, tmp, 21);
            free(tmp);
        }
        if (g_creds->hashlm || config_vars.magic_detect || interactivehash) {
            char *tmp = ntlm_hash_lm_password(config_vars.cpassword);
            AUTH_MEMCPY(g_creds, passlm, tmp, 21);
            free(tmp);
        }
        if (g_creds->hashntlm2 || config_vars.magic_detect || interactivehash) {
            char *tmp = ntlm2_hash_password(config_vars.cuser, config_vars.cdomain, config_vars.cpassword);
            AUTH_MEMCPY(g_creds, passntlm2, tmp, 16);
            free(tmp);
        }
        memset(config_vars.cpassword, 0, strlen(config_vars.cpassword));
    }

#ifdef ENABLE_KERBEROS
    g_creds->haskrb |= check_credential();
    if(g_creds->haskrb & KRB_CREDENTIAL_AVAILABLE)
        syslog(LOG_INFO, "Using cached credential for GSS auth.\n");
#endif

    AUTH_STRCPY(g_creds, user, config_vars.cuser);
    AUTH_STRCPY(g_creds, domain, config_vars.cdomain);
    AUTH_STRCPY(g_creds, workstation, config_vars.cworkstation);

    free(config_vars.cuser);
    free(config_vars.cdomain);
    free(config_vars.cworkstation);
    free(config_vars.cpassword);
    free(config_vars.cpassntlm2);
    free(config_vars.cpassnt);
    free(config_vars.cpasslm);
    free(config_vars.cauth);

    /*
     * Try known NTLM auth combinations and print which ones work.
     * User can pick the best (most secure) one as his config.
     */
    if (config_vars.magic_detect) {
        magic_auth_detect(config_vars.magic_detect);
        goto bailout;
    }

    if (interactivehash) {
        if (!is_memory_all_zero(g_creds->passlm, ARRAY_SIZE(g_creds->passlm))) {
            char *tmp = printmem(g_creds->passlm, 16, 8);
            printf("PassLM          %s\n", tmp);
            free(tmp);
        }

        if (!is_memory_all_zero(g_creds->passnt, ARRAY_SIZE(g_creds->passnt))) {
            char *tmp = printmem(g_creds->passnt, 16, 8);
            printf("PassNT          %s\n", tmp);
            free(tmp);
        }

        if (!is_memory_all_zero(g_creds->passntlm2, ARRAY_SIZE(g_creds->passntlm2))) {
            char *tmp = printmem(g_creds->passntlm2, 16, 8);
            printf("PassNTLMv2      %s    # Only for user '%s', domain '%s'\n",
                   tmp, g_creds->user, g_creds->domain);
            free(tmp);
        }
        goto bailout;
    }

    /*
     * If we're going to need a password, check we really have it.
     */
    if (!ntlmbasic &&
        #ifdef ENABLE_KERBEROS
        !g_creds->haskrb &&
        #endif
        ((g_creds->hashnt && is_memory_all_zero(g_creds->passnt, ARRAY_SIZE(g_creds->passnt)))
         || (g_creds->hashlm && is_memory_all_zero(g_creds->passlm, ARRAY_SIZE(g_creds->passlm)))
         || (g_creds->hashntlm2 && is_memory_all_zero(g_creds->passntlm2, ARRAY_SIZE(g_creds->passntlm2))))) {
        syslog(LOG_ERR, "Parent proxy account password (or required hashes) missing.\n");
        myexit(1);
    }

    /*
     * Ok, we are ready to rock. If daemon mode was requested,
     * fork and die. The child will not be group leader anymore
     * and can thus create a new session for itself and detach
     * from the controlling terminal.
     */
    if (asdaemon) {
        init_daemon(debug);
    }

    /*
     * Reinit syslog logging to include our PID, after forking
     * it is going to be OK
     */
    if (asdaemon) {
        openlog("cntlm", LOG_CONS | LOG_PID, LOG_DAEMON);
        syslog(LOG_INFO, "Daemon ready");
    } else {
        openlog("cntlm", LOG_CONS | LOG_PID | LOG_PERROR, LOG_DAEMON);
        syslog(LOG_INFO, "Cntlm ready, staying in the foreground");
    }

    /*
     * Check and change UID.
     */

    if (strlen(config_vars.cuid)) {
        change_ids(config_vars.cuid);
    }

    /*
     * PID file requested? Try to create one (it must not exist).
     * If we fail, exit with error.
     */
    if (strlen(config_vars.cpidfile)) {
        int len;

        umask(0);
        int cd = open(config_vars.cpidfile, O_WRONLY | O_CREAT | O_TRUNC, 0644);
        if (cd < 0) {
            syslog(LOG_ERR, "Error creating a new PID file\n");
            myexit(1);
        }

        char *tmp = zmalloc(50);
        snprintf(tmp, 50, "%d\n", getpid());
        ssize_t w = write_wrapper(cd, tmp, (len = strlen(tmp)));
        if (w != len) {
            syslog(LOG_ERR, "Error writing to the PID file\n");
            myexit(1);
        }
        free(tmp);
        close(cd);
    }

    /*
     * Change the handler for signals recognized as clean shutdown.
     * When the handler is called (termination request), it signals
     * this news by adding 1 to the global quit variable.
     */
    signal(SIGPIPE, SIG_IGN);
    signal(SIGINT, &sighandler);
    signal(SIGTERM, &sighandler);
    signal(SIGHUP, &sighandler);

    /*
     * Initialize the random number generator
     */
    srandom(time(NULL));
    run_poll_loop(config_vars);

    bailout:
    if (strlen(config_vars.cpidfile))
        unlink(config_vars.cpidfile);

    clean_memory(config_vars);

    exit(0);
}

void parse_config(config_t cf, config_vars_t config_vars) {/*
 * Check if gateway mode is requested before actually binding any ports.
 */
    char *tmp = zmalloc(MINIBUF_SIZE);
    CFG_DEFAULT(cf, "Gateway", tmp, MINIBUF_SIZE);
    if (!strcasecmp("yes", tmp))
        gateway = 1;
    free(tmp);

    /*
 * Check for NTLM-to-basic settings
 */
    tmp = zmalloc(MINIBUF_SIZE);
    CFG_DEFAULT(cf, "NTLMToBasic", tmp, MINIBUF_SIZE);
    if (!strcasecmp("yes", tmp))
        ntlmbasic = 1;
    free(tmp);

    /*
 * Setup the rest of tunnels.
 */
    while ((tmp = config_pop(cf, "Tunnel"))) {
        tunnel_add(&config_vars.tunneld_list, tmp, gateway);
        free(tmp);
    }

    /*
 * Bind the rest of proxy service ports.
 */
    while ((tmp = config_pop(cf, "Listen"))) {
        listen_add("Proxy", &config_vars.proxyd_list, tmp, gateway);
        free(tmp);
    }

    /*
 * Bind the rest of SOCKS5 service ports.
 */
    while ((tmp = config_pop(cf, "SOCKS5Proxy"))) {
        listen_add("SOCKS5 proxy", &config_vars.socksd_list, tmp, gateway);
        free(tmp);
    }

    /*
 * Accept only headers not specified on the command line.
 * Command line has higher priority.
 */
    while ((tmp = config_pop(cf, "Header"))) {
        if (is_http_header(tmp)) {
            char *head = get_http_header_name(tmp);
            if (!hlist_in(header_list, head))
                header_list = hlist_add(header_list, head, get_http_header_value(tmp),
                                        HLIST_ALLOC, HLIST_NOALLOC);
            free(head);
        } else
            syslog(LOG_ERR, "Invalid header format: %s\n", tmp);

        free(tmp);
    }

#ifdef ENABLE_PACPARSER
    /*
         * Check if PAC mode is requested.
         */
        tmp = zmalloc(MINIBUF_SIZE);
        CFG_DEFAULT(cf, "Pac", tmp, MINIBUF_SIZE);
        if (!strcasecmp("yes", tmp)) {
            pac = 1;
        }
        free(tmp);

        CFG_DEFAULT(cf, "PacFile", pac_file, MINIBUF_SIZE);
#endif

    /*
 * Add the rest of parent proxies.
 */
    while ((tmp = config_pop(cf, "Proxy"))) {
        parent_add(tmp, 0);
        free(tmp);
    }


    /*
 * Single options.
 */
    CFG_DEFAULT(cf, "Auth", config_vars.cauth, MINIBUF_SIZE);
    CFG_DEFAULT(cf, "Domain", config_vars.cdomain, MINIBUF_SIZE);
    CFG_DEFAULT(cf, "Password", config_vars.cpassword, MINIBUF_SIZE);
    CFG_DEFAULT(cf, "PassNTLMv2", config_vars.cpassntlm2, MINIBUF_SIZE);
    CFG_DEFAULT(cf, "PassNT", config_vars.cpassnt, MINIBUF_SIZE);
    CFG_DEFAULT(cf, "PassLM", config_vars.cpasslm, MINIBUF_SIZE);
    CFG_DEFAULT(cf, "Username", config_vars.cuser, MINIBUF_SIZE);
    CFG_DEFAULT(cf, "Workstation", config_vars.cworkstation, MINIBUF_SIZE);

#ifdef __CYGWIN__
    /*
         * Check if SSPI is enabled and it's type.
         */
        tmp = zmalloc(MINIBUF_SIZE);
        CFG_DEFAULT(cf, "SSPI", tmp, MINIBUF_SIZE);

        if (!sspi_enabled() && strlen(tmp))
        {
            if (!strcasecmp("NTLM", tmp) && !sspi_set(tmp)) // Only NTLM supported for now
            {
                fprintf(stderr, "SSPI initialize failed! Proceeding with SSPI disabled.\n");
            }
        }
        free(tmp);

#endif

    tmp = zmalloc(MINIBUF_SIZE);
    CFG_DEFAULT(cf, "Flags", tmp, MINIBUF_SIZE);
    if (!cflags)
        cflags = swap32(strtoul(tmp, NULL, 0));
    free(tmp);

    tmp = zmalloc(MINIBUF_SIZE);
    CFG_DEFAULT(cf, "ISAScannerSize", tmp, MINIBUF_SIZE);
    if (!scanner_plugin_maxsize && strlen(tmp)) {
        scanner_plugin = 1;
        scanner_plugin_maxsize = atoi(tmp);
    }
    free(tmp);

    while ((tmp = config_pop(cf, "NoProxy"))) {
        if (strlen(tmp)) {
            noproxy_list = noproxy_add(noproxy_list, tmp);
        }
        free(tmp);
    }

    while ((tmp = config_pop(cf, "SOCKS5Users"))) {
        char *head = strchr(tmp, ':');
        if (!head) {
            syslog(LOG_ERR, "Invalid username:password format for SOCKS5User: %s\n", tmp);
        } else {
            head[0] = 0;
            users_list = hlist_add(users_list, tmp, head + 1, HLIST_ALLOC, HLIST_ALLOC);
        }
    }


    /*
 * Add User-Agent matching patterns.
 */
    while ((tmp = config_pop(cf, "ISAScannerAgent"))) {
        scanner_plugin = 1;
        if (!scanner_plugin_maxsize)
            scanner_plugin_maxsize = 1;

        size_t i;
        if ((i = strlen(tmp))) {
            char *head = zmalloc(i + 3);
            snprintf(head, i + 3, "*%s*", tmp);
            scanner_agent_list = plist_add(scanner_agent_list, 0, head);
        }
        free(tmp);
    }

    /*
 * Print out unused/unknown options.
 */
    hlist_const_t list = cf->options;
    while (list) {
        syslog(LOG_INFO, "Ignoring config file option: %s\n", list->key);
        list = list->next;
    }
}

void run_poll_loop(config_vars_t vars) {/*
 * This loop iterates over every connection request on any of
 * the listening ports. We keep the number of created threads.
 *
 * We also check the "finished threads" list, threads_list, here and
 * free the memory of all inactive threads. Then, we update the
 * number of finished threads.
 *
 * The loop ends, when we were "killed" and all threads created
 * are finished, OR if we were killed more than once. This way,
 * we have a "clean" shutdown (wait for all connections to finish
 * after the first kill) and a "forced" one (user insists and
 * killed us twice).
 */
    unsigned int tc = 0; ///< Total number of created threads
    unsigned int tj = 0; ///< Total number of joined threads
    while (quit == 0 || (tc != tj && quit < 2)) {
        struct thread_arg_s *data;
        struct sockaddr_in6 caddr;
        struct timeval tv;
        socklen_t clen;
        fd_set set;
        plist_t t;
        int tid = 0;

        FD_ZERO(&set);

        /*
         * Watch for proxy ports.
         */
        t = vars.proxyd_list;
        while (t) {
            FD_SET(t->key, &set);
            t = t->next;
        }

        /*
         * Watch for SOCKS5 ports.
         */
        t = vars.socksd_list;
        while (t) {
            FD_SET(t->key, &set);
            t = t->next;
        }

        /*
         * Watch for tunneled ports.
         */
        t = vars.tunneld_list;
        while (t) {
            FD_SET(t->key, &set);
            t = t->next;
        }

        tv.tv_sec = 1;
        tv.tv_usec = 0;

        /*
         * Wait here for data (connection request) on any of the listening
         * sockets. When ready, establish the connection. For the main
         * port, a new proxy_thread() thread is spawned to service the HTTP
         * request. For tunneled ports, tunnel_thread() thread is created
         * and for SOCKS port, socks5_thread() is created.
         *
         * All threads are defined in forward.c, except for local proxy_thread()
         * which routes the request as forwarded or direct, depending on the
         * URL host name and NoProxy settings.
         */
        int cd = select(FD_SETSIZE, &set, NULL, NULL, &tv);
        if (cd > 0) {
            for (int i = 0; i < FD_SETSIZE; ++i) {
                if (!FD_ISSET(i, &set))
                    continue;

                clen = sizeof(caddr);
                cd = accept(i, (struct sockaddr *) &caddr, (socklen_t *) &clen);

                if (cd < 0) {
                    syslog(LOG_ERR, "Serious error during accept: %s\n", strerror(errno));
                    continue;
                }

                pthread_attr_t pattr;
                pthread_attr_init(&pattr);
                pthread_attr_setstacksize(&pattr, MAX(STACK_SIZE, PTHREAD_STACK_MIN));
#ifndef __CYGWIN__
                pthread_attr_setguardsize(&pattr, 256);
#endif
                pthread_t pthread;
                if (plist_in(vars.proxyd_list, i)) {
                    data = (struct thread_arg_s *) zmalloc(sizeof(struct thread_arg_s));
                    data->fd = cd;
                    data->addr = caddr;
                    if (!serialize)
                        tid = pthread_create(&pthread, &pattr, proxy_thread, (void *) data);
                    else
                        proxy_thread((void *) data);
                } else if (plist_in(vars.socksd_list, i)) {
                    data = (struct thread_arg_s *) zmalloc(sizeof(struct thread_arg_s));
                    data->fd = cd;
                    data->addr = caddr;
                    tid = pthread_create(&pthread, &pattr, socks5_thread, (void *) data);
                } else {
                    data = (struct thread_arg_s *) zmalloc(sizeof(struct thread_arg_s));
                    data->fd = cd;
                    data->addr = caddr;
                    data->target = plist_get(vars.tunneld_list, i);
                    tid = pthread_create(&pthread, &pattr, tunnel_thread, (void *) data);
                }

                pthread_attr_destroy(&pattr);

                if (tid)
                    syslog(LOG_ERR, "Serious error during pthread_create: %d\n", tid);
                else
                    tc++;
            }
        } else if (cd < 0 && !quit)
            syslog(LOG_ERR, "Serious error during select: %s\n", strerror(errno));

        if (threads_list) {
            pthread_mutex_lock(&threads_mtx);
            t = threads_list;
            while (t) {
                plist_t tmp_next = t->next;
                int i;
                tid = pthread_join((pthread_t) t->key, (void *) &i);

                if (!tid) {
                    tj++;
                    if (debug)
                        printf("Joined thread %lu; rc: %d\n", t->key, i);
                } else
                    syslog(LOG_ERR, "Serious error during pthread_join: %d\n", tid);

                free(t);
                t = tmp_next;
            }
            threads_list = NULL;
            pthread_mutex_unlock(&threads_mtx);
        }
    }
    syslog(LOG_INFO, "Terminating with %u active threads\n", tc - tj);
}

void clean_memory(config_vars_t config_vars) {
    pthread_mutex_lock(&connection_mtx);
    plist_free(connection_list);
    pthread_mutex_unlock(&connection_mtx);

    hlist_free(header_list);
    plist_free(scanner_agent_list);
    plist_free(noproxy_list);
    plist_free(config_vars.tunneld_list);
    plist_free(config_vars.proxyd_list);
    plist_free(config_vars.socksd_list);
    plist_free(config_vars.rules);

#ifdef ENABLE_PACPARSER
    free(pac_file);
#endif

    free(config_vars.cuid);
    free(config_vars.cpidfile);
    free(config_vars.magic_detect);
    free(g_creds);

    parentlist_free(parent_list);
}

int show_help(char **argv) {
    printf("CNTLM - Accelerating NTLM Authentication Proxy version " VERSION "\n");
    printf("Copyright (c) 2oo7-2o1o David Kubicek\n\n"
           "This program comes with NO WARRANTY, to the extent permitted by law. You\n"
           "may redistribute copies of it under the terms of the GNU GPL Version 2 or\n"
           "newer. For more information about these matters, see the file LICENSE.\n"
           "For copyright holders of included encryption routines see headers.\n\n");

    FILE *stream = stdout;
    int exit_code = 0;
    if (help > 1) {
        stream = stderr;
        exit_code = 1;
    }

    fprintf(stream, "Usage: %s [-AaBcDdFfgHhILlMPpSsTUuvw] <proxy_host>[:]<proxy_port> ...\n", argv[0]);
    fprintf(stream, "\t-a  ntlm | nt | lm\n"
                    "\t    Authentication type - combined NTLM, just LM, or just NT. Default NTLM.\n"
                    #ifdef ENABLE_KERBEROS
                    "\t    GSS activates kerberos auth: you need a cached credential.\n"
                    #endif
                    "\t    It is the most versatile setting and likely to work for you.\n");
    fprintf(stream, "\t-B  Enable NTLM-to-basic authentication.\n");
    fprintf(stream, "\t-c  <config_file>\n"
                    "\t    Configuration file. Other arguments can be used as well, overriding\n"
                    "\t    config file settings.\n");
    fprintf(stream, "\t-d  <domain>\n"
                    "\t    Domain/workgroup can be set separately.\n");
    fprintf(stream, "\t-f  Run in foreground, do not fork into daemon mode.\n");
    fprintf(stream, "\t-F  <flags>\n"
                    "\t    NTLM authentication flags.\n");
    fprintf(stream, "\t-G  <pattern>\n"
                    "\t    User-Agent matching for the trans-isa-scan plugin.\n");
    fprintf(stream, "\t-g  Gateway mode - listen on all interfaces, not only loopback.\n");
    fprintf(stream, "\t-H  Print password hashes for use in config file (NTLMv2 needs -u and -d).\n");
    fprintf(stream, "\t-h  Print this help info along with version number.\n");
    fprintf(stream, "\t-I  Prompt for the password interactively.\n");
    fprintf(stream, "\t-L  [<saddr>:]<lport>:<rhost>:<rport>\n"
                    "\t    Forwarding/tunneling a la OpenSSH. Same syntax - listen on lport\n"
                    "\t    and forward all connections through the proxy to rhost:rport.\n"
                    "\t    Can be used for direct tunneling without corkscrew, etc.\n");
    fprintf(stream, "\t-l  [<saddr>:]<lport>\n"
                    "\t    Main listening port for the NTLM proxy.\n");
    fprintf(stream, "\t-M  <testurl>\n"
                    "\t    Magic autodetection of proxy's NTLM dialect.\n");
    fprintf(stream, "\t-N  \"<hostname_wildcard1>[, <hostname_wildcardN>\"\n"
                    "\t    List of URL's to serve directly as stand-alone proxy (e.g. '*.local')\n");
    fprintf(stream, "\t-O  [<saddr>:]<lport>\n"
                    "\t    Enable SOCKS5 proxy on port lport (binding to address saddr)\n");
    fprintf(stream, "\t-P  <pidfile>\n"
                    "\t    Create a PID file upon successful start.\n");
    fprintf(stream, "\t-p  <password>\n"
                    "\t    Account password. Will not be visible in \"ps\", /proc, etc.\n");
    fprintf(stream, "\t-q  <level>\n"
                    "\t    Controls logging of requests like CONNECT/GET with URL.\n"
                    "\t    level can be:\n"
                    "\t    0 no requests are logged - default\n"
                    "\t    1 requests are logged (old behavior)\n");
    fprintf(stream, "\t-r  \"HeaderName: value\"\n"
                    "\t    Add a header substitution. All such headers will be added/replaced\n"
                    "\t    in the client's requests.\n");
    fprintf(stream, "\t-S  <size_in_kb>\n"
                    "\t    Enable automation of GFI WebMonitor ISA scanner for files < size_in_kb.\n");
    fprintf(stream, "\t-s  Do not use threads, serialize all requests - for debugging only.\n");
    fprintf(stream, "\t-T  <file.log>\n"
                    "\t    Redirect all debug information into a trace file for support upload.\n"
                    "\t    MUST be the first argument on the command line, implies -v.\n");
    fprintf(stream, "\t-U  <uid>\n"
                    "\t    Run as uid. It is an important security measure not to run as root.\n");
    fprintf(stream, "\t-u  <user>[@<domain]\n"
                    "\t    Domain/workgroup can be set separately.\n");
    fprintf(stream, "\t-v  Print debugging information.\n");
    fprintf(stream, "\t-w  <workstation>\n"
                    "\t    Some proxies require correct NetBIOS hostname.\n");
#ifdef ENABLE_PACPARSER
    fprintf(stream, "\t-x  <PAC_file>\n"
    "\t    Specify a PAC file to load.\n");
#endif
    fprintf(stream, "\t-X  <sspi_handle_type>\n"
                    "\t    Use SSPI with specified handle type. Works only under Windows.\n"
                    "\t    Default is negotiate.\n");
    fprintf(stream, "\n");
    return exit_code;
}

void parse_option(int opt, config_vars_t config_vars) {
    switch (opt) {
        char *tmp;
        case 'a':
            strlcpy(config_vars.cauth, optarg, MINIBUF_SIZE);
            break;
        case 'B':
            ntlmbasic = 1;
            break;
        case 'c':
            config_vars.myconfig = strdup(optarg);
            break;
        case 'd':
            strlcpy(config_vars.cdomain, optarg, MINIBUF_SIZE);
            break;
        case 'x':
#ifdef ENABLE_PACPARSER
            pac = 1;
            /*
             * Resolve relative paths if necessary.
             * Don't care if the named file does not exist (ENOENT) because
             * later on we check the file's availability anyway.
             */
            if (!realpath(optarg, pac_file) && errno != ENOENT) {
                syslog(LOG_ERR, "Resolving path to PAC file failed: %s\n", strerror(errno));
                myexit(1);
            }
#else
            fprintf(stderr, "-x specified but CNTLM was compiled without PAC support\n");
#endif
            break;
        case 'F':
            cflags = swap32(strtoul(optarg, NULL, 0));
            break;
        case 'f':
            asdaemon = 0;
            break;
        case 'G':
            if (strlen(optarg)) {
                scanner_plugin = 1;
                if (!scanner_plugin_maxsize)
                    scanner_plugin_maxsize = 1;
                int i = strlen(optarg) + 3;
                tmp = zmalloc(i);
                snprintf(tmp, i, "*%s*", optarg);
                scanner_agent_list = plist_add(scanner_agent_list, 0, tmp);
            }
            break;
        case 'g':
            gateway = 1;
            break;
        case 'H':
            interactivehash = 1;
            break;
        case 'I':
            interactivepwd = 1;
            break;
        case 'L':
            /*
             * Parse and validate the argument.
             * Create a listening socket for tunneling.
             */
            tunnel_add(&config_vars.tunneld_list, optarg, gateway);
            break;
        case 'l':
            /*
             * Create a listening socket for proxy function.
             */
            listen_add("Proxy", &config_vars.proxyd_list, optarg, gateway);
            break;
        case 'M':
            config_vars.magic_detect = strdup(optarg);
            break;
        case 'N':
            noproxy_list = noproxy_add(noproxy_list, tmp = strdup(optarg));
            free(tmp);
            break;
        case 'O':
            listen_add("SOCKS5 proxy", &config_vars.socksd_list, optarg, gateway);
            break;
        case 'P':
            strlcpy(config_vars.cpidfile, optarg, MINIBUF_SIZE);
            break;
        case 'p':
            /*
             * Overwrite the password parameter with '*'s to make it
             * invisible in "ps", /proc, etc.
             */
            strlcpy(config_vars.cpassword, optarg, MINIBUF_SIZE);
            for (int i = strlen(optarg) - 1; i >= 0; --i)
                optarg[i] = '*';
            break;
        case 'R':
            tmp = strdup(optarg);
            char *head = strchr(tmp, ':');
            if (!head) {
                fprintf(stderr, "Invalid username:password format for -R: %s\n", tmp);
            } else {
                head[0] = 0;
                users_list = hlist_add(users_list, tmp, head + 1,
                                       HLIST_ALLOC, HLIST_ALLOC);
            }
            break;
        case 'r':
            if (is_http_header(optarg))
                header_list = hlist_add(header_list,
                                        get_http_header_name(optarg),
                                        get_http_header_value(optarg),
                                        HLIST_NOALLOC, HLIST_NOALLOC);
            break;
        case 'S':
            scanner_plugin = 1;
            scanner_plugin_maxsize = atol(optarg);
            break;
        case 's':
            /*
             * Do not use threads - for debugging purposes only
             */
            serialize = 1;
            break;
        case 'T':
            debug = 1;
            asdaemon = 0;
            tracefile = open(optarg, O_CREAT | O_TRUNC | O_WRONLY, 0600);
            openlog("cntlm", LOG_CONS | LOG_PERROR, LOG_DAEMON);
            if (tracefile < 0) {
                fprintf(stderr, "Cannot create trace file.\n");
                myexit(1);
            } else {
                printf("Redirecting all output to %s\n", optarg);
                dup2(tracefile, 1);
                dup2(tracefile, 2);
            }
            break;
        case 'U':
            strlcpy(config_vars.cuid, optarg, MINIBUF_SIZE);
            break;
        case 'u': {
            int i;
            i = strcspn(optarg, "@");
            if (i != strlen(optarg)) {
                strlcpy(config_vars.cuser, optarg, MIN(MINIBUF_SIZE, i + 1));
                strlcpy(config_vars.cdomain, optarg + i + 1, MINIBUF_SIZE);
            } else {
                strlcpy(config_vars.cuser, optarg, MINIBUF_SIZE);
            }
            break;
        }
        case 'v':
            debug = 1;
            asdaemon = 0;
            openlog("cntlm", LOG_CONS | LOG_PERROR, LOG_DAEMON);
            break;
        case 'w':
            strlcpy(config_vars.cworkstation, optarg, MINIBUF_SIZE);
            break;
        case 'X':
#ifdef __CYGWIN__
            if (!sspi_set(strdup(optarg)))
            {
                fprintf(stderr, "SSPI initialize failed! Proceeding with SSPI disabled.\n");
            }
#else
            fprintf(stderr, "This feature is available under Windows only!\n");
            help = 1;
#endif
            break;
        case 'q':
            if (*optarg == '0') {
                request_logging_level = 0;
            } else if (*optarg == '1') {
                request_logging_level = 1;
            } else {
                fprintf(stderr, "Invalid argument for option -q, using default value of %d.\n",
                        request_logging_level);
            }
            break;
        case 'h':
            help = 1;
            break;
        default:
            help = 2;
    }
}

