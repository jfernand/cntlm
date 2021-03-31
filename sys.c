#include "utils.h"
#include <termios.h>
#include <syslog.h>
#include <fcntl.h>
#include <pwd.h>
#include <ctype.h>
#include <strings.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <errno.h>
#include <stdio.h>
#include <sys/stat.h>
#include "sys.h"

void init_daemon(int debug) {
    if (debug)
        printf("Forking into background as requested.\n");

    pid_t i = fork();
    if (i == -1) {
        perror("Fork into background failed");        /* fork failed */
        myexit(1);
    } else if (i)
        myexit(0);                    /* parent */

    setsid();
    umask(0);
    int w = chdir("/");
    if (w != 0) {
        perror("chdir(\"/\") failed");
    }
    i = open("/dev/null", O_RDWR);
    if (i >= 0) {
        dup2(i, 0);
        dup2(i, 1);
        dup2(i, 2);
        if (i > 2)
            close(i);
    }
}

void change_ids(char * cuid) {
    int new_uid;
    int new_gid;
    if (getuid() && geteuid()) {
        syslog(LOG_WARNING, "No root privileges; keeping identity %d:%d\n", getuid(), getgid());
    } else {
        if (isdigit(cuid[0])) {
            new_uid = atoi(cuid);
            new_gid = new_uid;
            if (new_uid <= 0) {
                syslog(LOG_ERR, "Numerical uid parameter invalid\n");
                myexit(1);
            }
        } else {
            const struct passwd *const pw = getpwnam(cuid);
            if (!pw || !pw->pw_uid) {
                syslog(LOG_ERR, "Username %s in -U is invalid\n", cuid);
                myexit(1);
            }
            new_uid = pw->pw_uid;
            new_gid = pw->pw_gid;
        }
        if (setgid(new_gid)) {
            syslog(LOG_ERR, "Setting group identity failed: %s\n", strerror(errno));
            syslog(LOG_ERR, "Terminating\n");
            myexit(1);
        }
        int i = setuid(new_uid);
        syslog(LOG_INFO, "Changing uid:gid to %d:%d - %s\n", new_uid, new_gid, strerror(errno));
        if (i) {
            syslog(LOG_ERR, "Terminating\n");
            myexit(1);
        }
    }
}
