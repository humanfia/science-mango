#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <sys/types.h>
#include <arpa/inet.h>
#include <unistd.h>
#include <sys/syscall.h>

static int write_path(const char *path) {
    int fd = open(path, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, 0600);
    if (fd < 0) return 20;
    if (write(fd, "ok\n", 3) != 3) return 21;
    if (fsync(fd) != 0) return 22;
    return close(fd) == 0 ? 0 : 23;
}

int main(int argc, char **argv) {
    if (argc < 2) return 2;
    if (strcmp(argv[1], "write") == 0 && argc == 3) return write_path(argv[2]);
    if (strcmp(argv[1], "double-fork") == 0) {
        pid_t first = fork();
        if (first < 0) return 30;
        if (first > 0) return 0;
        if (setsid() < 0) _exit(31);
        pid_t second = fork();
        if (second < 0) _exit(32);
        if (second > 0) _exit(0);
        for (;;) pause();
    }
    if (strcmp(argv[1], "tcp") == 0 && argc == 3) {
        int fd = socket(AF_INET, SOCK_STREAM, 0);
        if (fd < 0) return 40;
        struct sockaddr_in address = {0};
        address.sin_family = AF_INET;
        address.sin_port = htons((unsigned short)atoi(argv[2]));
        address.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
        return connect(fd, (struct sockaddr *)&address, sizeof(address)) == 0 ? 0 : 41;
    }
    if (strcmp(argv[1], "udp") == 0) {
        int fd = socket(AF_INET, SOCK_DGRAM, 0);
        return fd < 0 && errno == EPERM ? 0 : 42;
    }
    if (strcmp(argv[1], "mptcp") == 0) {
        int fd = socket(AF_INET, SOCK_STREAM, 262);
        return fd < 0 && errno == EPERM ? 0 : 43;
    }
    if (strcmp(argv[1], "io-uring") == 0) {
        long result = syscall(425, 1, NULL);
        return result < 0 && errno == EPERM ? 0 : 44;
    }
    if (strcmp(argv[1], "unix-path") == 0 && argc == 3) {
        int fd = socket(AF_UNIX, SOCK_STREAM, 0);
        if (fd < 0) return errno == EPERM ? 0 : 45;
        struct sockaddr_un address = {0};
        address.sun_family = AF_UNIX;
        if (strlen(argv[2]) >= sizeof(address.sun_path)) return 46;
        strcpy(address.sun_path, argv[2]);
        return connect(fd, (struct sockaddr *)&address, sizeof(address)) == 0 ? 47 : 48;
    }
    if (strcmp(argv[1], "unix-abstract") == 0 && argc == 3) {
        int fd = socket(AF_UNIX, SOCK_STREAM, 0);
        if (fd < 0) return errno == EPERM ? 0 : 49;
        struct sockaddr_un address = {0};
        address.sun_family = AF_UNIX;
        size_t length = strlen(argv[2]);
        if (length + 1 >= sizeof(address.sun_path)) return 50;
        address.sun_path[0] = '\0';
        memcpy(address.sun_path + 1, argv[2], length);
        socklen_t size = (socklen_t)(sizeof(address.sun_family) + 1 + length);
        return connect(fd, (struct sockaddr *)&address, size) == 0 ? 51 : 52;
    }
    if (strcmp(argv[1], "socketpair") == 0) {
        int descriptors[2];
        int result = socketpair(AF_UNIX, SOCK_STREAM, 0, descriptors);
        return result < 0 && errno == EPERM ? 0 : 53;
    }
    return 3;
}
