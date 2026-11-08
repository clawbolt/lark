// lterm run 用到的几个 C 函数：开一个伪终端（pty）在里面跑 shell、同时等两个文件描述符、改伪终端的大小、看 shell 退出了没有。
// 只用 POSIX 的函数（posix_openpt、grantpt、unlockpt、ptsname、fork、poll），macOS 和 Linux 都不用多链接库。
#define _XOPEN_SOURCE 600
#define _DEFAULT_SOURCE
#define _DARWIN_C_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/wait.h>
#include <termios.h>
#include <unistd.h>

static pid_t lterm_pid = -1;

// 开伪终端、fork 出子进程跑 cmd（空串时跑 $SHELL）；返回主端的文件描述符，失败时返回 -errno
int lterm_spawn(const char* cmd, int rows, int cols) {
  int m = posix_openpt(O_RDWR | O_NOCTTY);
  if (m < 0) return -errno;
  if (grantpt(m) < 0 || unlockpt(m) < 0) {
    int e = errno;
    close(m);
    return -e;
  }
  const char* name = ptsname(m);
  if (name == NULL) {
    int e = errno;
    close(m);
    return -e;
  }
  char path[256];
  strncpy(path, name, sizeof path - 1);
  path[sizeof path - 1] = 0;
  struct winsize ws;
  memset(&ws, 0, sizeof ws);
  ws.ws_row = (unsigned short)rows;
  ws.ws_col = (unsigned short)cols;
  // 子进程里只调用 exec 之前安全的函数，所以环境变量在 fork 之前设好
  setenv("TERM", "xterm-256color", 1);
  const char* sh = getenv("SHELL");
  if (sh == NULL || sh[0] == 0) sh = "/bin/sh";
  pid_t p = fork();
  if (p < 0) {
    int e = errno;
    close(m);
    return -e;
  }
  if (p == 0) {
    setsid();
    int s = open(path, O_RDWR);
    if (s < 0) _exit(127);
#ifdef TIOCSCTTY
    ioctl(s, TIOCSCTTY, 0);
#endif
    ioctl(s, TIOCSWINSZ, &ws);
    dup2(s, 0);
    dup2(s, 1);
    dup2(s, 2);
    if (s > 2) close(s);
    close(m);
    // 父进程（Lark 的运行时）可能改过信号的处理和屏蔽，shell 要从默认的开始
    int sigs[] = {SIGINT, SIGQUIT, SIGTSTP, SIGTTIN, SIGTTOU, SIGCHLD, SIGPIPE, SIGWINCH, SIGHUP, SIGTERM};
    for (size_t i = 0; i < sizeof sigs / sizeof sigs[0]; i++) signal(sigs[i], SIG_DFL);
    sigset_t none;
    sigemptyset(&none);
    sigprocmask(SIG_SETMASK, &none, NULL);
    if (cmd != NULL && cmd[0] != 0) execl("/bin/sh", "sh", "-c", cmd, (char*)NULL);
    else execl(sh, sh, (char*)NULL);
    _exit(127);
  }
  ioctl(m, TIOCSWINSZ, &ws);
  lterm_pid = p;
  return m;
}

// 改伪终端的大小（shell 会收到 SIGWINCH）；返回 0 或 errno
int lterm_resize(int fd, int rows, int cols) {
  struct winsize ws;
  memset(&ws, 0, sizeof ws);
  ws.ws_row = (unsigned short)rows;
  ws.ws_col = (unsigned short)cols;
  return ioctl(fd, TIOCSWINSZ, &ws) < 0 ? errno : 0;
}

// 等 a、b 两个文件描述符最多 ms 毫秒：返回值的第 1 位是 a 能读了，第 2 位是 b 能读了（或者断开了）；
// 等到时间（或者被信号打断）是 0，出错是 -errno
int lterm_poll(int a, int b, int ms) {
  struct pollfd fs[2];
  fs[0].fd = a;
  fs[0].events = POLLIN;
  fs[0].revents = 0;
  fs[1].fd = b;
  fs[1].events = POLLIN;
  fs[1].revents = 0;
  int n = poll(fs, 2, ms);
  if (n < 0) return errno == EINTR ? 0 : -errno;
  int r = 0;
  if (fs[0].revents & (POLLIN | POLLHUP | POLLERR)) r |= 1;
  if (fs[1].revents & (POLLIN | POLLHUP | POLLERR)) r |= 2;
  return r;
}

// shell 退出了没有（退出了就收掉它）：1 是退出了
int lterm_exited(void) {
  if (lterm_pid < 0) return 1;
  int st = 0;
  pid_t r = waitpid(lterm_pid, &st, WNOHANG);
  if (r == lterm_pid || (r < 0 && errno == ECHILD)) {
    lterm_pid = -1;
    return 1;
  }
  return 0;
}
