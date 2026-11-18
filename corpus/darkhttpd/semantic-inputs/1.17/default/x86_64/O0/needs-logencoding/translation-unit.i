static const char
    pkgname[] = "darkhttpd/1.17",
    copyright[] = "copyright (c) 2003-2025 Emil Mikulic";
static const int debug = 0;

typedef unsigned char __u_char;
typedef unsigned short int __u_short;
typedef unsigned int __u_int;
typedef unsigned long int __u_long;
typedef signed char __int8_t;
typedef unsigned char __uint8_t;
typedef signed short int __int16_t;
typedef unsigned short int __uint16_t;
typedef signed int __int32_t;
typedef unsigned int __uint32_t;
typedef signed long int __int64_t;
typedef unsigned long int __uint64_t;
typedef __int8_t __int_least8_t;
typedef __uint8_t __uint_least8_t;
typedef __int16_t __int_least16_t;
typedef __uint16_t __uint_least16_t;
typedef __int32_t __int_least32_t;
typedef __uint32_t __uint_least32_t;
typedef __int64_t __int_least64_t;
typedef __uint64_t __uint_least64_t;
typedef long int __quad_t;
typedef unsigned long int __u_quad_t;
typedef long int __intmax_t;
typedef unsigned long int __uintmax_t;
typedef unsigned long int __dev_t;
typedef unsigned int __uid_t;
typedef unsigned int __gid_t;
typedef unsigned long int __ino_t;
typedef unsigned long int __ino64_t;
typedef unsigned int __mode_t;
typedef unsigned long int __nlink_t;
typedef long int __off_t;
typedef long int __off64_t;
typedef int __pid_t;
typedef struct { int __val[2]; } __fsid_t;
typedef long int __clock_t;
typedef unsigned long int __rlim_t;
typedef unsigned long int __rlim64_t;
typedef unsigned int __id_t;
typedef long int __time_t;
typedef unsigned int __useconds_t;
typedef long int __suseconds_t;
typedef long int __suseconds64_t;
typedef int __daddr_t;
typedef int __key_t;
typedef int __clockid_t;
typedef void * __timer_t;
typedef long int __blksize_t;
typedef long int __blkcnt_t;
typedef long int __blkcnt64_t;
typedef unsigned long int __fsblkcnt_t;
typedef unsigned long int __fsblkcnt64_t;
typedef unsigned long int __fsfilcnt_t;
typedef unsigned long int __fsfilcnt64_t;
typedef long int __fsword_t;
typedef long int __ssize_t;
typedef long int __syscall_slong_t;
typedef unsigned long int __syscall_ulong_t;
typedef __off64_t __loff_t;
typedef char *__caddr_t;
typedef long int __intptr_t;
typedef unsigned int __socklen_t;
typedef int __sig_atomic_t;
typedef __u_char u_char;
typedef __u_short u_short;
typedef __u_int u_int;
typedef __u_long u_long;
typedef __quad_t quad_t;
typedef __u_quad_t u_quad_t;
typedef __fsid_t fsid_t;
typedef __loff_t loff_t;
typedef __ino64_t ino_t;
typedef __ino64_t ino64_t;
typedef __dev_t dev_t;
typedef __gid_t gid_t;
typedef __mode_t mode_t;
typedef __nlink_t nlink_t;
typedef __uid_t uid_t;
typedef __off64_t off_t;
typedef __off64_t off64_t;
typedef __pid_t pid_t;
typedef __id_t id_t;
typedef __ssize_t ssize_t;
typedef __daddr_t daddr_t;
typedef __caddr_t caddr_t;
typedef __key_t key_t;
typedef __clock_t clock_t;
typedef __clockid_t clockid_t;
typedef __time_t time_t;
typedef __timer_t timer_t;
typedef __useconds_t useconds_t;
typedef __suseconds_t suseconds_t;
typedef long unsigned int size_t;
typedef unsigned long int ulong;
typedef unsigned short int ushort;
typedef unsigned int uint;
typedef __int8_t int8_t;
typedef __int16_t int16_t;
typedef __int32_t int32_t;
typedef __int64_t int64_t;
typedef __uint8_t u_int8_t;
typedef __uint16_t u_int16_t;
typedef __uint32_t u_int32_t;
typedef __uint64_t u_int64_t;
typedef int register_t __attribute__ ((__mode__ (__word__)));
static __inline __uint16_t
__bswap_16 (__uint16_t __bsx)
{
  return __builtin_bswap16 (__bsx);
}
static __inline __uint32_t
__bswap_32 (__uint32_t __bsx)
{
  return __builtin_bswap32 (__bsx);
}
__extension__ static __inline __uint64_t
__bswap_64 (__uint64_t __bsx)
{
  return __builtin_bswap64 (__bsx);
}
static __inline __uint16_t
__uint16_identity (__uint16_t __x)
{
  return __x;
}
static __inline __uint32_t
__uint32_identity (__uint32_t __x)
{
  return __x;
}
static __inline __uint64_t
__uint64_identity (__uint64_t __x)
{
  return __x;
}
typedef struct
{
  unsigned long int __val[(1024 / (8 * sizeof (unsigned long int)))];
} __sigset_t;
typedef __sigset_t sigset_t;
struct timeval
{
  __time_t tv_sec;
  __suseconds_t tv_usec;
};
struct timespec
{
  __time_t tv_sec;
  __syscall_slong_t tv_nsec;
};
typedef long int __fd_mask;
typedef struct
  {
    __fd_mask fds_bits[1024 / (8 * (int) sizeof (__fd_mask))];
  } fd_set;
typedef __fd_mask fd_mask;

extern int select (int __nfds, fd_set *__restrict __readfds,
     fd_set *__restrict __writefds,
     fd_set *__restrict __exceptfds,
     struct timeval *__restrict __timeout);
extern int pselect (int __nfds, fd_set *__restrict __readfds,
      fd_set *__restrict __writefds,
      fd_set *__restrict __exceptfds,
      const struct timespec *__restrict __timeout,
      const __sigset_t *__restrict __sigmask);

typedef __blksize_t blksize_t;
typedef __blkcnt64_t blkcnt_t;
typedef __fsblkcnt64_t fsblkcnt_t;
typedef __fsfilcnt64_t fsfilcnt_t;
typedef __blkcnt64_t blkcnt64_t;
typedef __fsblkcnt64_t fsblkcnt64_t;
typedef __fsfilcnt64_t fsfilcnt64_t;
typedef union
{
  __extension__ unsigned long long int __value64;
  struct
  {
    unsigned int __low;
    unsigned int __high;
  } __value32;
} __atomic_wide_counter;
typedef struct __pthread_internal_list
{
  struct __pthread_internal_list *__prev;
  struct __pthread_internal_list *__next;
} __pthread_list_t;
typedef struct __pthread_internal_slist
{
  struct __pthread_internal_slist *__next;
} __pthread_slist_t;
struct __pthread_mutex_s
{
  int __lock;
  unsigned int __count;
  int __owner;
  unsigned int __nusers;
  int __kind;
  short __spins;
  short __elision;
  __pthread_list_t __list;
};
struct __pthread_rwlock_arch_t
{
  unsigned int __readers;
  unsigned int __writers;
  unsigned int __wrphase_futex;
  unsigned int __writers_futex;
  unsigned int __pad3;
  unsigned int __pad4;
  int __cur_writer;
  int __shared;
  signed char __rwelision;
  unsigned char __pad1[7];
  unsigned long int __pad2;
  unsigned int __flags;
};
struct __pthread_cond_s
{
  __atomic_wide_counter __wseq;
  __atomic_wide_counter __g1_start;
  unsigned int __g_size[2] ;
  unsigned int __g1_orig_size;
  unsigned int __wrefs;
  unsigned int __g_signals[2];
  unsigned int __unused_initialized_1;
  unsigned int __unused_initialized_2;
};
typedef unsigned int __tss_t;
typedef unsigned long int __thrd_t;
typedef struct
{
  int __data ;
} __once_flag;
typedef unsigned long int pthread_t;
typedef union
{
  char __size[4];
  int __align;
} pthread_mutexattr_t;
typedef union
{
  char __size[4];
  int __align;
} pthread_condattr_t;
typedef unsigned int pthread_key_t;
typedef int pthread_once_t;
union pthread_attr_t
{
  char __size[56];
  long int __align;
};
typedef union pthread_attr_t pthread_attr_t;
typedef union
{
  struct __pthread_mutex_s __data;
  char __size[40];
  long int __align;
} pthread_mutex_t;
typedef union
{
  struct __pthread_cond_s __data;
  char __size[48];
  __extension__ long long int __align;
} pthread_cond_t;
typedef union
{
  struct __pthread_rwlock_arch_t __data;
  char __size[56];
  long int __align;
} pthread_rwlock_t;
typedef union
{
  char __size[8];
  long int __align;
} pthread_rwlockattr_t;
typedef volatile int pthread_spinlock_t;
typedef union
{
  char __size[32];
  long int __align;
} pthread_barrier_t;
typedef union
{
  char __size[4];
  int __align;
} pthread_barrierattr_t;


extern ssize_t sendfile (int __out_fd, int __in_fd, __off64_t *__offset, size_t __count) __asm__ ("" "sendfile64") __attribute__ ((__nothrow__ , __leaf__));
extern ssize_t sendfile64 (int __out_fd, int __in_fd, __off64_t *__offset,
      size_t __count) __attribute__ ((__nothrow__ , __leaf__));


struct timezone
  {
    int tz_minuteswest;
    int tz_dsttime;
  };
extern int gettimeofday (struct timeval *__restrict __tv,
    void *__restrict __tz) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int settimeofday (const struct timeval *__tv,
    const struct timezone *__tz)
     __attribute__ ((__nothrow__ , __leaf__));
extern int adjtime (const struct timeval *__delta,
      struct timeval *__olddelta) __attribute__ ((__nothrow__ , __leaf__));
enum __itimer_which
  {
    ITIMER_REAL = 0,
    ITIMER_VIRTUAL = 1,
    ITIMER_PROF = 2
  };
struct itimerval
  {
    struct timeval it_interval;
    struct timeval it_value;
  };
typedef enum __itimer_which __itimer_which_t;
extern int getitimer (__itimer_which_t __which,
        struct itimerval *__value) __attribute__ ((__nothrow__ , __leaf__));
extern int setitimer (__itimer_which_t __which,
        const struct itimerval *__restrict __new,
        struct itimerval *__restrict __old) __attribute__ ((__nothrow__ , __leaf__));
extern int utimes (const char *__file, const struct timeval __tvp[2])
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int lutimes (const char *__file, const struct timeval __tvp[2])
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int futimes (int __fd, const struct timeval __tvp[2]) __attribute__ ((__nothrow__ , __leaf__));
extern int futimesat (int __fd, const char *__file,
        const struct timeval __tvp[2]) __attribute__ ((__nothrow__ , __leaf__));


struct iovec
  {
    void *iov_base;
    size_t iov_len;
  };
typedef __socklen_t socklen_t;
enum __socket_type
{
  SOCK_STREAM = 1,
  SOCK_DGRAM = 2,
  SOCK_RAW = 3,
  SOCK_RDM = 4,
  SOCK_SEQPACKET = 5,
  SOCK_DCCP = 6,
  SOCK_PACKET = 10,
  SOCK_CLOEXEC = 02000000,
  SOCK_NONBLOCK = 00004000
};
typedef unsigned short int sa_family_t;
struct __attribute__ ((__may_alias__)) sockaddr
  {
    sa_family_t sa_family;
    char sa_data[14];
  };
struct __attribute__ ((__may_alias__)) sockaddr_storage
  {
    sa_family_t ss_family;
    char __ss_padding[(128 - (sizeof (unsigned short int)) - sizeof (unsigned long int))];
    unsigned long int __ss_align;
  };
enum
  {
    MSG_OOB = 0x01,
    MSG_PEEK = 0x02,
    MSG_DONTROUTE = 0x04,
    MSG_TRYHARD = MSG_DONTROUTE,
    MSG_CTRUNC = 0x08,
    MSG_PROXY = 0x10,
    MSG_TRUNC = 0x20,
    MSG_DONTWAIT = 0x40,
    MSG_EOR = 0x80,
    MSG_WAITALL = 0x100,
    MSG_FIN = 0x200,
    MSG_SYN = 0x400,
    MSG_CONFIRM = 0x800,
    MSG_RST = 0x1000,
    MSG_ERRQUEUE = 0x2000,
    MSG_NOSIGNAL = 0x4000,
    MSG_MORE = 0x8000,
    MSG_WAITFORONE = 0x10000,
    MSG_BATCH = 0x40000,
    MSG_SOCK_DEVMEM = 0x2000000,
    MSG_ZEROCOPY = 0x4000000,
    MSG_FASTOPEN = 0x20000000,
    MSG_CMSG_CLOEXEC = 0x40000000
  };
struct msghdr
  {
    void *msg_name;
    socklen_t msg_namelen;
    struct iovec *msg_iov;
    size_t msg_iovlen;
    void *msg_control;
    size_t msg_controllen;
    int msg_flags;
  };
struct cmsghdr
  {
    size_t cmsg_len;
    int cmsg_level;
    int cmsg_type;
    __extension__ unsigned char __cmsg_data [];
  };
extern struct cmsghdr *__cmsg_nxthdr (struct msghdr *__mhdr,
          struct cmsghdr *__cmsg) __attribute__ ((__nothrow__ , __leaf__));
enum
  {
    SCM_RIGHTS = 0x01
    , SCM_CREDENTIALS = 0x02
    , SCM_SECURITY = 0x03
    , SCM_PIDFD = 0x04
  };
struct ucred
{
  pid_t pid;
  uid_t uid;
  gid_t gid;
};
typedef struct {
 unsigned long fds_bits[1024 / (8 * sizeof(long))];
} __kernel_fd_set;
typedef void (*__kernel_sighandler_t)(int);
typedef int __kernel_key_t;
typedef int __kernel_mqd_t;
typedef unsigned short __kernel_old_uid_t;
typedef unsigned short __kernel_old_gid_t;
typedef unsigned long __kernel_old_dev_t;
typedef long __kernel_long_t;
typedef unsigned long __kernel_ulong_t;
typedef __kernel_ulong_t __kernel_ino_t;
typedef unsigned int __kernel_mode_t;
typedef int __kernel_pid_t;
typedef int __kernel_ipc_pid_t;
typedef unsigned int __kernel_uid_t;
typedef unsigned int __kernel_gid_t;
typedef __kernel_long_t __kernel_suseconds_t;
typedef int __kernel_daddr_t;
typedef unsigned int __kernel_uid32_t;
typedef unsigned int __kernel_gid32_t;
typedef __kernel_ulong_t __kernel_size_t;
typedef __kernel_long_t __kernel_ssize_t;
typedef __kernel_long_t __kernel_ptrdiff_t;
typedef struct {
 int val[2];
} __kernel_fsid_t;
typedef __kernel_long_t __kernel_off_t;
typedef long long __kernel_loff_t;
typedef __kernel_long_t __kernel_old_time_t;
typedef __kernel_long_t __kernel_time_t;
typedef long long __kernel_time64_t;
typedef __kernel_long_t __kernel_clock_t;
typedef int __kernel_timer_t;
typedef int __kernel_clockid_t;
typedef char * __kernel_caddr_t;
typedef unsigned short __kernel_uid16_t;
typedef unsigned short __kernel_gid16_t;
struct linger
  {
    int l_onoff;
    int l_linger;
  };
struct osockaddr
{
  unsigned short int sa_family;
  unsigned char sa_data[14];
};
enum
{
  SHUT_RD = 0,
  SHUT_WR,
  SHUT_RDWR
};
typedef union { struct sockaddr *__restrict __sockaddr__; struct sockaddr_at *__restrict __sockaddr_at__; struct sockaddr_ax25 *__restrict __sockaddr_ax25__; struct sockaddr_dl *__restrict __sockaddr_dl__; struct sockaddr_eon *__restrict __sockaddr_eon__; struct sockaddr_in *__restrict __sockaddr_in__; struct sockaddr_in6 *__restrict __sockaddr_in6__; struct sockaddr_inarp *__restrict __sockaddr_inarp__; struct sockaddr_ipx *__restrict __sockaddr_ipx__; struct sockaddr_iso *__restrict __sockaddr_iso__; struct sockaddr_ns *__restrict __sockaddr_ns__; struct sockaddr_un *__restrict __sockaddr_un__; struct sockaddr_x25 *__restrict __sockaddr_x25__;
       } __SOCKADDR_ARG __attribute__ ((__transparent_union__));
typedef union { const struct sockaddr *__restrict __sockaddr__; const struct sockaddr_at *__restrict __sockaddr_at__; const struct sockaddr_ax25 *__restrict __sockaddr_ax25__; const struct sockaddr_dl *__restrict __sockaddr_dl__; const struct sockaddr_eon *__restrict __sockaddr_eon__; const struct sockaddr_in *__restrict __sockaddr_in__; const struct sockaddr_in6 *__restrict __sockaddr_in6__; const struct sockaddr_inarp *__restrict __sockaddr_inarp__; const struct sockaddr_ipx *__restrict __sockaddr_ipx__; const struct sockaddr_iso *__restrict __sockaddr_iso__; const struct sockaddr_ns *__restrict __sockaddr_ns__; const struct sockaddr_un *__restrict __sockaddr_un__; const struct sockaddr_x25 *__restrict __sockaddr_x25__;
       } __CONST_SOCKADDR_ARG __attribute__ ((__transparent_union__));
struct mmsghdr
  {
    struct msghdr msg_hdr;
    unsigned int msg_len;
  };
extern int socket (int __domain, int __type, int __protocol) __attribute__ ((__nothrow__ , __leaf__));
extern int socketpair (int __domain, int __type, int __protocol,
         int __fds[2]) __attribute__ ((__nothrow__ , __leaf__));
extern int bind (int __fd, __CONST_SOCKADDR_ARG __addr, socklen_t __len)
     __attribute__ ((__nothrow__ , __leaf__));
extern int getsockname (int __fd, __SOCKADDR_ARG __addr,
   socklen_t *__restrict __len) __attribute__ ((__nothrow__ , __leaf__));
extern int connect (int __fd, __CONST_SOCKADDR_ARG __addr, socklen_t __len);
extern int getpeername (int __fd, __SOCKADDR_ARG __addr,
   socklen_t *__restrict __len) __attribute__ ((__nothrow__ , __leaf__));
extern ssize_t send (int __fd, const void *__buf, size_t __n, int __flags);
extern ssize_t recv (int __fd, void *__buf, size_t __n, int __flags);
extern ssize_t sendto (int __fd, const void *__buf, size_t __n,
         int __flags, __CONST_SOCKADDR_ARG __addr,
         socklen_t __addr_len);
extern ssize_t recvfrom (int __fd, void *__restrict __buf, size_t __n,
    int __flags, __SOCKADDR_ARG __addr,
    socklen_t *__restrict __addr_len);
extern ssize_t sendmsg (int __fd, const struct msghdr *__message,
   int __flags);
extern int sendmmsg (int __fd, struct mmsghdr *__vmessages,
       unsigned int __vlen, int __flags);
extern ssize_t recvmsg (int __fd, struct msghdr *__message, int __flags);
extern int recvmmsg (int __fd, struct mmsghdr *__vmessages,
       unsigned int __vlen, int __flags,
       struct timespec *__tmo);
extern int getsockopt (int __fd, int __level, int __optname,
         void *__restrict __optval,
         socklen_t *__restrict __optlen) __attribute__ ((__nothrow__ , __leaf__));
extern int setsockopt (int __fd, int __level, int __optname,
         const void *__optval, socklen_t __optlen) __attribute__ ((__nothrow__ , __leaf__));
extern int listen (int __fd, int __n) __attribute__ ((__nothrow__ , __leaf__));
extern int accept (int __fd, __SOCKADDR_ARG __addr,
     socklen_t *__restrict __addr_len);
extern int accept4 (int __fd, __SOCKADDR_ARG __addr,
      socklen_t *__restrict __addr_len, int __flags);
extern int shutdown (int __fd, int __how) __attribute__ ((__nothrow__ , __leaf__));
extern int sockatmark (int __fd) __attribute__ ((__nothrow__ , __leaf__));
extern int isfdtype (int __fd, int __fdtype) __attribute__ ((__nothrow__ , __leaf__));


struct stat
  {
    __dev_t st_dev;
    __ino_t st_ino;
    __nlink_t st_nlink;
    __mode_t st_mode;
    __uid_t st_uid;
    __gid_t st_gid;
    int __pad0;
    __dev_t st_rdev;
    __off_t st_size;
    __blksize_t st_blksize;
    __blkcnt_t st_blocks;
    struct timespec st_atim;
    struct timespec st_mtim;
    struct timespec st_ctim;
    __syscall_slong_t __glibc_reserved[3];
  };
struct stat64
  {
    __dev_t st_dev;
    __ino64_t st_ino;
    __nlink_t st_nlink;
    __mode_t st_mode;
    __uid_t st_uid;
    __gid_t st_gid;
    int __pad0;
    __dev_t st_rdev;
    __off_t st_size;
    __blksize_t st_blksize;
    __blkcnt64_t st_blocks;
    struct timespec st_atim;
    struct timespec st_mtim;
    struct timespec st_ctim;
    __syscall_slong_t __glibc_reserved[3];
  };
extern int stat (const char *__restrict __file, struct stat *__restrict __buf) __asm__ ("" "stat64") __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__nonnull__ (1, 2)));
extern int fstat (int __fd, struct stat *__buf) __asm__ ("" "fstat64") __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__nonnull__ (2)));
extern int stat64 (const char *__restrict __file,
     struct stat64 *__restrict __buf) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int fstat64 (int __fd, struct stat64 *__buf) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int fstatat (int __fd, const char *__restrict __file, struct stat *__restrict __buf, int __flag) __asm__ ("" "fstatat64") __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3)));
extern int fstatat64 (int __fd, const char *__restrict __file,
        struct stat64 *__restrict __buf, int __flag)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3)));
extern int lstat (const char *__restrict __file, struct stat *__restrict __buf) __asm__ ("" "lstat64") __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__nonnull__ (1, 2)));
extern int lstat64 (const char *__restrict __file,
      struct stat64 *__restrict __buf)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int chmod (const char *__file, __mode_t __mode)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int lchmod (const char *__file, __mode_t __mode)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int fchmod (int __fd, __mode_t __mode) __attribute__ ((__nothrow__ , __leaf__));
extern int fchmodat (int __fd, const char *__file, __mode_t __mode,
       int __flag)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2))) ;
extern __mode_t umask (__mode_t __mask) __attribute__ ((__nothrow__ , __leaf__));
extern __mode_t getumask (void) __attribute__ ((__nothrow__ , __leaf__));
extern int mkdir (const char *__path, __mode_t __mode)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int mkdirat (int __fd, const char *__path, __mode_t __mode)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int mknod (const char *__path, __mode_t __mode, __dev_t __dev)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int mknodat (int __fd, const char *__path, __mode_t __mode,
      __dev_t __dev) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int mkfifo (const char *__path, __mode_t __mode)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int mkfifoat (int __fd, const char *__path, __mode_t __mode)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int utimensat (int __fd, const char *__path,
        const struct timespec __times[2],
        int __flags)
     __attribute__ ((__nothrow__ , __leaf__));
extern int futimens (int __fd, const struct timespec __times[2]) __attribute__ ((__nothrow__ , __leaf__));
typedef __signed__ char __s8;
typedef unsigned char __u8;
typedef __signed__ short __s16;
typedef unsigned short __u16;
typedef __signed__ int __s32;
typedef unsigned int __u32;
__extension__ typedef __signed__ long long __s64;
__extension__ typedef unsigned long long __u64;
typedef __signed__ __int128 __s128 __attribute__((aligned(16)));
typedef unsigned __int128 __u128 __attribute__((aligned(16)));
typedef __u16 __le16;
typedef __u16 __be16;
typedef __u32 __le32;
typedef __u32 __be32;
typedef __u64 __le64;
typedef __u64 __be64;
typedef __u16 __sum16;
typedef __u32 __wsum;
typedef unsigned __poll_t;
struct statx_timestamp {
 __s64 tv_sec;
 __u32 tv_nsec;
 __s32 __reserved;
};
struct statx {
 __u32 stx_mask;
 __u32 stx_blksize;
 __u64 stx_attributes;
 __u32 stx_nlink;
 __u32 stx_uid;
 __u32 stx_gid;
 __u16 stx_mode;
 __u16 __spare0[1];
 __u64 stx_ino;
 __u64 stx_size;
 __u64 stx_blocks;
 __u64 stx_attributes_mask;
 struct statx_timestamp stx_atime;
 struct statx_timestamp stx_btime;
 struct statx_timestamp stx_ctime;
 struct statx_timestamp stx_mtime;
 __u32 stx_rdev_major;
 __u32 stx_rdev_minor;
 __u32 stx_dev_major;
 __u32 stx_dev_minor;
 __u64 stx_mnt_id;
 __u32 stx_dio_mem_align;
 __u32 stx_dio_offset_align;
 __u64 stx_subvol;
 __u32 stx_atomic_write_unit_min;
 __u32 stx_atomic_write_unit_max;
 __u32 stx_atomic_write_segments_max;
 __u32 __spare1[1];
 __u64 __spare3[9];
};

int statx (int __dirfd, const char *__restrict __path, int __flags,
           unsigned int __mask, struct statx *__restrict __buf)
  __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (5)));


enum __rlimit_resource
{
  RLIMIT_CPU = 0,
  RLIMIT_FSIZE = 1,
  RLIMIT_DATA = 2,
  RLIMIT_STACK = 3,
  RLIMIT_CORE = 4,
  __RLIMIT_RSS = 5,
  RLIMIT_NOFILE = 7,
  __RLIMIT_OFILE = RLIMIT_NOFILE,
  RLIMIT_AS = 9,
  __RLIMIT_NPROC = 6,
  __RLIMIT_MEMLOCK = 8,
  __RLIMIT_LOCKS = 10,
  __RLIMIT_SIGPENDING = 11,
  __RLIMIT_MSGQUEUE = 12,
  __RLIMIT_NICE = 13,
  __RLIMIT_RTPRIO = 14,
  __RLIMIT_RTTIME = 15,
  __RLIMIT_NLIMITS = 16,
  __RLIM_NLIMITS = __RLIMIT_NLIMITS
};
typedef __rlim64_t rlim_t;
typedef __rlim64_t rlim64_t;
struct rlimit
  {
    rlim_t rlim_cur;
    rlim_t rlim_max;
  };
struct rlimit64
  {
    rlim64_t rlim_cur;
    rlim64_t rlim_max;
 };
enum __rusage_who
{
  RUSAGE_SELF = 0,
  RUSAGE_CHILDREN = -1
  ,
  RUSAGE_THREAD = 1
};
struct rusage
  {
    struct timeval ru_utime;
    struct timeval ru_stime;
    __extension__ union
      {
 long int ru_maxrss;
 __syscall_slong_t __ru_maxrss_word;
      };
    __extension__ union
      {
 long int ru_ixrss;
 __syscall_slong_t __ru_ixrss_word;
      };
    __extension__ union
      {
 long int ru_idrss;
 __syscall_slong_t __ru_idrss_word;
      };
    __extension__ union
      {
 long int ru_isrss;
  __syscall_slong_t __ru_isrss_word;
      };
    __extension__ union
      {
 long int ru_minflt;
 __syscall_slong_t __ru_minflt_word;
      };
    __extension__ union
      {
 long int ru_majflt;
 __syscall_slong_t __ru_majflt_word;
      };
    __extension__ union
      {
 long int ru_nswap;
 __syscall_slong_t __ru_nswap_word;
      };
    __extension__ union
      {
 long int ru_inblock;
 __syscall_slong_t __ru_inblock_word;
      };
    __extension__ union
      {
 long int ru_oublock;
 __syscall_slong_t __ru_oublock_word;
      };
    __extension__ union
      {
 long int ru_msgsnd;
 __syscall_slong_t __ru_msgsnd_word;
      };
    __extension__ union
      {
 long int ru_msgrcv;
 __syscall_slong_t __ru_msgrcv_word;
      };
    __extension__ union
      {
 long int ru_nsignals;
 __syscall_slong_t __ru_nsignals_word;
      };
    __extension__ union
      {
 long int ru_nvcsw;
 __syscall_slong_t __ru_nvcsw_word;
      };
    __extension__ union
      {
 long int ru_nivcsw;
 __syscall_slong_t __ru_nivcsw_word;
      };
  };
enum __priority_which
{
  PRIO_PROCESS = 0,
  PRIO_PGRP = 1,
  PRIO_USER = 2
};

extern int prlimit (__pid_t __pid, enum __rlimit_resource __resource, const struct rlimit *__new_limit, struct rlimit *__old_limit) __asm__ ("" "prlimit64") __attribute__ ((__nothrow__ , __leaf__));
extern int prlimit64 (__pid_t __pid, enum __rlimit_resource __resource,
        const struct rlimit64 *__new_limit,
        struct rlimit64 *__old_limit) __attribute__ ((__nothrow__ , __leaf__));


typedef enum __rlimit_resource __rlimit_resource_t;
typedef enum __rusage_who __rusage_who_t;
typedef enum __priority_which __priority_which_t;
extern int getrlimit (__rlimit_resource_t __resource, struct rlimit *__rlimits) __asm__ ("" "getrlimit64") __attribute__ ((__nothrow__ , __leaf__))
           __attribute__ ((__nonnull__ (2)));
extern int getrlimit64 (__rlimit_resource_t __resource,
   struct rlimit64 *__rlimits) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int setrlimit (__rlimit_resource_t __resource, const struct rlimit *__rlimits) __asm__ ("" "setrlimit64") __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int setrlimit64 (__rlimit_resource_t __resource,
   const struct rlimit64 *__rlimits) __attribute__ ((__nothrow__ , __leaf__))
   __attribute__ ((__nonnull__ (2)));
extern int getrusage (__rusage_who_t __who, struct rusage *__usage) __attribute__ ((__nothrow__ , __leaf__));
extern int getpriority (__priority_which_t __which, id_t __who) __attribute__ ((__nothrow__ , __leaf__));
extern int setpriority (__priority_which_t __which, id_t __who, int __prio)
     __attribute__ ((__nothrow__ , __leaf__));



typedef __sig_atomic_t sig_atomic_t;
union sigval
{
  int sival_int;
  void *sival_ptr;
};
typedef union sigval __sigval_t;
typedef struct
  {
    int si_signo;
    int si_errno;
    int si_code;
    int __pad0;
    union
      {
 int _pad[((128 / sizeof (int)) - 4)];
 struct
   {
     __pid_t si_pid;
     __uid_t si_uid;
   } _kill;
 struct
   {
     int si_tid;
     int si_overrun;
     __sigval_t si_sigval;
   } _timer;
 struct
   {
     __pid_t si_pid;
     __uid_t si_uid;
     __sigval_t si_sigval;
   } _rt;
 struct
   {
     __pid_t si_pid;
     __uid_t si_uid;
     int si_status;
     __clock_t si_utime;
     __clock_t si_stime;
   } _sigchld;
 struct
   {
     void *si_addr;
    
     short int si_addr_lsb;
     union
       {
  struct
    {
      void *_lower;
      void *_upper;
    } _addr_bnd;
  __uint32_t _pkey;
       } _bounds;
   } _sigfault;
 struct
   {
     long int si_band;
     int si_fd;
   } _sigpoll;
 struct
   {
     void *_call_addr;
     int _syscall;
     unsigned int _arch;
   } _sigsys;
      } _sifields;
  } siginfo_t ;
enum
{
  SI_ASYNCNL = -60,
  SI_DETHREAD = -7,
  SI_TKILL,
  SI_SIGIO,
  SI_ASYNCIO,
  SI_MESGQ,
  SI_TIMER,
  SI_QUEUE,
  SI_USER,
  SI_KERNEL = 0x80
};
enum
{
  ILL_ILLOPC = 1,
  ILL_ILLOPN,
  ILL_ILLADR,
  ILL_ILLTRP,
  ILL_PRVOPC,
  ILL_PRVREG,
  ILL_COPROC,
  ILL_BADSTK,
  ILL_BADIADDR
};
enum
{
  FPE_INTDIV = 1,
  FPE_INTOVF,
  FPE_FLTDIV,
  FPE_FLTOVF,
  FPE_FLTUND,
  FPE_FLTRES,
  FPE_FLTINV,
  FPE_FLTSUB,
  FPE_FLTUNK = 14,
  FPE_CONDTRAP
};
enum
{
  SEGV_MAPERR = 1,
  SEGV_ACCERR,
  SEGV_BNDERR,
  SEGV_PKUERR,
  SEGV_ACCADI,
  SEGV_ADIDERR,
  SEGV_ADIPERR,
  SEGV_MTEAERR,
  SEGV_MTESERR,
  SEGV_CPERR
};
enum
{
  BUS_ADRALN = 1,
  BUS_ADRERR,
  BUS_OBJERR,
  BUS_MCEERR_AR,
  BUS_MCEERR_AO
};
enum
{
  TRAP_BRKPT = 1,
  TRAP_TRACE,
  TRAP_BRANCH,
  TRAP_HWBKPT,
  TRAP_UNK
};
enum
{
  CLD_EXITED = 1,
  CLD_KILLED,
  CLD_DUMPED,
  CLD_TRAPPED,
  CLD_STOPPED,
  CLD_CONTINUED
};
enum
{
  POLL_IN = 1,
  POLL_OUT,
  POLL_MSG,
  POLL_ERR,
  POLL_PRI,
  POLL_HUP
};
typedef __sigval_t sigval_t;
typedef struct sigevent
  {
    __sigval_t sigev_value;
    int sigev_signo;
    int sigev_notify;
    union
      {
 int _pad[((64 / sizeof (int)) - 4)];
 __pid_t _tid;
 struct
   {
     void (*_function) (__sigval_t);
     pthread_attr_t *_attribute;
   } _sigev_thread;
      } _sigev_un;
  } sigevent_t;
enum
{
  SIGEV_SIGNAL = 0,
  SIGEV_NONE,
  SIGEV_THREAD,
  SIGEV_THREAD_ID = 4
};
typedef void (*__sighandler_t) (int);
extern __sighandler_t __sysv_signal (int __sig, __sighandler_t __handler)
     __attribute__ ((__nothrow__ , __leaf__));
extern __sighandler_t sysv_signal (int __sig, __sighandler_t __handler)
     __attribute__ ((__nothrow__ , __leaf__));
extern __sighandler_t signal (int __sig, __sighandler_t __handler)
     __attribute__ ((__nothrow__ , __leaf__));
extern int kill (__pid_t __pid, int __sig) __attribute__ ((__nothrow__ , __leaf__));
extern int killpg (__pid_t __pgrp, int __sig) __attribute__ ((__nothrow__ , __leaf__));
extern int raise (int __sig) __attribute__ ((__nothrow__ , __leaf__));
extern __sighandler_t ssignal (int __sig, __sighandler_t __handler)
     __attribute__ ((__nothrow__ , __leaf__));
extern int gsignal (int __sig) __attribute__ ((__nothrow__ , __leaf__));
extern void psignal (int __sig, const char *__s);
extern void psiginfo (const siginfo_t *__pinfo, const char *__s);
extern int sigpause (int __sig) __asm__ ("__xpg_sigpause")
  __attribute__ ((__deprecated__ ("Use the sigsuspend function instead")));
extern int sigblock (int __mask) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__deprecated__));
extern int sigsetmask (int __mask) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__deprecated__));
extern int siggetmask (void) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__deprecated__));
typedef __sighandler_t sighandler_t;
typedef __sighandler_t sig_t;
extern int sigemptyset (sigset_t *__set) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int sigfillset (sigset_t *__set) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int sigaddset (sigset_t *__set, int __signo) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int sigdelset (sigset_t *__set, int __signo) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int sigismember (const sigset_t *__set, int __signo)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int sigisemptyset (const sigset_t *__set) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int sigandset (sigset_t *__set, const sigset_t *__left,
        const sigset_t *__right) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2, 3)));
extern int sigorset (sigset_t *__set, const sigset_t *__left,
       const sigset_t *__right) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2, 3)));
struct sigaction
  {
    union
      {
 __sighandler_t sa_handler;
 void (*sa_sigaction) (int, siginfo_t *, void *);
      }
    __sigaction_handler;
    __sigset_t sa_mask;
    int sa_flags;
    void (*sa_restorer) (void);
  };
extern int sigprocmask (int __how, const sigset_t *__restrict __set,
   sigset_t *__restrict __oset) __attribute__ ((__nothrow__ , __leaf__));
extern int sigsuspend (const sigset_t *__set) __attribute__ ((__nonnull__ (1)));
extern int sigaction (int __sig, const struct sigaction *__restrict __act,
        struct sigaction *__restrict __oact) __attribute__ ((__nothrow__ , __leaf__));
extern int sigpending (sigset_t *__set) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int sigwait (const sigset_t *__restrict __set, int *__restrict __sig)
     __attribute__ ((__nonnull__ (1, 2)));
extern int sigwaitinfo (const sigset_t *__restrict __set,
   siginfo_t *__restrict __info) __attribute__ ((__nonnull__ (1)));
extern int sigtimedwait (const sigset_t *__restrict __set,
    siginfo_t *__restrict __info,
    const struct timespec *__restrict __timeout)
     __attribute__ ((__nonnull__ (1)));
extern int sigqueue (__pid_t __pid, int __sig, const union sigval __val)
     __attribute__ ((__nothrow__ , __leaf__));
struct _fpx_sw_bytes
{
  __uint32_t magic1;
  __uint32_t extended_size;
  __uint64_t xstate_bv;
  __uint32_t xstate_size;
  __uint32_t __glibc_reserved1[7];
};
struct _fpreg
{
  unsigned short significand[4];
  unsigned short exponent;
};
struct _fpxreg
{
  unsigned short significand[4];
  unsigned short exponent;
  unsigned short __glibc_reserved1[3];
};
struct _xmmreg
{
  __uint32_t element[4];
};
struct _fpstate
{
  __uint16_t cwd;
  __uint16_t swd;
  __uint16_t ftw;
  __uint16_t fop;
  __uint64_t rip;
  __uint64_t rdp;
  __uint32_t mxcsr;
  __uint32_t mxcr_mask;
  struct _fpxreg _st[8];
  struct _xmmreg _xmm[16];
  __uint32_t __glibc_reserved1[24];
};
struct sigcontext
{
  __uint64_t r8;
  __uint64_t r9;
  __uint64_t r10;
  __uint64_t r11;
  __uint64_t r12;
  __uint64_t r13;
  __uint64_t r14;
  __uint64_t r15;
  __uint64_t rdi;
  __uint64_t rsi;
  __uint64_t rbp;
  __uint64_t rbx;
  __uint64_t rdx;
  __uint64_t rax;
  __uint64_t rcx;
  __uint64_t rsp;
  __uint64_t rip;
  __uint64_t eflags;
  unsigned short cs;
  unsigned short gs;
  unsigned short fs;
  unsigned short __pad0;
  __uint64_t err;
  __uint64_t trapno;
  __uint64_t oldmask;
  __uint64_t cr2;
  __extension__ union
    {
      struct _fpstate * fpstate;
      __uint64_t __fpstate_word;
    };
  __uint64_t __reserved1 [8];
};
struct _xsave_hdr
{
  __uint64_t xstate_bv;
  __uint64_t __glibc_reserved1[2];
  __uint64_t __glibc_reserved2[5];
};
struct _ymmh_state
{
  __uint32_t ymmh_space[64];
};
struct _xstate
{
  struct _fpstate fpstate;
  struct _xsave_hdr xstate_hdr;
  struct _ymmh_state ymmh;
};
extern int sigreturn (struct sigcontext *__scp) __attribute__ ((__nothrow__ , __leaf__));
typedef struct
  {
    void *ss_sp;
    int ss_flags;
    size_t ss_size;
  } stack_t;
__extension__ typedef long long int greg_t;
typedef greg_t gregset_t[23];
enum
{
  REG_R8 = 0,
  REG_R9,
  REG_R10,
  REG_R11,
  REG_R12,
  REG_R13,
  REG_R14,
  REG_R15,
  REG_RDI,
  REG_RSI,
  REG_RBP,
  REG_RBX,
  REG_RDX,
  REG_RAX,
  REG_RCX,
  REG_RSP,
  REG_RIP,
  REG_EFL,
  REG_CSGSFS,
  REG_ERR,
  REG_TRAPNO,
  REG_OLDMASK,
  REG_CR2
};
struct _libc_fpxreg
{
  unsigned short int significand[4];
  unsigned short int exponent;
  unsigned short int __glibc_reserved1[3];
};
struct _libc_xmmreg
{
  __uint32_t element[4];
};
struct _libc_fpstate
{
  __uint16_t cwd;
  __uint16_t swd;
  __uint16_t ftw;
  __uint16_t fop;
  __uint64_t rip;
  __uint64_t rdp;
  __uint32_t mxcsr;
  __uint32_t mxcr_mask;
  struct _libc_fpxreg _st[8];
  struct _libc_xmmreg _xmm[16];
  __uint32_t __glibc_reserved1[24];
};
typedef struct _libc_fpstate *fpregset_t;
typedef struct
  {
    gregset_t gregs;
    fpregset_t fpregs;
    __extension__ unsigned long long __reserved1 [8];
} mcontext_t;
typedef struct ucontext_t
  {
    unsigned long int uc_flags;
    struct ucontext_t *uc_link;
    stack_t uc_stack;
    mcontext_t uc_mcontext;
    sigset_t uc_sigmask;
    struct _libc_fpstate __fpregs_mem;
    __extension__ unsigned long long int __ssp[4];
  } ucontext_t;
extern int siginterrupt (int __sig, int __interrupt) __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__deprecated__ ("Use sigaction with SA_RESTART instead")));

typedef __intptr_t intptr_t;
extern int access (const char *__name, int __type) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int euidaccess (const char *__name, int __type)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int eaccess (const char *__name, int __type)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int execveat (int __fd, const char *__path, char *const __argv[],
                     char *const __envp[], int __flags)
    __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 3)));
extern int faccessat (int __fd, const char *__file, int __type, int __flag)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2))) ;
extern __off64_t lseek (int __fd, __off64_t __offset, int __whence) __asm__ ("" "lseek64") __attribute__ ((__nothrow__ , __leaf__));
extern __off64_t lseek64 (int __fd, __off64_t __offset, int __whence)
     __attribute__ ((__nothrow__ , __leaf__));
extern int close (int __fd);
extern void closefrom (int __lowfd) __attribute__ ((__nothrow__ , __leaf__));
extern ssize_t read (int __fd, void *__buf, size_t __nbytes)
    __attribute__ ((__access__ (__write_only__, 2, 3)));
extern ssize_t write (int __fd, const void *__buf, size_t __n)
    __attribute__ ((__access__ (__read_only__, 2, 3)));
extern ssize_t pread (int __fd, void *__buf, size_t __nbytes, __off64_t __offset) __asm__ ("" "pread64")
    __attribute__ ((__access__ (__write_only__, 2, 3)));
extern ssize_t pwrite (int __fd, const void *__buf, size_t __nbytes, __off64_t __offset) __asm__ ("" "pwrite64")
    __attribute__ ((__access__ (__read_only__, 2, 3)));
extern ssize_t pread64 (int __fd, void *__buf, size_t __nbytes,
   __off64_t __offset)
    __attribute__ ((__access__ (__write_only__, 2, 3)));
extern ssize_t pwrite64 (int __fd, const void *__buf, size_t __n,
    __off64_t __offset)
    __attribute__ ((__access__ (__read_only__, 2, 3)));
extern int pipe (int __pipedes[2]) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int pipe2 (int __pipedes[2], int __flags) __attribute__ ((__nothrow__ , __leaf__)) ;
extern unsigned int alarm (unsigned int __seconds) __attribute__ ((__nothrow__ , __leaf__));
extern unsigned int sleep (unsigned int __seconds);
extern __useconds_t ualarm (__useconds_t __value, __useconds_t __interval)
     __attribute__ ((__nothrow__ , __leaf__));
extern int usleep (__useconds_t __useconds);
extern int pause (void);
extern int chown (const char *__file, __uid_t __owner, __gid_t __group)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int fchown (int __fd, __uid_t __owner, __gid_t __group) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int lchown (const char *__file, __uid_t __owner, __gid_t __group)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int fchownat (int __fd, const char *__file, __uid_t __owner,
       __gid_t __group, int __flag)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2))) ;
extern int chdir (const char *__path) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int fchdir (int __fd) __attribute__ ((__nothrow__ , __leaf__)) ;
extern char *getcwd (char *__buf, size_t __size) __attribute__ ((__nothrow__ , __leaf__)) ;
extern char *get_current_dir_name (void) __attribute__ ((__nothrow__ , __leaf__));
extern char *getwd (char *__buf)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) __attribute__ ((__deprecated__))
    __attribute__ ((__access__ (__write_only__, 1)));
extern int dup (int __fd) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int dup2 (int __fd, int __fd2) __attribute__ ((__nothrow__ , __leaf__));
extern int dup3 (int __fd, int __fd2, int __flags) __attribute__ ((__nothrow__ , __leaf__));
extern char **__environ;
extern char **environ;
extern int execve (const char *__path, char *const __argv[],
     char *const __envp[]) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int fexecve (int __fd, char *const __argv[], char *const __envp[])
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int execv (const char *__path, char *const __argv[])
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int execle (const char *__path, const char *__arg, ...)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int execl (const char *__path, const char *__arg, ...)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int execvp (const char *__file, char *const __argv[])
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int execlp (const char *__file, const char *__arg, ...)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int execvpe (const char *__file, char *const __argv[],
      char *const __envp[])
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int nice (int __inc) __attribute__ ((__nothrow__ , __leaf__)) ;
extern void _exit (int __status) __attribute__ ((__noreturn__));
enum
  {
    _PC_LINK_MAX,
    _PC_MAX_CANON,
    _PC_MAX_INPUT,
    _PC_NAME_MAX,
    _PC_PATH_MAX,
    _PC_PIPE_BUF,
    _PC_CHOWN_RESTRICTED,
    _PC_NO_TRUNC,
    _PC_VDISABLE,
    _PC_SYNC_IO,
    _PC_ASYNC_IO,
    _PC_PRIO_IO,
    _PC_SOCK_MAXBUF,
    _PC_FILESIZEBITS,
    _PC_REC_INCR_XFER_SIZE,
    _PC_REC_MAX_XFER_SIZE,
    _PC_REC_MIN_XFER_SIZE,
    _PC_REC_XFER_ALIGN,
    _PC_ALLOC_SIZE_MIN,
    _PC_SYMLINK_MAX,
    _PC_2_SYMLINKS
  };
enum
  {
    _SC_ARG_MAX,
    _SC_CHILD_MAX,
    _SC_CLK_TCK,
    _SC_NGROUPS_MAX,
    _SC_OPEN_MAX,
    _SC_STREAM_MAX,
    _SC_TZNAME_MAX,
    _SC_JOB_CONTROL,
    _SC_SAVED_IDS,
    _SC_REALTIME_SIGNALS,
    _SC_PRIORITY_SCHEDULING,
    _SC_TIMERS,
    _SC_ASYNCHRONOUS_IO,
    _SC_PRIORITIZED_IO,
    _SC_SYNCHRONIZED_IO,
    _SC_FSYNC,
    _SC_MAPPED_FILES,
    _SC_MEMLOCK,
    _SC_MEMLOCK_RANGE,
    _SC_MEMORY_PROTECTION,
    _SC_MESSAGE_PASSING,
    _SC_SEMAPHORES,
    _SC_SHARED_MEMORY_OBJECTS,
    _SC_AIO_LISTIO_MAX,
    _SC_AIO_MAX,
    _SC_AIO_PRIO_DELTA_MAX,
    _SC_DELAYTIMER_MAX,
    _SC_MQ_OPEN_MAX,
    _SC_MQ_PRIO_MAX,
    _SC_VERSION,
    _SC_PAGESIZE,
    _SC_RTSIG_MAX,
    _SC_SEM_NSEMS_MAX,
    _SC_SEM_VALUE_MAX,
    _SC_SIGQUEUE_MAX,
    _SC_TIMER_MAX,
    _SC_BC_BASE_MAX,
    _SC_BC_DIM_MAX,
    _SC_BC_SCALE_MAX,
    _SC_BC_STRING_MAX,
    _SC_COLL_WEIGHTS_MAX,
    _SC_EQUIV_CLASS_MAX,
    _SC_EXPR_NEST_MAX,
    _SC_LINE_MAX,
    _SC_RE_DUP_MAX,
    _SC_CHARCLASS_NAME_MAX,
    _SC_2_VERSION,
    _SC_2_C_BIND,
    _SC_2_C_DEV,
    _SC_2_FORT_DEV,
    _SC_2_FORT_RUN,
    _SC_2_SW_DEV,
    _SC_2_LOCALEDEF,
    _SC_PII,
    _SC_PII_XTI,
    _SC_PII_SOCKET,
    _SC_PII_INTERNET,
    _SC_PII_OSI,
    _SC_POLL,
    _SC_SELECT,
    _SC_UIO_MAXIOV,
    _SC_IOV_MAX = _SC_UIO_MAXIOV,
    _SC_PII_INTERNET_STREAM,
    _SC_PII_INTERNET_DGRAM,
    _SC_PII_OSI_COTS,
    _SC_PII_OSI_CLTS,
    _SC_PII_OSI_M,
    _SC_T_IOV_MAX,
    _SC_THREADS,
    _SC_THREAD_SAFE_FUNCTIONS,
    _SC_GETGR_R_SIZE_MAX,
    _SC_GETPW_R_SIZE_MAX,
    _SC_LOGIN_NAME_MAX,
    _SC_TTY_NAME_MAX,
    _SC_THREAD_DESTRUCTOR_ITERATIONS,
    _SC_THREAD_KEYS_MAX,
    _SC_THREAD_STACK_MIN,
    _SC_THREAD_THREADS_MAX,
    _SC_THREAD_ATTR_STACKADDR,
    _SC_THREAD_ATTR_STACKSIZE,
    _SC_THREAD_PRIORITY_SCHEDULING,
    _SC_THREAD_PRIO_INHERIT,
    _SC_THREAD_PRIO_PROTECT,
    _SC_THREAD_PROCESS_SHARED,
    _SC_NPROCESSORS_CONF,
    _SC_NPROCESSORS_ONLN,
    _SC_PHYS_PAGES,
    _SC_AVPHYS_PAGES,
    _SC_ATEXIT_MAX,
    _SC_PASS_MAX,
    _SC_XOPEN_VERSION,
    _SC_XOPEN_XCU_VERSION,
    _SC_XOPEN_UNIX,
    _SC_XOPEN_CRYPT,
    _SC_XOPEN_ENH_I18N,
    _SC_XOPEN_SHM,
    _SC_2_CHAR_TERM,
    _SC_2_C_VERSION,
    _SC_2_UPE,
    _SC_XOPEN_XPG2,
    _SC_XOPEN_XPG3,
    _SC_XOPEN_XPG4,
    _SC_CHAR_BIT,
    _SC_CHAR_MAX,
    _SC_CHAR_MIN,
    _SC_INT_MAX,
    _SC_INT_MIN,
    _SC_LONG_BIT,
    _SC_WORD_BIT,
    _SC_MB_LEN_MAX,
    _SC_NZERO,
    _SC_SSIZE_MAX,
    _SC_SCHAR_MAX,
    _SC_SCHAR_MIN,
    _SC_SHRT_MAX,
    _SC_SHRT_MIN,
    _SC_UCHAR_MAX,
    _SC_UINT_MAX,
    _SC_ULONG_MAX,
    _SC_USHRT_MAX,
    _SC_NL_ARGMAX,
    _SC_NL_LANGMAX,
    _SC_NL_MSGMAX,
    _SC_NL_NMAX,
    _SC_NL_SETMAX,
    _SC_NL_TEXTMAX,
    _SC_XBS5_ILP32_OFF32,
    _SC_XBS5_ILP32_OFFBIG,
    _SC_XBS5_LP64_OFF64,
    _SC_XBS5_LPBIG_OFFBIG,
    _SC_XOPEN_LEGACY,
    _SC_XOPEN_REALTIME,
    _SC_XOPEN_REALTIME_THREADS,
    _SC_ADVISORY_INFO,
    _SC_BARRIERS,
    _SC_BASE,
    _SC_C_LANG_SUPPORT,
    _SC_C_LANG_SUPPORT_R,
    _SC_CLOCK_SELECTION,
    _SC_CPUTIME,
    _SC_THREAD_CPUTIME,
    _SC_DEVICE_IO,
    _SC_DEVICE_SPECIFIC,
    _SC_DEVICE_SPECIFIC_R,
    _SC_FD_MGMT,
    _SC_FIFO,
    _SC_PIPE,
    _SC_FILE_ATTRIBUTES,
    _SC_FILE_LOCKING,
    _SC_FILE_SYSTEM,
    _SC_MONOTONIC_CLOCK,
    _SC_MULTI_PROCESS,
    _SC_SINGLE_PROCESS,
    _SC_NETWORKING,
    _SC_READER_WRITER_LOCKS,
    _SC_SPIN_LOCKS,
    _SC_REGEXP,
    _SC_REGEX_VERSION,
    _SC_SHELL,
    _SC_SIGNALS,
    _SC_SPAWN,
    _SC_SPORADIC_SERVER,
    _SC_THREAD_SPORADIC_SERVER,
    _SC_SYSTEM_DATABASE,
    _SC_SYSTEM_DATABASE_R,
    _SC_TIMEOUTS,
    _SC_TYPED_MEMORY_OBJECTS,
    _SC_USER_GROUPS,
    _SC_USER_GROUPS_R,
    _SC_2_PBS,
    _SC_2_PBS_ACCOUNTING,
    _SC_2_PBS_LOCATE,
    _SC_2_PBS_MESSAGE,
    _SC_2_PBS_TRACK,
    _SC_SYMLOOP_MAX,
    _SC_STREAMS,
    _SC_2_PBS_CHECKPOINT,
    _SC_V6_ILP32_OFF32,
    _SC_V6_ILP32_OFFBIG,
    _SC_V6_LP64_OFF64,
    _SC_V6_LPBIG_OFFBIG,
    _SC_HOST_NAME_MAX,
    _SC_TRACE,
    _SC_TRACE_EVENT_FILTER,
    _SC_TRACE_INHERIT,
    _SC_TRACE_LOG,
    _SC_LEVEL1_ICACHE_SIZE,
    _SC_LEVEL1_ICACHE_ASSOC,
    _SC_LEVEL1_ICACHE_LINESIZE,
    _SC_LEVEL1_DCACHE_SIZE,
    _SC_LEVEL1_DCACHE_ASSOC,
    _SC_LEVEL1_DCACHE_LINESIZE,
    _SC_LEVEL2_CACHE_SIZE,
    _SC_LEVEL2_CACHE_ASSOC,
    _SC_LEVEL2_CACHE_LINESIZE,
    _SC_LEVEL3_CACHE_SIZE,
    _SC_LEVEL3_CACHE_ASSOC,
    _SC_LEVEL3_CACHE_LINESIZE,
    _SC_LEVEL4_CACHE_SIZE,
    _SC_LEVEL4_CACHE_ASSOC,
    _SC_LEVEL4_CACHE_LINESIZE,
    _SC_IPV6 = _SC_LEVEL1_ICACHE_SIZE + 50,
    _SC_RAW_SOCKETS,
    _SC_V7_ILP32_OFF32,
    _SC_V7_ILP32_OFFBIG,
    _SC_V7_LP64_OFF64,
    _SC_V7_LPBIG_OFFBIG,
    _SC_SS_REPL_MAX,
    _SC_TRACE_EVENT_NAME_MAX,
    _SC_TRACE_NAME_MAX,
    _SC_TRACE_SYS_MAX,
    _SC_TRACE_USER_EVENT_MAX,
    _SC_XOPEN_STREAMS,
    _SC_THREAD_ROBUST_PRIO_INHERIT,
    _SC_THREAD_ROBUST_PRIO_PROTECT,
    _SC_MINSIGSTKSZ,
    _SC_SIGSTKSZ
  };
enum
  {
    _CS_PATH,
    _CS_V6_WIDTH_RESTRICTED_ENVS,
    _CS_GNU_LIBC_VERSION,
    _CS_GNU_LIBPTHREAD_VERSION,
    _CS_V5_WIDTH_RESTRICTED_ENVS,
    _CS_V7_WIDTH_RESTRICTED_ENVS,
    _CS_LFS_CFLAGS = 1000,
    _CS_LFS_LDFLAGS,
    _CS_LFS_LIBS,
    _CS_LFS_LINTFLAGS,
    _CS_LFS64_CFLAGS,
    _CS_LFS64_LDFLAGS,
    _CS_LFS64_LIBS,
    _CS_LFS64_LINTFLAGS,
    _CS_XBS5_ILP32_OFF32_CFLAGS = 1100,
    _CS_XBS5_ILP32_OFF32_LDFLAGS,
    _CS_XBS5_ILP32_OFF32_LIBS,
    _CS_XBS5_ILP32_OFF32_LINTFLAGS,
    _CS_XBS5_ILP32_OFFBIG_CFLAGS,
    _CS_XBS5_ILP32_OFFBIG_LDFLAGS,
    _CS_XBS5_ILP32_OFFBIG_LIBS,
    _CS_XBS5_ILP32_OFFBIG_LINTFLAGS,
    _CS_XBS5_LP64_OFF64_CFLAGS,
    _CS_XBS5_LP64_OFF64_LDFLAGS,
    _CS_XBS5_LP64_OFF64_LIBS,
    _CS_XBS5_LP64_OFF64_LINTFLAGS,
    _CS_XBS5_LPBIG_OFFBIG_CFLAGS,
    _CS_XBS5_LPBIG_OFFBIG_LDFLAGS,
    _CS_XBS5_LPBIG_OFFBIG_LIBS,
    _CS_XBS5_LPBIG_OFFBIG_LINTFLAGS,
    _CS_POSIX_V6_ILP32_OFF32_CFLAGS,
    _CS_POSIX_V6_ILP32_OFF32_LDFLAGS,
    _CS_POSIX_V6_ILP32_OFF32_LIBS,
    _CS_POSIX_V6_ILP32_OFF32_LINTFLAGS,
    _CS_POSIX_V6_ILP32_OFFBIG_CFLAGS,
    _CS_POSIX_V6_ILP32_OFFBIG_LDFLAGS,
    _CS_POSIX_V6_ILP32_OFFBIG_LIBS,
    _CS_POSIX_V6_ILP32_OFFBIG_LINTFLAGS,
    _CS_POSIX_V6_LP64_OFF64_CFLAGS,
    _CS_POSIX_V6_LP64_OFF64_LDFLAGS,
    _CS_POSIX_V6_LP64_OFF64_LIBS,
    _CS_POSIX_V6_LP64_OFF64_LINTFLAGS,
    _CS_POSIX_V6_LPBIG_OFFBIG_CFLAGS,
    _CS_POSIX_V6_LPBIG_OFFBIG_LDFLAGS,
    _CS_POSIX_V6_LPBIG_OFFBIG_LIBS,
    _CS_POSIX_V6_LPBIG_OFFBIG_LINTFLAGS,
    _CS_POSIX_V7_ILP32_OFF32_CFLAGS,
    _CS_POSIX_V7_ILP32_OFF32_LDFLAGS,
    _CS_POSIX_V7_ILP32_OFF32_LIBS,
    _CS_POSIX_V7_ILP32_OFF32_LINTFLAGS,
    _CS_POSIX_V7_ILP32_OFFBIG_CFLAGS,
    _CS_POSIX_V7_ILP32_OFFBIG_LDFLAGS,
    _CS_POSIX_V7_ILP32_OFFBIG_LIBS,
    _CS_POSIX_V7_ILP32_OFFBIG_LINTFLAGS,
    _CS_POSIX_V7_LP64_OFF64_CFLAGS,
    _CS_POSIX_V7_LP64_OFF64_LDFLAGS,
    _CS_POSIX_V7_LP64_OFF64_LIBS,
    _CS_POSIX_V7_LP64_OFF64_LINTFLAGS,
    _CS_POSIX_V7_LPBIG_OFFBIG_CFLAGS,
    _CS_POSIX_V7_LPBIG_OFFBIG_LDFLAGS,
    _CS_POSIX_V7_LPBIG_OFFBIG_LIBS,
    _CS_POSIX_V7_LPBIG_OFFBIG_LINTFLAGS,
    _CS_V6_ENV,
    _CS_V7_ENV
  };
extern long int pathconf (const char *__path, int __name)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern long int fpathconf (int __fd, int __name) __attribute__ ((__nothrow__ , __leaf__));
extern long int sysconf (int __name) __attribute__ ((__nothrow__ , __leaf__));
extern size_t confstr (int __name, char *__buf, size_t __len) __attribute__ ((__nothrow__ , __leaf__))
    __attribute__ ((__access__ (__write_only__, 2, 3)));
extern __pid_t getpid (void) __attribute__ ((__nothrow__ , __leaf__));
extern __pid_t getppid (void) __attribute__ ((__nothrow__ , __leaf__));
extern __pid_t getpgrp (void) __attribute__ ((__nothrow__ , __leaf__));
extern __pid_t __getpgid (__pid_t __pid) __attribute__ ((__nothrow__ , __leaf__));
extern __pid_t getpgid (__pid_t __pid) __attribute__ ((__nothrow__ , __leaf__));
extern int setpgid (__pid_t __pid, __pid_t __pgid) __attribute__ ((__nothrow__ , __leaf__));
extern int setpgrp (void) __attribute__ ((__nothrow__ , __leaf__));
extern __pid_t setsid (void) __attribute__ ((__nothrow__ , __leaf__));
extern __pid_t getsid (__pid_t __pid) __attribute__ ((__nothrow__ , __leaf__));
extern __uid_t getuid (void) __attribute__ ((__nothrow__ , __leaf__));
extern __uid_t geteuid (void) __attribute__ ((__nothrow__ , __leaf__));
extern __gid_t getgid (void) __attribute__ ((__nothrow__ , __leaf__));
extern __gid_t getegid (void) __attribute__ ((__nothrow__ , __leaf__));
extern int getgroups (int __size, __gid_t __list[]) __attribute__ ((__nothrow__ , __leaf__))
    __attribute__ ((__access__ (__write_only__, 2, 1)));
extern int group_member (__gid_t __gid) __attribute__ ((__nothrow__ , __leaf__));
extern int setuid (__uid_t __uid) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int setreuid (__uid_t __ruid, __uid_t __euid) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int seteuid (__uid_t __uid) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int setgid (__gid_t __gid) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int setregid (__gid_t __rgid, __gid_t __egid) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int setegid (__gid_t __gid) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int getresuid (__uid_t *__ruid, __uid_t *__euid, __uid_t *__suid)
     __attribute__ ((__nothrow__ , __leaf__));
extern int getresgid (__gid_t *__rgid, __gid_t *__egid, __gid_t *__sgid)
     __attribute__ ((__nothrow__ , __leaf__));
extern int setresuid (__uid_t __ruid, __uid_t __euid, __uid_t __suid)
     __attribute__ ((__nothrow__ , __leaf__)) ;
extern int setresgid (__gid_t __rgid, __gid_t __egid, __gid_t __sgid)
     __attribute__ ((__nothrow__ , __leaf__)) ;
extern __pid_t fork (void) __attribute__ ((__nothrow__));
extern __pid_t vfork (void) __attribute__ ((__nothrow__ , __leaf__));
extern __pid_t _Fork (void) __attribute__ ((__nothrow__ , __leaf__));
extern char *ttyname (int __fd) __attribute__ ((__nothrow__ , __leaf__));
extern int ttyname_r (int __fd, char *__buf, size_t __buflen)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)))
     __attribute__ ((__access__ (__write_only__, 2, 3)));
extern int isatty (int __fd) __attribute__ ((__nothrow__ , __leaf__));
extern int ttyslot (void) __attribute__ ((__nothrow__ , __leaf__));
extern int link (const char *__from, const char *__to)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2))) ;
extern int linkat (int __fromfd, const char *__from, int __tofd,
     const char *__to, int __flags)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 4))) ;
extern int symlink (const char *__from, const char *__to)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2))) ;
extern ssize_t readlink (const char *__restrict __path,
    char *__restrict __buf, size_t __len)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)))
     __attribute__ ((__access__ (__write_only__, 2, 3)));
extern int symlinkat (const char *__from, int __tofd,
        const char *__to) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 3))) ;
extern ssize_t readlinkat (int __fd, const char *__restrict __path,
      char *__restrict __buf, size_t __len)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 3)))
     __attribute__ ((__access__ (__write_only__, 3, 4)));
extern int unlink (const char *__name) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int unlinkat (int __fd, const char *__name, int __flag)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int rmdir (const char *__path) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern __pid_t tcgetpgrp (int __fd) __attribute__ ((__nothrow__ , __leaf__));
extern int tcsetpgrp (int __fd, __pid_t __pgrp_id) __attribute__ ((__nothrow__ , __leaf__));
extern char *getlogin (void);
extern int getlogin_r (char *__name, size_t __name_len) __attribute__ ((__nonnull__ (1)))
    __attribute__ ((__access__ (__write_only__, 1, 2)));
extern int setlogin (const char *__name) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));

extern char *optarg;
extern int optind;
extern int opterr;
extern int optopt;
extern int getopt (int ___argc, char *const *___argv, const char *__shortopts)
       __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 3)));



extern int gethostname (char *__name, size_t __len) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)))
    __attribute__ ((__access__ (__write_only__, 1, 2)));
extern int sethostname (const char *__name, size_t __len)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) __attribute__ ((__access__ (__read_only__, 1, 2)));
extern int sethostid (long int __id) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int getdomainname (char *__name, size_t __len)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)))
     __attribute__ ((__access__ (__write_only__, 1, 2)));
extern int setdomainname (const char *__name, size_t __len)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) __attribute__ ((__access__ (__read_only__, 1, 2)));
extern int vhangup (void) __attribute__ ((__nothrow__ , __leaf__));
extern int revoke (const char *__file) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int profil (unsigned short int *__sample_buffer, size_t __size,
     size_t __offset, unsigned int __scale)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int acct (const char *__name) __attribute__ ((__nothrow__ , __leaf__));
extern char *getusershell (void) __attribute__ ((__nothrow__ , __leaf__));
extern void endusershell (void) __attribute__ ((__nothrow__ , __leaf__));
extern void setusershell (void) __attribute__ ((__nothrow__ , __leaf__));
extern int daemon (int __nochdir, int __noclose) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int chroot (const char *__path) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern char *getpass (const char *__prompt) __attribute__ ((__nonnull__ (1)));
extern int fsync (int __fd);
extern int syncfs (int __fd) __attribute__ ((__nothrow__ , __leaf__));
extern long int gethostid (void);
extern void sync (void) __attribute__ ((__nothrow__ , __leaf__));
extern int getpagesize (void) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int getdtablesize (void) __attribute__ ((__nothrow__ , __leaf__));
extern int truncate (const char *__file, __off64_t __length) __asm__ ("" "truncate64") __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int truncate64 (const char *__file, __off64_t __length)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int ftruncate (int __fd, __off64_t __length) __asm__ ("" "ftruncate64") __attribute__ ((__nothrow__ , __leaf__)) ;
extern int ftruncate64 (int __fd, __off64_t __length) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int brk (void *__addr) __attribute__ ((__nothrow__ , __leaf__)) ;
extern void *sbrk (intptr_t __delta) __attribute__ ((__nothrow__ , __leaf__));
extern long int syscall (long int __sysno, ...) __attribute__ ((__nothrow__ , __leaf__));
extern int lockf (int __fd, int __cmd, __off64_t __len) __asm__ ("" "lockf64") ;
extern int lockf64 (int __fd, int __cmd, __off64_t __len) ;
ssize_t copy_file_range (int __infd, __off64_t *__pinoff,
    int __outfd, __off64_t *__poutoff,
    size_t __length, unsigned int __flags);
extern int fdatasync (int __fildes);
extern char *crypt (const char *__key, const char *__salt)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern void swab (const void *__restrict __from, void *__restrict __to,
    ssize_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)))
    __attribute__ ((__access__ (__read_only__, 1, 3)))
    __attribute__ ((__access__ (__write_only__, 2, 3)));
int getentropy (void *__buffer, size_t __length)
    __attribute__ ((__access__ (__write_only__, 1, 2)));
extern int close_range (unsigned int __fd, unsigned int __max_fd,
   int __flags) __attribute__ ((__nothrow__ , __leaf__));
extern __pid_t gettid (void) __attribute__ ((__nothrow__ , __leaf__));

enum
{
  SS_ONSTACK = 1,
  SS_DISABLE
};
extern int sigaltstack (const stack_t *__restrict __ss,
   stack_t *__restrict __oss) __attribute__ ((__nothrow__ , __leaf__));
struct sigstack
  {
    void *ss_sp;
    int ss_onstack;
  };
extern int sigstack (struct sigstack *__ss, struct sigstack *__oss)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__deprecated__));
extern int sighold (int __sig) __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__deprecated__ ("Use the sigprocmask function instead")));
extern int sigrelse (int __sig) __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__deprecated__ ("Use the sigprocmask function instead")));
extern int sigignore (int __sig) __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__deprecated__ ("Use the signal function instead")));
extern __sighandler_t sigset (int __sig, __sighandler_t __disp) __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__deprecated__ ("Use the signal and sigprocmask functions instead")));
extern int pthread_sigmask (int __how,
       const __sigset_t *__restrict __newmask,
       __sigset_t *__restrict __oldmask)__attribute__ ((__nothrow__ , __leaf__));
extern int pthread_kill (pthread_t __threadid, int __signo) __attribute__ ((__nothrow__ , __leaf__));
extern int pthread_sigqueue (pthread_t __threadid, int __signo,
        const union sigval __value) __attribute__ ((__nothrow__ , __leaf__));
extern int __libc_current_sigrtmin (void) __attribute__ ((__nothrow__ , __leaf__));
extern int __libc_current_sigrtmax (void) __attribute__ ((__nothrow__ , __leaf__));
extern int tgkill (__pid_t __tgid, __pid_t __tid, int __signal);

typedef enum
{
  P_ALL,
  P_PID,
  P_PGID,
  P_PIDFD,
} idtype_t;
extern __pid_t wait (int *__stat_loc);
extern __pid_t waitpid (__pid_t __pid, int *__stat_loc, int __options);
extern int waitid (idtype_t __idtype, __id_t __id, siginfo_t *__infop,
     int __options);
struct rusage;
extern __pid_t wait3 (int *__stat_loc, int __options,
        struct rusage * __usage) __attribute__ ((__nothrow__));
extern __pid_t wait4 (__pid_t __pid, int *__stat_loc, int __options,
        struct rusage *__usage) __attribute__ ((__nothrow__));


extern long int __sysconf (int __name) __attribute__ ((__nothrow__ , __leaf__));

typedef __uint8_t uint8_t;
typedef __uint16_t uint16_t;
typedef __uint32_t uint32_t;
typedef __uint64_t uint64_t;

typedef uint32_t in_addr_t;
struct in_addr
  {
    in_addr_t s_addr;
  };
struct ip_opts
  {
    struct in_addr ip_dst;
    char ip_opts[40];
  };
struct in_pktinfo
  {
    int ipi_ifindex;
    struct in_addr ipi_spec_dst;
    struct in_addr ipi_addr;
  };
enum
  {
    IPPROTO_IP = 0,
    IPPROTO_ICMP = 1,
    IPPROTO_IGMP = 2,
    IPPROTO_IPIP = 4,
    IPPROTO_TCP = 6,
    IPPROTO_EGP = 8,
    IPPROTO_PUP = 12,
    IPPROTO_UDP = 17,
    IPPROTO_IDP = 22,
    IPPROTO_TP = 29,
    IPPROTO_DCCP = 33,
    IPPROTO_IPV6 = 41,
    IPPROTO_RSVP = 46,
    IPPROTO_GRE = 47,
    IPPROTO_ESP = 50,
    IPPROTO_AH = 51,
    IPPROTO_MTP = 92,
    IPPROTO_BEETPH = 94,
    IPPROTO_ENCAP = 98,
    IPPROTO_PIM = 103,
    IPPROTO_COMP = 108,
    IPPROTO_L2TP = 115,
    IPPROTO_SCTP = 132,
    IPPROTO_UDPLITE = 136,
    IPPROTO_MPLS = 137,
    IPPROTO_ETHERNET = 143,
    IPPROTO_RAW = 255,
    IPPROTO_SMC = 256,
    IPPROTO_MPTCP = 262,
    IPPROTO_MAX
  };
enum
  {
    IPPROTO_HOPOPTS = 0,
    IPPROTO_ROUTING = 43,
    IPPROTO_FRAGMENT = 44,
    IPPROTO_ICMPV6 = 58,
    IPPROTO_NONE = 59,
    IPPROTO_DSTOPTS = 60,
    IPPROTO_MH = 135
  };
typedef uint16_t in_port_t;
enum
  {
    IPPORT_ECHO = 7,
    IPPORT_DISCARD = 9,
    IPPORT_SYSTAT = 11,
    IPPORT_DAYTIME = 13,
    IPPORT_NETSTAT = 15,
    IPPORT_FTP = 21,
    IPPORT_TELNET = 23,
    IPPORT_SMTP = 25,
    IPPORT_TIMESERVER = 37,
    IPPORT_NAMESERVER = 42,
    IPPORT_WHOIS = 43,
    IPPORT_MTP = 57,
    IPPORT_TFTP = 69,
    IPPORT_RJE = 77,
    IPPORT_FINGER = 79,
    IPPORT_TTYLINK = 87,
    IPPORT_SUPDUP = 95,
    IPPORT_EXECSERVER = 512,
    IPPORT_LOGINSERVER = 513,
    IPPORT_CMDSERVER = 514,
    IPPORT_EFSSERVER = 520,
    IPPORT_BIFFUDP = 512,
    IPPORT_WHOSERVER = 513,
    IPPORT_ROUTESERVER = 520,
    IPPORT_RESERVED = 1024,
    IPPORT_USERRESERVED = 5000
  };
struct in6_addr
  {
    union
      {
 uint8_t __u6_addr8[16];
 uint16_t __u6_addr16[8];
 uint32_t __u6_addr32[4];
      } __in6_u;
  };
extern const struct in6_addr in6addr_any;
extern const struct in6_addr in6addr_loopback;
struct __attribute__ ((__may_alias__)) sockaddr_in
  {
    sa_family_t sin_family;
    in_port_t sin_port;
    struct in_addr sin_addr;
    unsigned char sin_zero[sizeof (struct sockaddr)
      - (sizeof (unsigned short int))
      - sizeof (in_port_t)
      - sizeof (struct in_addr)];
  };
struct __attribute__ ((__may_alias__)) sockaddr_in6
  {
    sa_family_t sin6_family;
    in_port_t sin6_port;
    uint32_t sin6_flowinfo;
    struct in6_addr sin6_addr;
    uint32_t sin6_scope_id;
  };
struct ip_mreq
  {
    struct in_addr imr_multiaddr;
    struct in_addr imr_interface;
  };
struct ip_mreqn
  {
    struct in_addr imr_multiaddr;
    struct in_addr imr_address;
    int imr_ifindex;
  };
struct ip_mreq_source
  {
    struct in_addr imr_multiaddr;
    struct in_addr imr_interface;
    struct in_addr imr_sourceaddr;
  };
struct ipv6_mreq
  {
    struct in6_addr ipv6mr_multiaddr;
    unsigned int ipv6mr_interface;
  };
struct group_req
  {
    uint32_t gr_interface;
    struct sockaddr_storage gr_group;
  };
struct group_source_req
  {
    uint32_t gsr_interface;
    struct sockaddr_storage gsr_group;
    struct sockaddr_storage gsr_source;
  };
struct ip_msfilter
  {
    struct in_addr imsf_multiaddr;
    struct in_addr imsf_interface;
    uint32_t imsf_fmode;
    uint32_t imsf_numsrc;
    struct in_addr imsf_slist[1];
  };
struct group_filter
  {
    uint32_t gf_interface;
    struct sockaddr_storage gf_group;
    uint32_t gf_fmode;
    uint32_t gf_numsrc;
    struct sockaddr_storage gf_slist[1];
};
extern uint32_t ntohl (uint32_t __netlong) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern uint16_t ntohs (uint16_t __netshort)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern uint32_t htonl (uint32_t __hostlong)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern uint16_t htons (uint16_t __hostshort)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int bindresvport (int __sockfd, struct sockaddr_in *__sock_in) __attribute__ ((__nothrow__ , __leaf__));
extern int bindresvport6 (int __sockfd, struct sockaddr_in6 *__sock_in)
     __attribute__ ((__nothrow__ , __leaf__));
struct cmsghdr;
struct in6_pktinfo
  {
    struct in6_addr ipi6_addr;
    unsigned int ipi6_ifindex;
  };
struct ip6_mtuinfo
  {
    struct sockaddr_in6 ip6m_addr;
    uint32_t ip6m_mtu;
  };
extern int inet6_option_space (int __nbytes)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__deprecated__));
extern int inet6_option_init (void *__bp, struct cmsghdr **__cmsgp,
         int __type) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__deprecated__));
extern int inet6_option_append (struct cmsghdr *__cmsg,
    const uint8_t *__typep, int __multx,
    int __plusy) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__deprecated__));
extern uint8_t *inet6_option_alloc (struct cmsghdr *__cmsg, int __datalen,
        int __multx, int __plusy)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__deprecated__));
extern int inet6_option_next (const struct cmsghdr *__cmsg,
         uint8_t **__tptrp)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__deprecated__));
extern int inet6_option_find (const struct cmsghdr *__cmsg,
         uint8_t **__tptrp, int __type)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__deprecated__));
extern int inet6_opt_init (void *__extbuf, socklen_t __extlen) __attribute__ ((__nothrow__ , __leaf__));
extern int inet6_opt_append (void *__extbuf, socklen_t __extlen, int __offset,
        uint8_t __type, socklen_t __len, uint8_t __align,
        void **__databufp) __attribute__ ((__nothrow__ , __leaf__));
extern int inet6_opt_finish (void *__extbuf, socklen_t __extlen, int __offset)
     __attribute__ ((__nothrow__ , __leaf__));
extern int inet6_opt_set_val (void *__databuf, int __offset, void *__val,
         socklen_t __vallen) __attribute__ ((__nothrow__ , __leaf__));
extern int inet6_opt_next (void *__extbuf, socklen_t __extlen, int __offset,
      uint8_t *__typep, socklen_t *__lenp,
      void **__databufp) __attribute__ ((__nothrow__ , __leaf__));
extern int inet6_opt_find (void *__extbuf, socklen_t __extlen, int __offset,
      uint8_t __type, socklen_t *__lenp,
      void **__databufp) __attribute__ ((__nothrow__ , __leaf__));
extern int inet6_opt_get_val (void *__databuf, int __offset, void *__val,
         socklen_t __vallen) __attribute__ ((__nothrow__ , __leaf__));
extern socklen_t inet6_rth_space (int __type, int __segments) __attribute__ ((__nothrow__ , __leaf__));
extern void *inet6_rth_init (void *__bp, socklen_t __bp_len, int __type,
        int __segments) __attribute__ ((__nothrow__ , __leaf__));
extern int inet6_rth_add (void *__bp, const struct in6_addr *__addr) __attribute__ ((__nothrow__ , __leaf__));
extern int inet6_rth_reverse (const void *__in, void *__out) __attribute__ ((__nothrow__ , __leaf__));
extern int inet6_rth_segments (const void *__bp) __attribute__ ((__nothrow__ , __leaf__));
extern struct in6_addr *inet6_rth_getaddr (const void *__bp, int __index)
     __attribute__ ((__nothrow__ , __leaf__));
extern int getipv4sourcefilter (int __s, struct in_addr __interface_addr,
    struct in_addr __group, uint32_t *__fmode,
    uint32_t *__numsrc, struct in_addr *__slist)
     __attribute__ ((__nothrow__ , __leaf__));
extern int setipv4sourcefilter (int __s, struct in_addr __interface_addr,
    struct in_addr __group, uint32_t __fmode,
    uint32_t __numsrc,
    const struct in_addr *__slist)
     __attribute__ ((__nothrow__ , __leaf__));
extern int getsourcefilter (int __s, uint32_t __interface_addr,
       const struct sockaddr *__group,
       socklen_t __grouplen, uint32_t *__fmode,
       uint32_t *__numsrc,
       struct sockaddr_storage *__slist) __attribute__ ((__nothrow__ , __leaf__));
extern int setsourcefilter (int __s, uint32_t __interface_addr,
       const struct sockaddr *__group,
       socklen_t __grouplen, uint32_t __fmode,
       uint32_t __numsrc,
       const struct sockaddr_storage *__slist) __attribute__ ((__nothrow__ , __leaf__));

typedef __int_least8_t int_least8_t;
typedef __int_least16_t int_least16_t;
typedef __int_least32_t int_least32_t;
typedef __int_least64_t int_least64_t;
typedef __uint_least8_t uint_least8_t;
typedef __uint_least16_t uint_least16_t;
typedef __uint_least32_t uint_least32_t;
typedef __uint_least64_t uint_least64_t;
typedef signed char int_fast8_t;
typedef long int int_fast16_t;
typedef long int int_fast32_t;
typedef long int int_fast64_t;
typedef unsigned char uint_fast8_t;
typedef unsigned long int uint_fast16_t;
typedef unsigned long int uint_fast32_t;
typedef unsigned long int uint_fast64_t;
typedef unsigned long int uintptr_t;
typedef __intmax_t intmax_t;
typedef __uintmax_t uintmax_t;
typedef uint32_t tcp_seq;
struct tcphdr
  {
    __extension__ union
    {
      struct
      {
 uint16_t th_sport;
 uint16_t th_dport;
 tcp_seq th_seq;
 tcp_seq th_ack;
 uint8_t th_x2:4;
 uint8_t th_off:4;
 uint8_t th_flags;
 uint16_t th_win;
 uint16_t th_sum;
 uint16_t th_urp;
      };
      struct
      {
 uint16_t source;
 uint16_t dest;
 uint32_t seq;
 uint32_t ack_seq;
 uint16_t res1:4;
 uint16_t doff:4;
 uint16_t fin:1;
 uint16_t syn:1;
 uint16_t rst:1;
 uint16_t psh:1;
 uint16_t ack:1;
 uint16_t urg:1;
 uint16_t res2:2;
 uint16_t window;
 uint16_t check;
 uint16_t urg_ptr;
      };
    };
};
enum
{
  TCP_ESTABLISHED = 1,
  TCP_SYN_SENT,
  TCP_SYN_RECV,
  TCP_FIN_WAIT1,
  TCP_FIN_WAIT2,
  TCP_TIME_WAIT,
  TCP_CLOSE,
  TCP_CLOSE_WAIT,
  TCP_LAST_ACK,
  TCP_LISTEN,
  TCP_CLOSING
};
enum tcp_ca_state
{
  TCP_CA_Open = 0,
  TCP_CA_Disorder = 1,
  TCP_CA_CWR = 2,
  TCP_CA_Recovery = 3,
  TCP_CA_Loss = 4
};
struct tcp_info
{
  uint8_t tcpi_state;
  uint8_t tcpi_ca_state;
  uint8_t tcpi_retransmits;
  uint8_t tcpi_probes;
  uint8_t tcpi_backoff;
  uint8_t tcpi_options;
  uint8_t tcpi_snd_wscale : 4, tcpi_rcv_wscale : 4;
  uint32_t tcpi_rto;
  uint32_t tcpi_ato;
  uint32_t tcpi_snd_mss;
  uint32_t tcpi_rcv_mss;
  uint32_t tcpi_unacked;
  uint32_t tcpi_sacked;
  uint32_t tcpi_lost;
  uint32_t tcpi_retrans;
  uint32_t tcpi_fackets;
  uint32_t tcpi_last_data_sent;
  uint32_t tcpi_last_ack_sent;
  uint32_t tcpi_last_data_recv;
  uint32_t tcpi_last_ack_recv;
  uint32_t tcpi_pmtu;
  uint32_t tcpi_rcv_ssthresh;
  uint32_t tcpi_rtt;
  uint32_t tcpi_rttvar;
  uint32_t tcpi_snd_ssthresh;
  uint32_t tcpi_snd_cwnd;
  uint32_t tcpi_advmss;
  uint32_t tcpi_reordering;
  uint32_t tcpi_rcv_rtt;
  uint32_t tcpi_rcv_space;
  uint32_t tcpi_total_retrans;
};
struct tcp_md5sig
{
  struct sockaddr_storage tcpm_addr;
  uint8_t tcpm_flags;
  uint8_t tcpm_prefixlen;
  uint16_t tcpm_keylen;
  int tcpm_ifindex;
  uint8_t tcpm_key[80];
};
struct tcp_repair_opt
{
  uint32_t opt_code;
  uint32_t opt_val;
};
enum
{
  TCP_NO_QUEUE,
  TCP_RECV_QUEUE,
  TCP_SEND_QUEUE,
  TCP_QUEUES_NR,
};
struct tcp_cookie_transactions
{
  uint16_t tcpct_flags;
  uint8_t __tcpct_pad1;
  uint8_t tcpct_cookie_desired;
  uint16_t tcpct_s_data_desired;
  uint16_t tcpct_used;
  uint8_t tcpct_value[536U];
};
struct tcp_repair_window
{
  uint32_t snd_wl1;
  uint32_t snd_wnd;
  uint32_t max_window;
  uint32_t rcv_wnd;
  uint32_t rcv_wup;
};
struct tcp_zerocopy_receive
{
  uint64_t address;
  uint32_t length;
  uint32_t recv_skip_hint;
};

extern in_addr_t inet_addr (const char *__cp) __attribute__ ((__nothrow__ , __leaf__));
extern in_addr_t inet_lnaof (struct in_addr __in) __attribute__ ((__nothrow__ , __leaf__));
extern struct in_addr inet_makeaddr (in_addr_t __net, in_addr_t __host)
     __attribute__ ((__nothrow__ , __leaf__));
extern in_addr_t inet_netof (struct in_addr __in) __attribute__ ((__nothrow__ , __leaf__));
extern in_addr_t inet_network (const char *__cp) __attribute__ ((__nothrow__ , __leaf__));
extern char *inet_ntoa (struct in_addr __in) __attribute__ ((__nothrow__ , __leaf__));
extern int inet_pton (int __af, const char *__restrict __cp,
        void *__restrict __buf) __attribute__ ((__nothrow__ , __leaf__));
extern const char *inet_ntop (int __af, const void *__restrict __cp,
         char *__restrict __buf, socklen_t __len)
     __attribute__ ((__nothrow__ , __leaf__));
extern int inet_aton (const char *__cp, struct in_addr *__inp) __attribute__ ((__nothrow__ , __leaf__));
extern char *inet_neta (in_addr_t __net, char *__buf, size_t __len) __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__deprecated__ ("Use inet_ntop instead")));
extern char *inet_net_ntop (int __af, const void *__cp, int __bits,
       char *__buf, size_t __len) __attribute__ ((__nothrow__ , __leaf__));
extern int inet_net_pton (int __af, const char *__cp,
     void *__buf, size_t __len) __attribute__ ((__nothrow__ , __leaf__));
extern unsigned int inet_nsap_addr (const char *__cp,
        unsigned char *__buf, int __len) __attribute__ ((__nothrow__ , __leaf__));
extern char *inet_nsap_ntoa (int __len, const unsigned char *__cp,
        char *__buf) __attribute__ ((__nothrow__ , __leaf__));


enum
{
  _ISupper = ((0) < 8 ? ((1 << (0)) << 8) : ((1 << (0)) >> 8)),
  _ISlower = ((1) < 8 ? ((1 << (1)) << 8) : ((1 << (1)) >> 8)),
  _ISalpha = ((2) < 8 ? ((1 << (2)) << 8) : ((1 << (2)) >> 8)),
  _ISdigit = ((3) < 8 ? ((1 << (3)) << 8) : ((1 << (3)) >> 8)),
  _ISxdigit = ((4) < 8 ? ((1 << (4)) << 8) : ((1 << (4)) >> 8)),
  _ISspace = ((5) < 8 ? ((1 << (5)) << 8) : ((1 << (5)) >> 8)),
  _ISprint = ((6) < 8 ? ((1 << (6)) << 8) : ((1 << (6)) >> 8)),
  _ISgraph = ((7) < 8 ? ((1 << (7)) << 8) : ((1 << (7)) >> 8)),
  _ISblank = ((8) < 8 ? ((1 << (8)) << 8) : ((1 << (8)) >> 8)),
  _IScntrl = ((9) < 8 ? ((1 << (9)) << 8) : ((1 << (9)) >> 8)),
  _ISpunct = ((10) < 8 ? ((1 << (10)) << 8) : ((1 << (10)) >> 8)),
  _ISalnum = ((11) < 8 ? ((1 << (11)) << 8) : ((1 << (11)) >> 8))
};
extern const unsigned short int **__ctype_b_loc (void)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern const __int32_t **__ctype_tolower_loc (void)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern const __int32_t **__ctype_toupper_loc (void)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int isalnum (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isalpha (int) __attribute__ ((__nothrow__ , __leaf__));
extern int iscntrl (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isdigit (int) __attribute__ ((__nothrow__ , __leaf__));
extern int islower (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isgraph (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isprint (int) __attribute__ ((__nothrow__ , __leaf__));
extern int ispunct (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isspace (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isupper (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isxdigit (int) __attribute__ ((__nothrow__ , __leaf__));
extern int tolower (int __c) __attribute__ ((__nothrow__ , __leaf__));
extern int toupper (int __c) __attribute__ ((__nothrow__ , __leaf__));
extern int isblank (int) __attribute__ ((__nothrow__ , __leaf__));
extern int isctype (int __c, int __mask) __attribute__ ((__nothrow__ , __leaf__));
extern int isascii (int __c) __attribute__ ((__nothrow__ , __leaf__));
extern int toascii (int __c) __attribute__ ((__nothrow__ , __leaf__));
extern int _toupper (int) __attribute__ ((__nothrow__ , __leaf__));
extern int _tolower (int) __attribute__ ((__nothrow__ , __leaf__));
struct __locale_struct
{
  struct __locale_data *__locales[13];
  const unsigned short int *__ctype_b;
  const int *__ctype_tolower;
  const int *__ctype_toupper;
  const char *__names[13];
};
typedef struct __locale_struct *__locale_t;
typedef __locale_t locale_t;
extern int isalnum_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isalpha_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int iscntrl_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isdigit_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int islower_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isgraph_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isprint_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int ispunct_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isspace_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isupper_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isxdigit_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int isblank_l (int, locale_t) __attribute__ ((__nothrow__ , __leaf__));
extern int __tolower_l (int __c, locale_t __l) __attribute__ ((__nothrow__ , __leaf__));
extern int tolower_l (int __c, locale_t __l) __attribute__ ((__nothrow__ , __leaf__));
extern int __toupper_l (int __c, locale_t __l) __attribute__ ((__nothrow__ , __leaf__));
extern int toupper_l (int __c, locale_t __l) __attribute__ ((__nothrow__ , __leaf__));


struct dirent
  {
    __ino64_t d_ino;
    __off64_t d_off;
    unsigned short int d_reclen;
    unsigned char d_type;
    char d_name[256];
  };
struct dirent64
  {
    __ino64_t d_ino;
    __off64_t d_off;
    unsigned short int d_reclen;
    unsigned char d_type;
    char d_name[256];
  };
enum
  {
    DT_UNKNOWN = 0,
    DT_FIFO = 1,
    DT_CHR = 2,
    DT_DIR = 4,
    DT_BLK = 6,
    DT_REG = 8,
    DT_LNK = 10,
    DT_SOCK = 12,
    DT_WHT = 14
  };
typedef struct __dirstream DIR;
extern int closedir (DIR *__dirp) __attribute__ ((__nonnull__ (1)));
extern DIR *opendir (const char *__name) __attribute__ ((__nonnull__ (1)))
 __attribute__ ((__malloc__)) __attribute__ ((__malloc__ (closedir, 1)));
extern DIR *fdopendir (int __fd)
 __attribute__ ((__malloc__)) __attribute__ ((__malloc__ (closedir, 1)));
extern struct dirent *readdir (DIR *__dirp) __asm__ ("" "readdir64")
     __attribute__ ((__nonnull__ (1)));
extern struct dirent64 *readdir64 (DIR *__dirp) __attribute__ ((__nonnull__ (1)));
extern int readdir_r (DIR *__restrict __dirp, struct dirent *__restrict __entry, struct dirent **__restrict __result) __asm__ ("" "readdir64_r")
  __attribute__ ((__nonnull__ (1, 2, 3))) __attribute__ ((__deprecated__));
extern int readdir64_r (DIR *__restrict __dirp,
   struct dirent64 *__restrict __entry,
   struct dirent64 **__restrict __result)
  __attribute__ ((__nonnull__ (1, 2, 3))) __attribute__ ((__deprecated__));
extern void rewinddir (DIR *__dirp) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern void seekdir (DIR *__dirp, long int __pos) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern long int telldir (DIR *__dirp) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int dirfd (DIR *__dirp) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int scandir (const char *__restrict __dir, struct dirent ***__restrict __namelist, int (*__selector) (const struct dirent *), int (*__cmp) (const struct dirent **, const struct dirent **)) __asm__ ("" "scandir64") __attribute__ ((__nonnull__ (1, 2)));
extern int scandir64 (const char *__restrict __dir,
        struct dirent64 ***__restrict __namelist,
        int (*__selector) (const struct dirent64 *),
        int (*__cmp) (const struct dirent64 **,
        const struct dirent64 **))
     __attribute__ ((__nonnull__ (1, 2)));
extern int scandirat (int __dfd, const char *__restrict __dir, struct dirent ***__restrict __namelist, int (*__selector) (const struct dirent *), int (*__cmp) (const struct dirent **, const struct dirent **)) __asm__ ("" "scandirat64") __attribute__ ((__nonnull__ (2, 3)));
extern int scandirat64 (int __dfd, const char *__restrict __dir,
   struct dirent64 ***__restrict __namelist,
   int (*__selector) (const struct dirent64 *),
   int (*__cmp) (const struct dirent64 **,
          const struct dirent64 **))
     __attribute__ ((__nonnull__ (2, 3)));
extern int alphasort (const struct dirent **__e1, const struct dirent **__e2) __asm__ ("" "alphasort64") __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern int alphasort64 (const struct dirent64 **__e1,
   const struct dirent64 **__e2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern __ssize_t getdirentries (int __fd, char *__restrict __buf, size_t __nbytes, __off64_t *__restrict __basep) __asm__ ("" "getdirentries64") __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 4)));
extern __ssize_t getdirentries64 (int __fd, char *__restrict __buf,
      size_t __nbytes,
      __off64_t *__restrict __basep)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 4)));
extern int versionsort (const struct dirent **__e1, const struct dirent **__e2) __asm__ ("" "versionsort64") __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern int versionsort64 (const struct dirent64 **__e1,
     const struct dirent64 **__e2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));


extern __ssize_t getdents64 (int __fd, void *__buffer, size_t __length)
  __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));


extern int *__errno_location (void) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern char *program_invocation_name;
extern char *program_invocation_short_name;
typedef int error_t;


struct flock
  {
    short int l_type;
    short int l_whence;
    __off64_t l_start;
    __off64_t l_len;
    __pid_t l_pid;
  };
struct flock64
  {
    short int l_type;
    short int l_whence;
    __off64_t l_start;
    __off64_t l_len;
    __pid_t l_pid;
  };
enum __pid_type
  {
    F_OWNER_TID = 0,
    F_OWNER_PID,
    F_OWNER_PGRP,
    F_OWNER_GID = F_OWNER_PGRP
  };
struct f_owner_ex
  {
    enum __pid_type type;
    __pid_t pid;
  };
struct file_handle
{
  unsigned int handle_bytes;
  int handle_type;
  unsigned char f_handle[0];
};

extern __ssize_t readahead (int __fd, __off64_t __offset, size_t __count)
    __attribute__ ((__nothrow__ , __leaf__));
extern int sync_file_range (int __fd, __off64_t __offset, __off64_t __count,
       unsigned int __flags);
extern __ssize_t vmsplice (int __fdout, const struct iovec *__iov,
      size_t __count, unsigned int __flags);
extern __ssize_t splice (int __fdin, __off64_t *__offin, int __fdout,
    __off64_t *__offout, size_t __len,
    unsigned int __flags);
extern __ssize_t tee (int __fdin, int __fdout, size_t __len,
        unsigned int __flags);
extern int fallocate (int __fd, int __mode, __off64_t __offset, __off64_t __len) __asm__ ("" "fallocate64");
extern int fallocate64 (int __fd, int __mode, __off64_t __offset,
   __off64_t __len);
extern int name_to_handle_at (int __dfd, const char *__name,
         struct file_handle *__handle, int *__mnt_id,
         int __flags) __attribute__ ((__nothrow__ , __leaf__));
extern int open_by_handle_at (int __mountdirfd, struct file_handle *__handle,
         int __flags);

extern int fcntl (int __fd, int __cmd, ...) __asm__ ("" "fcntl64");
extern int fcntl64 (int __fd, int __cmd, ...);
extern int open (const char *__file, int __oflag, ...) __asm__ ("" "open64")
     __attribute__ ((__nonnull__ (1)));
extern int open64 (const char *__file, int __oflag, ...) __attribute__ ((__nonnull__ (1)));
extern int openat (int __fd, const char *__file, int __oflag, ...) __asm__ ("" "openat64") __attribute__ ((__nonnull__ (2)));
extern int openat64 (int __fd, const char *__file, int __oflag, ...)
     __attribute__ ((__nonnull__ (2)));
extern int creat (const char *__file, mode_t __mode) __asm__ ("" "creat64") __attribute__ ((__nonnull__ (1)));
extern int creat64 (const char *__file, mode_t __mode) __attribute__ ((__nonnull__ (1)));
extern int posix_fadvise (int __fd, __off64_t __offset, __off64_t __len, int __advise) __asm__ ("" "posix_fadvise64") __attribute__ ((__nothrow__ , __leaf__));
extern int posix_fadvise64 (int __fd, off64_t __offset, off64_t __len,
       int __advise) __attribute__ ((__nothrow__ , __leaf__));
extern int posix_fallocate (int __fd, __off64_t __offset, __off64_t __len) __asm__ ("" "posix_fallocate64");
extern int posix_fallocate64 (int __fd, off64_t __offset, off64_t __len);


struct group
  {
    char *gr_name;
    char *gr_passwd;
    __gid_t gr_gid;
    char **gr_mem;
  };
struct _IO_FILE;
typedef struct _IO_FILE FILE;
extern void setgrent (void);
extern void endgrent (void);
extern struct group *getgrent (void);
extern struct group *fgetgrent (FILE *__stream);
extern int putgrent (const struct group *__restrict __p,
       FILE *__restrict __f);
extern struct group *getgrgid (__gid_t __gid);
extern struct group *getgrnam (const char *__name);
extern int getgrent_r (struct group *__restrict __resultbuf,
         char *__restrict __buffer, size_t __buflen,
         struct group **__restrict __result)
 __attribute__ ((__access__ (__write_only__, 2, 3)));
extern int getgrgid_r (__gid_t __gid, struct group *__restrict __resultbuf,
         char *__restrict __buffer, size_t __buflen,
         struct group **__restrict __result)
 __attribute__ ((__access__ (__write_only__, 3, 4)));
extern int getgrnam_r (const char *__restrict __name,
         struct group *__restrict __resultbuf,
         char *__restrict __buffer, size_t __buflen,
         struct group **__restrict __result)
 __attribute__ ((__access__ (__write_only__, 3, 4)));
extern int fgetgrent_r (FILE *__restrict __stream,
   struct group *__restrict __resultbuf,
   char *__restrict __buffer, size_t __buflen,
   struct group **__restrict __result)
 __attribute__ ((__access__ (__write_only__, 3, 4)));
extern int setgroups (size_t __n, const __gid_t *__groups) __attribute__ ((__nothrow__ , __leaf__));
extern int getgrouplist (const char *__user, __gid_t __group,
    __gid_t *__groups, int *__ngroups);
extern int initgroups (const char *__user, __gid_t __group);


struct passwd
{
  char *pw_name;
  char *pw_passwd;
  __uid_t pw_uid;
  __gid_t pw_gid;
  char *pw_gecos;
  char *pw_dir;
  char *pw_shell;
};
extern void setpwent (void);
extern void endpwent (void);
extern struct passwd *getpwent (void);
extern struct passwd *fgetpwent (FILE *__stream) __attribute__ ((__nonnull__ (1)));
extern int putpwent (const struct passwd *__restrict __p,
       FILE *__restrict __f);
extern struct passwd *getpwuid (__uid_t __uid);
extern struct passwd *getpwnam (const char *__name) __attribute__ ((__nonnull__ (1)));
extern int getpwent_r (struct passwd *__restrict __resultbuf,
         char *__restrict __buffer, size_t __buflen,
         struct passwd **__restrict __result)
    __attribute__ ((__nonnull__ (1, 2, 4)))
    __attribute__ ((__access__ (__write_only__, 2, 3)));
extern int getpwuid_r (__uid_t __uid,
         struct passwd *__restrict __resultbuf,
         char *__restrict __buffer, size_t __buflen,
         struct passwd **__restrict __result)
    __attribute__ ((__nonnull__ (2, 3, 5)))
    __attribute__ ((__access__ (__write_only__, 3, 4)));
extern int getpwnam_r (const char *__restrict __name,
         struct passwd *__restrict __resultbuf,
         char *__restrict __buffer, size_t __buflen,
         struct passwd **__restrict __result)
    __attribute__ ((__nonnull__ (1, 2, 3, 5)))
    __attribute__ ((__access__ (__write_only__, 3, 4)));
extern int fgetpwent_r (FILE *__restrict __stream,
   struct passwd *__restrict __resultbuf,
   char *__restrict __buffer, size_t __buflen,
   struct passwd **__restrict __result)
    __attribute__ ((__nonnull__ (1, 2, 3, 5)))
    __attribute__ ((__access__ (__write_only__, 3, 4)));
extern int getpw (__uid_t __uid, char *__buffer);

typedef __builtin_va_list __gnuc_va_list;
typedef __gnuc_va_list va_list;

typedef struct
{
  int __count;
  union
  {
    unsigned int __wch;
    char __wchb[4];
  } __value;
} __mbstate_t;
typedef struct _G_fpos_t
{
  __off_t __pos;
  __mbstate_t __state;
} __fpos_t;
typedef struct _G_fpos64_t
{
  __off64_t __pos;
  __mbstate_t __state;
} __fpos64_t;
struct _IO_FILE;
typedef struct _IO_FILE __FILE;
struct _IO_FILE;
struct _IO_marker;
struct _IO_codecvt;
struct _IO_wide_data;
typedef void _IO_lock_t;
struct _IO_FILE
{
  int _flags;
  char *_IO_read_ptr;
  char *_IO_read_end;
  char *_IO_read_base;
  char *_IO_write_base;
  char *_IO_write_ptr;
  char *_IO_write_end;
  char *_IO_buf_base;
  char *_IO_buf_end;
  char *_IO_save_base;
  char *_IO_backup_base;
  char *_IO_save_end;
  struct _IO_marker *_markers;
  struct _IO_FILE *_chain;
  int _fileno;
  int _flags2:24;
  char _short_backupbuf[1];
  __off_t _old_offset;
  unsigned short _cur_column;
  signed char _vtable_offset;
  char _shortbuf[1];
  _IO_lock_t *_lock;
  __off64_t _offset;
  struct _IO_codecvt *_codecvt;
  struct _IO_wide_data *_wide_data;
  struct _IO_FILE *_freeres_list;
  void *_freeres_buf;
  struct _IO_FILE **_prevchain;
  int _mode;
  char _unused2[15 * sizeof (int) - 5 * sizeof (void *)];
};
typedef __ssize_t cookie_read_function_t (void *__cookie, char *__buf,
                                          size_t __nbytes);
typedef __ssize_t cookie_write_function_t (void *__cookie, const char *__buf,
                                           size_t __nbytes);
typedef int cookie_seek_function_t (void *__cookie, __off64_t *__pos, int __w);
typedef int cookie_close_function_t (void *__cookie);
typedef struct _IO_cookie_io_functions_t
{
  cookie_read_function_t *read;
  cookie_write_function_t *write;
  cookie_seek_function_t *seek;
  cookie_close_function_t *close;
} cookie_io_functions_t;
typedef __fpos64_t fpos_t;
typedef __fpos64_t fpos64_t;
extern FILE *stdin;
extern FILE *stdout;
extern FILE *stderr;
extern int remove (const char *__filename) __attribute__ ((__nothrow__ , __leaf__));
extern int rename (const char *__old, const char *__new) __attribute__ ((__nothrow__ , __leaf__));
extern int renameat (int __oldfd, const char *__old, int __newfd,
       const char *__new) __attribute__ ((__nothrow__ , __leaf__));
extern int renameat2 (int __oldfd, const char *__old, int __newfd,
        const char *__new, unsigned int __flags) __attribute__ ((__nothrow__ , __leaf__));
extern int fclose (FILE *__stream) __attribute__ ((__nonnull__ (1)));
extern FILE *tmpfile (void) __asm__ ("" "tmpfile64")
  __attribute__ ((__malloc__)) __attribute__ ((__malloc__ (fclose, 1))) ;
extern FILE *tmpfile64 (void)
   __attribute__ ((__malloc__)) __attribute__ ((__malloc__ (fclose, 1))) ;
extern char *tmpnam (char[20]) __attribute__ ((__nothrow__ , __leaf__)) ;
extern char *tmpnam_r (char __s[20]) __attribute__ ((__nothrow__ , __leaf__)) ;
extern char *tempnam (const char *__dir, const char *__pfx)
   __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) __attribute__ ((__malloc__ (__builtin_free, 1)));
extern int fflush (FILE *__stream);
extern int fflush_unlocked (FILE *__stream);
extern int fcloseall (void);
extern FILE *fopen (const char *__restrict __filename, const char *__restrict __modes) __asm__ ("" "fopen64")
  __attribute__ ((__malloc__)) __attribute__ ((__malloc__ (fclose, 1))) ;
extern FILE *freopen (const char *__restrict __filename, const char *__restrict __modes, FILE *__restrict __stream) __asm__ ("" "freopen64")
  __attribute__ ((__nonnull__ (3)));
extern FILE *fopen64 (const char *__restrict __filename,
        const char *__restrict __modes)
  __attribute__ ((__malloc__)) __attribute__ ((__malloc__ (fclose, 1))) ;
extern FILE *freopen64 (const char *__restrict __filename,
   const char *__restrict __modes,
   FILE *__restrict __stream) __attribute__ ((__nonnull__ (3)));
extern FILE *fdopen (int __fd, const char *__modes) __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__malloc__)) __attribute__ ((__malloc__ (fclose, 1))) ;
extern FILE *fopencookie (void *__restrict __magic_cookie,
     const char *__restrict __modes,
     cookie_io_functions_t __io_funcs) __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__malloc__)) __attribute__ ((__malloc__ (fclose, 1))) ;
extern FILE *fmemopen (void *__s, size_t __len, const char *__modes)
  __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) __attribute__ ((__malloc__ (fclose, 1))) ;
extern FILE *open_memstream (char **__bufloc, size_t *__sizeloc) __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__malloc__)) __attribute__ ((__malloc__ (fclose, 1))) ;
extern void setbuf (FILE *__restrict __stream, char *__restrict __buf) __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__nonnull__ (1)));
extern int setvbuf (FILE *__restrict __stream, char *__restrict __buf,
      int __modes, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern void setbuffer (FILE *__restrict __stream, char *__restrict __buf,
         size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern void setlinebuf (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int fprintf (FILE *__restrict __stream,
      const char *__restrict __format, ...) __attribute__ ((__nonnull__ (1)));
extern int printf (const char *__restrict __format, ...);
extern int sprintf (char *__restrict __s,
      const char *__restrict __format, ...) __attribute__ ((__nothrow__));
extern int vfprintf (FILE *__restrict __s, const char *__restrict __format,
       __gnuc_va_list __arg) __attribute__ ((__nonnull__ (1)));
extern int vprintf (const char *__restrict __format, __gnuc_va_list __arg);
extern int vsprintf (char *__restrict __s, const char *__restrict __format,
       __gnuc_va_list __arg) __attribute__ ((__nothrow__));
extern int snprintf (char *__restrict __s, size_t __maxlen,
       const char *__restrict __format, ...)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 3, 4)));
extern int vsnprintf (char *__restrict __s, size_t __maxlen,
        const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 3, 0)));
extern int vasprintf (char **__restrict __ptr, const char *__restrict __f,
        __gnuc_va_list __arg)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 2, 0))) ;
extern int __asprintf (char **__restrict __ptr,
         const char *__restrict __fmt, ...)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 2, 3))) ;
extern int asprintf (char **__restrict __ptr,
       const char *__restrict __fmt, ...)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 2, 3))) ;
extern int vdprintf (int __fd, const char *__restrict __fmt,
       __gnuc_va_list __arg)
     __attribute__ ((__format__ (__printf__, 2, 0)));
extern int dprintf (int __fd, const char *__restrict __fmt, ...)
     __attribute__ ((__format__ (__printf__, 2, 3)));
extern int fscanf (FILE *__restrict __stream,
     const char *__restrict __format, ...) __attribute__ ((__nonnull__ (1)));
extern int scanf (const char *__restrict __format, ...) ;
extern int sscanf (const char *__restrict __s,
     const char *__restrict __format, ...) __attribute__ ((__nothrow__ , __leaf__));
extern int fscanf (FILE *__restrict __stream, const char *__restrict __format, ...) __asm__ ("" "__isoc23_fscanf") __attribute__ ((__nonnull__ (1)));
extern int scanf (const char *__restrict __format, ...) __asm__ ("" "__isoc23_scanf") ;
extern int sscanf (const char *__restrict __s, const char *__restrict __format, ...) __asm__ ("" "__isoc23_sscanf") __attribute__ ((__nothrow__ , __leaf__));
extern int vfscanf (FILE *__restrict __s, const char *__restrict __format,
      __gnuc_va_list __arg)
     __attribute__ ((__format__ (__scanf__, 2, 0))) __attribute__ ((__nonnull__ (1)));
extern int vscanf (const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__format__ (__scanf__, 1, 0))) ;
extern int vsscanf (const char *__restrict __s,
      const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__format__ (__scanf__, 2, 0)));
extern int vfscanf (FILE *__restrict __s, const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc23_vfscanf")
     __attribute__ ((__format__ (__scanf__, 2, 0))) __attribute__ ((__nonnull__ (1)));
extern int vscanf (const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc23_vscanf")
     __attribute__ ((__format__ (__scanf__, 1, 0))) ;
extern int vsscanf (const char *__restrict __s, const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc23_vsscanf") __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__format__ (__scanf__, 2, 0)));
extern int fgetc (FILE *__stream) __attribute__ ((__nonnull__ (1)));
extern int getc (FILE *__stream) __attribute__ ((__nonnull__ (1)));
extern int getchar (void);
extern int getc_unlocked (FILE *__stream) __attribute__ ((__nonnull__ (1)));
extern int getchar_unlocked (void);
extern int fgetc_unlocked (FILE *__stream) __attribute__ ((__nonnull__ (1)));
extern int fputc (int __c, FILE *__stream) __attribute__ ((__nonnull__ (2)));
extern int putc (int __c, FILE *__stream) __attribute__ ((__nonnull__ (2)));
extern int putchar (int __c);
extern int fputc_unlocked (int __c, FILE *__stream) __attribute__ ((__nonnull__ (2)));
extern int putc_unlocked (int __c, FILE *__stream) __attribute__ ((__nonnull__ (2)));
extern int putchar_unlocked (int __c);
extern int getw (FILE *__stream) __attribute__ ((__nonnull__ (1)));
extern int putw (int __w, FILE *__stream) __attribute__ ((__nonnull__ (2)));
extern char *fgets (char *__restrict __s, int __n, FILE *__restrict __stream)
     __attribute__ ((__access__ (__write_only__, 1, 2))) __attribute__ ((__nonnull__ (3)));
extern char *fgets_unlocked (char *__restrict __s, int __n,
        FILE *__restrict __stream)
    __attribute__ ((__access__ (__write_only__, 1, 2))) __attribute__ ((__nonnull__ (3)));
extern __ssize_t __getdelim (char **__restrict __lineptr,
                             size_t *__restrict __n, int __delimiter,
                             FILE *__restrict __stream) __attribute__ ((__nonnull__ (4)));
extern __ssize_t getdelim (char **__restrict __lineptr,
                           size_t *__restrict __n, int __delimiter,
                           FILE *__restrict __stream) __attribute__ ((__nonnull__ (4)));
extern __ssize_t getline (char **__restrict __lineptr,
                          size_t *__restrict __n,
                          FILE *__restrict __stream) __attribute__ ((__nonnull__ (3)));
extern int fputs (const char *__restrict __s, FILE *__restrict __stream)
  __attribute__ ((__nonnull__ (2)));
extern int puts (const char *__s);
extern int ungetc (int __c, FILE *__stream) __attribute__ ((__nonnull__ (2)));
extern size_t fread (void *__restrict __ptr, size_t __size,
       size_t __n, FILE *__restrict __stream)
  __attribute__ ((__nonnull__ (4)));
extern size_t fwrite (const void *__restrict __ptr, size_t __size,
        size_t __n, FILE *__restrict __s) __attribute__ ((__nonnull__ (4)));
extern int fputs_unlocked (const char *__restrict __s,
      FILE *__restrict __stream) __attribute__ ((__nonnull__ (2)));
extern size_t fread_unlocked (void *__restrict __ptr, size_t __size,
         size_t __n, FILE *__restrict __stream)
  __attribute__ ((__nonnull__ (4)));
extern size_t fwrite_unlocked (const void *__restrict __ptr, size_t __size,
          size_t __n, FILE *__restrict __stream)
  __attribute__ ((__nonnull__ (4)));
extern int fseek (FILE *__stream, long int __off, int __whence)
  __attribute__ ((__nonnull__ (1)));
extern long int ftell (FILE *__stream) __attribute__ ((__nonnull__ (1)));
extern void rewind (FILE *__stream) __attribute__ ((__nonnull__ (1)));
extern int fseeko (FILE *__stream, __off64_t __off, int __whence) __asm__ ("" "fseeko64") __attribute__ ((__nonnull__ (1)));
extern __off64_t ftello (FILE *__stream) __asm__ ("" "ftello64")
  __attribute__ ((__nonnull__ (1)));
extern int fgetpos (FILE *__restrict __stream, fpos_t *__restrict __pos) __asm__ ("" "fgetpos64")
  __attribute__ ((__nonnull__ (1)));
extern int fsetpos (FILE *__stream, const fpos_t *__pos) __asm__ ("" "fsetpos64")
  __attribute__ ((__nonnull__ (1)));
extern int fseeko64 (FILE *__stream, __off64_t __off, int __whence)
  __attribute__ ((__nonnull__ (1)));
extern __off64_t ftello64 (FILE *__stream) __attribute__ ((__nonnull__ (1)));
extern int fgetpos64 (FILE *__restrict __stream, fpos64_t *__restrict __pos)
  __attribute__ ((__nonnull__ (1)));
extern int fsetpos64 (FILE *__stream, const fpos64_t *__pos) __attribute__ ((__nonnull__ (1)));
extern void clearerr (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int feof (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int ferror (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern void clearerr_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int feof_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int ferror_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern void perror (const char *__s) __attribute__ ((__cold__));
extern int fileno (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int fileno_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int pclose (FILE *__stream) __attribute__ ((__nonnull__ (1)));
extern FILE *popen (const char *__command, const char *__modes)
  __attribute__ ((__malloc__)) __attribute__ ((__malloc__ (pclose, 1))) ;
extern char *ctermid (char *__s) __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__access__ (__write_only__, 1)));
extern char *cuserid (char *__s)
  __attribute__ ((__access__ (__write_only__, 1)));
struct obstack;
extern int obstack_printf (struct obstack *__restrict __obstack,
      const char *__restrict __format, ...)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 2, 3)));
extern int obstack_vprintf (struct obstack *__restrict __obstack,
       const char *__restrict __format,
       __gnuc_va_list __args)
     __attribute__ ((__nothrow__)) __attribute__ ((__format__ (__printf__, 2, 0)));
extern void flockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int ftrylockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern void funlockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int __uflow (FILE *);
extern int __overflow (FILE *, int);

typedef int wchar_t;

typedef struct
  {
    int quot;
    int rem;
  } div_t;
typedef struct
  {
    long int quot;
    long int rem;
  } ldiv_t;
__extension__ typedef struct
  {
    long long int quot;
    long long int rem;
  } lldiv_t;
extern size_t __ctype_get_mb_cur_max (void) __attribute__ ((__nothrow__ , __leaf__)) ;
extern double atof (const char *__nptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1))) ;
extern int atoi (const char *__nptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1))) ;
extern long int atol (const char *__nptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1))) ;
__extension__ extern long long int atoll (const char *__nptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1))) ;
extern double strtod (const char *__restrict __nptr,
        char **__restrict __endptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern float strtof (const char *__restrict __nptr,
       char **__restrict __endptr) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern long double strtold (const char *__restrict __nptr,
       char **__restrict __endptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern _Float32 strtof32 (const char *__restrict __nptr,
     char **__restrict __endptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern _Float64 strtof64 (const char *__restrict __nptr,
     char **__restrict __endptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern _Float128 strtof128 (const char *__restrict __nptr,
       char **__restrict __endptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern _Float32x strtof32x (const char *__restrict __nptr,
       char **__restrict __endptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern _Float64x strtof64x (const char *__restrict __nptr,
       char **__restrict __endptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern long int strtol (const char *__restrict __nptr,
   char **__restrict __endptr, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern unsigned long int strtoul (const char *__restrict __nptr,
      char **__restrict __endptr, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
__extension__
extern long long int strtoq (const char *__restrict __nptr,
        char **__restrict __endptr, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
__extension__
extern unsigned long long int strtouq (const char *__restrict __nptr,
           char **__restrict __endptr, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
__extension__
extern long long int strtoll (const char *__restrict __nptr,
         char **__restrict __endptr, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
__extension__
extern unsigned long long int strtoull (const char *__restrict __nptr,
     char **__restrict __endptr, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern long int strtol (const char *__restrict __nptr, char **__restrict __endptr, int __base) __asm__ ("" "__isoc23_strtol") __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__nonnull__ (1)));
extern unsigned long int strtoul (const char *__restrict __nptr, char **__restrict __endptr, int __base) __asm__ ("" "__isoc23_strtoul") __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__nonnull__ (1)));
__extension__
extern long long int strtoq (const char *__restrict __nptr, char **__restrict __endptr, int __base) __asm__ ("" "__isoc23_strtoll") __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__nonnull__ (1)));
__extension__
extern unsigned long long int strtouq (const char *__restrict __nptr, char **__restrict __endptr, int __base) __asm__ ("" "__isoc23_strtoull") __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__nonnull__ (1)));
__extension__
extern long long int strtoll (const char *__restrict __nptr, char **__restrict __endptr, int __base) __asm__ ("" "__isoc23_strtoll") __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__nonnull__ (1)));
__extension__
extern unsigned long long int strtoull (const char *__restrict __nptr, char **__restrict __endptr, int __base) __asm__ ("" "__isoc23_strtoull") __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__nonnull__ (1)));
extern int strfromd (char *__dest, size_t __size, const char *__format,
       double __f)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3)));
extern int strfromf (char *__dest, size_t __size, const char *__format,
       float __f)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3)));
extern int strfroml (char *__dest, size_t __size, const char *__format,
       long double __f)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3)));
extern int strfromf32 (char *__dest, size_t __size, const char * __format,
         _Float32 __f)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3)));
extern int strfromf64 (char *__dest, size_t __size, const char * __format,
         _Float64 __f)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3)));
extern int strfromf128 (char *__dest, size_t __size, const char * __format,
   _Float128 __f)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3)));
extern int strfromf32x (char *__dest, size_t __size, const char * __format,
   _Float32x __f)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3)));
extern int strfromf64x (char *__dest, size_t __size, const char * __format,
   _Float64x __f)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3)));
extern long int strtol_l (const char *__restrict __nptr,
     char **__restrict __endptr, int __base,
     locale_t __loc) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 4)));
extern unsigned long int strtoul_l (const char *__restrict __nptr,
        char **__restrict __endptr,
        int __base, locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 4)));
__extension__
extern long long int strtoll_l (const char *__restrict __nptr,
    char **__restrict __endptr, int __base,
    locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 4)));
__extension__
extern unsigned long long int strtoull_l (const char *__restrict __nptr,
       char **__restrict __endptr,
       int __base, locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 4)));
extern long int strtol_l (const char *__restrict __nptr, char **__restrict __endptr, int __base, locale_t __loc) __asm__ ("" "__isoc23_strtol_l") __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__nonnull__ (1, 4)));
extern unsigned long int strtoul_l (const char *__restrict __nptr, char **__restrict __endptr, int __base, locale_t __loc) __asm__ ("" "__isoc23_strtoul_l") __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__nonnull__ (1, 4)));
__extension__
extern long long int strtoll_l (const char *__restrict __nptr, char **__restrict __endptr, int __base, locale_t __loc) __asm__ ("" "__isoc23_strtoll_l") __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__nonnull__ (1, 4)));
__extension__
extern unsigned long long int strtoull_l (const char *__restrict __nptr, char **__restrict __endptr, int __base, locale_t __loc) __asm__ ("" "__isoc23_strtoull_l") __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__nonnull__ (1, 4)));
extern double strtod_l (const char *__restrict __nptr,
   char **__restrict __endptr, locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 3)));
extern float strtof_l (const char *__restrict __nptr,
         char **__restrict __endptr, locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 3)));
extern long double strtold_l (const char *__restrict __nptr,
         char **__restrict __endptr,
         locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 3)));
extern _Float32 strtof32_l (const char *__restrict __nptr,
       char **__restrict __endptr,
       locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 3)));
extern _Float64 strtof64_l (const char *__restrict __nptr,
       char **__restrict __endptr,
       locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 3)));
extern _Float128 strtof128_l (const char *__restrict __nptr,
         char **__restrict __endptr,
         locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 3)));
extern _Float32x strtof32x_l (const char *__restrict __nptr,
         char **__restrict __endptr,
         locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 3)));
extern _Float64x strtof64x_l (const char *__restrict __nptr,
         char **__restrict __endptr,
         locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 3)));
extern char *l64a (long int __n) __attribute__ ((__nothrow__ , __leaf__)) ;
extern long int a64l (const char *__s)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1))) ;
extern long int random (void) __attribute__ ((__nothrow__ , __leaf__));
extern void srandom (unsigned int __seed) __attribute__ ((__nothrow__ , __leaf__));
extern char *initstate (unsigned int __seed, char *__statebuf,
   size_t __statelen) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern char *setstate (char *__statebuf) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
struct random_data
  {
    int32_t *fptr;
    int32_t *rptr;
    int32_t *state;
    int rand_type;
    int rand_deg;
    int rand_sep;
    int32_t *end_ptr;
  };
extern int random_r (struct random_data *__restrict __buf,
       int32_t *__restrict __result) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int srandom_r (unsigned int __seed, struct random_data *__buf)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int initstate_r (unsigned int __seed, char *__restrict __statebuf,
   size_t __statelen,
   struct random_data *__restrict __buf)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 4)));
extern int setstate_r (char *__restrict __statebuf,
         struct random_data *__restrict __buf)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int rand (void) __attribute__ ((__nothrow__ , __leaf__));
extern void srand (unsigned int __seed) __attribute__ ((__nothrow__ , __leaf__));
extern int rand_r (unsigned int *__seed) __attribute__ ((__nothrow__ , __leaf__));
extern double drand48 (void) __attribute__ ((__nothrow__ , __leaf__));
extern double erand48 (unsigned short int __xsubi[3]) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern long int lrand48 (void) __attribute__ ((__nothrow__ , __leaf__));
extern long int nrand48 (unsigned short int __xsubi[3])
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern long int mrand48 (void) __attribute__ ((__nothrow__ , __leaf__));
extern long int jrand48 (unsigned short int __xsubi[3])
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern void srand48 (long int __seedval) __attribute__ ((__nothrow__ , __leaf__));
extern unsigned short int *seed48 (unsigned short int __seed16v[3])
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern void lcong48 (unsigned short int __param[7]) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
struct drand48_data
  {
    unsigned short int __x[3];
    unsigned short int __old_x[3];
    unsigned short int __c;
    unsigned short int __init;
    __extension__ unsigned long long int __a;
  };
extern int drand48_r (struct drand48_data *__restrict __buffer,
        double *__restrict __result) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int erand48_r (unsigned short int __xsubi[3],
        struct drand48_data *__restrict __buffer,
        double *__restrict __result) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int lrand48_r (struct drand48_data *__restrict __buffer,
        long int *__restrict __result)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int nrand48_r (unsigned short int __xsubi[3],
        struct drand48_data *__restrict __buffer,
        long int *__restrict __result)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int mrand48_r (struct drand48_data *__restrict __buffer,
        long int *__restrict __result)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int jrand48_r (unsigned short int __xsubi[3],
        struct drand48_data *__restrict __buffer,
        long int *__restrict __result)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int srand48_r (long int __seedval, struct drand48_data *__buffer)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int seed48_r (unsigned short int __seed16v[3],
       struct drand48_data *__buffer) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int lcong48_r (unsigned short int __param[7],
        struct drand48_data *__buffer)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern __uint32_t arc4random (void)
     __attribute__ ((__nothrow__ , __leaf__)) ;
extern void arc4random_buf (void *__buf, size_t __size)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern __uint32_t arc4random_uniform (__uint32_t __upper_bound)
     __attribute__ ((__nothrow__ , __leaf__)) ;
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__))
     __attribute__ ((__alloc_size__ (1))) ;
extern void *calloc (size_t __nmemb, size_t __size)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) __attribute__ ((__alloc_size__ (1, 2))) ;
extern void *realloc (void *__ptr, size_t __size)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__warn_unused_result__)) __attribute__ ((__alloc_size__ (2)));
extern void free (void *__ptr) __attribute__ ((__nothrow__ , __leaf__));
extern void *reallocarray (void *__ptr, size_t __nmemb, size_t __size)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__warn_unused_result__))
     __attribute__ ((__alloc_size__ (2, 3)))
    __attribute__ ((__malloc__ (__builtin_free, 1)));
extern void *reallocarray (void *__ptr, size_t __nmemb, size_t __size)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__ (reallocarray, 1)));

extern void *alloca (size_t __size) __attribute__ ((__nothrow__ , __leaf__));

extern void *valloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__))
     __attribute__ ((__alloc_size__ (1))) ;
extern int posix_memalign (void **__memptr, size_t __alignment, size_t __size)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern void *aligned_alloc (size_t __alignment, size_t __size)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) __attribute__ ((__alloc_align__ (1)))
     __attribute__ ((__alloc_size__ (2))) ;
extern void abort (void) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__)) __attribute__ ((__cold__));
extern int atexit (void (*__func) (void)) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int at_quick_exit (void (*__func) (void)) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int on_exit (void (*__func) (int __status, void *__arg), void *__arg)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern void exit (int __status) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void quick_exit (int __status) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern void _Exit (int __status) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
extern char *getenv (const char *__name) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern char *secure_getenv (const char *__name)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int putenv (char *__string) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int setenv (const char *__name, const char *__value, int __replace)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int unsetenv (const char *__name) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int clearenv (void) __attribute__ ((__nothrow__ , __leaf__));
extern char *mktemp (char *__template) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int mkstemp (char *__template) __asm__ ("" "mkstemp64")
     __attribute__ ((__nonnull__ (1))) ;
extern int mkstemp64 (char *__template) __attribute__ ((__nonnull__ (1))) ;
extern int mkstemps (char *__template, int __suffixlen) __asm__ ("" "mkstemps64") __attribute__ ((__nonnull__ (1))) ;
extern int mkstemps64 (char *__template, int __suffixlen)
     __attribute__ ((__nonnull__ (1))) ;
extern char *mkdtemp (char *__template) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int mkostemp (char *__template, int __flags) __asm__ ("" "mkostemp64")
     __attribute__ ((__nonnull__ (1))) ;
extern int mkostemp64 (char *__template, int __flags) __attribute__ ((__nonnull__ (1))) ;
extern int mkostemps (char *__template, int __suffixlen, int __flags) __asm__ ("" "mkostemps64")
     __attribute__ ((__nonnull__ (1))) ;
extern int mkostemps64 (char *__template, int __suffixlen, int __flags)
     __attribute__ ((__nonnull__ (1))) ;
extern int system (const char *__command) ;
extern char *canonicalize_file_name (const char *__name)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) __attribute__ ((__malloc__))
     __attribute__ ((__malloc__ (__builtin_free, 1))) ;
extern char *realpath (const char *__restrict __name,
         char *__restrict __resolved) __attribute__ ((__nothrow__ , __leaf__)) ;
typedef int (*__compar_fn_t) (const void *, const void *);
typedef __compar_fn_t comparison_fn_t;
typedef int (*__compar_d_fn_t) (const void *, const void *, void *);
extern void *bsearch (const void *__key, const void *__base,
        size_t __nmemb, size_t __size, __compar_fn_t __compar)
     __attribute__ ((__nonnull__ (1, 2, 5))) ;
extern void qsort (void *__base, size_t __nmemb, size_t __size,
     __compar_fn_t __compar) __attribute__ ((__nonnull__ (1, 4)));
extern void qsort_r (void *__base, size_t __nmemb, size_t __size,
       __compar_d_fn_t __compar, void *__arg)
  __attribute__ ((__nonnull__ (1, 4)));
extern int abs (int __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;
extern long int labs (long int __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;
__extension__ extern long long int llabs (long long int __x)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;
extern div_t div (int __numer, int __denom)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;
extern ldiv_t ldiv (long int __numer, long int __denom)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;
__extension__ extern lldiv_t lldiv (long long int __numer,
        long long int __denom)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;
extern char *ecvt (double __value, int __ndigit, int *__restrict __decpt,
     int *__restrict __sign) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4))) ;
extern char *fcvt (double __value, int __ndigit, int *__restrict __decpt,
     int *__restrict __sign) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4))) ;
extern char *gcvt (double __value, int __ndigit, char *__buf)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3))) ;
extern char *qecvt (long double __value, int __ndigit,
      int *__restrict __decpt, int *__restrict __sign)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4))) ;
extern char *qfcvt (long double __value, int __ndigit,
      int *__restrict __decpt, int *__restrict __sign)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4))) ;
extern char *qgcvt (long double __value, int __ndigit, char *__buf)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3))) ;
extern int ecvt_r (double __value, int __ndigit, int *__restrict __decpt,
     int *__restrict __sign, char *__restrict __buf,
     size_t __len) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4, 5)));
extern int fcvt_r (double __value, int __ndigit, int *__restrict __decpt,
     int *__restrict __sign, char *__restrict __buf,
     size_t __len) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4, 5)));
extern int qecvt_r (long double __value, int __ndigit,
      int *__restrict __decpt, int *__restrict __sign,
      char *__restrict __buf, size_t __len)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4, 5)));
extern int qfcvt_r (long double __value, int __ndigit,
      int *__restrict __decpt, int *__restrict __sign,
      char *__restrict __buf, size_t __len)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3, 4, 5)));
extern int mblen (const char *__s, size_t __n) __attribute__ ((__nothrow__ , __leaf__));
extern int mbtowc (wchar_t *__restrict __pwc,
     const char *__restrict __s, size_t __n) __attribute__ ((__nothrow__ , __leaf__));
extern int wctomb (char *__s, wchar_t __wchar) __attribute__ ((__nothrow__ , __leaf__));
extern size_t mbstowcs (wchar_t *__restrict __pwcs,
   const char *__restrict __s, size_t __n) __attribute__ ((__nothrow__ , __leaf__))
    __attribute__ ((__access__ (__read_only__, 2)));
extern size_t wcstombs (char *__restrict __s,
   const wchar_t *__restrict __pwcs, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__access__ (__write_only__, 1, 3)))
  __attribute__ ((__access__ (__read_only__, 2)));
extern int rpmatch (const char *__response) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
extern int getsubopt (char **__restrict __optionp,
        char *const *__restrict __tokens,
        char **__restrict __valuep)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2, 3))) ;
extern int posix_openpt (int __oflag) ;
extern int grantpt (int __fd) __attribute__ ((__nothrow__ , __leaf__));
extern int unlockpt (int __fd) __attribute__ ((__nothrow__ , __leaf__));
extern char *ptsname (int __fd) __attribute__ ((__nothrow__ , __leaf__)) ;
extern int ptsname_r (int __fd, char *__buf, size_t __buflen)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2))) __attribute__ ((__access__ (__write_only__, 2, 3)));
extern int getpt (void);
extern int getloadavg (double __loadavg[], int __nelem)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern void *memcpy (void *__restrict __dest, const void *__restrict __src,
       size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern void *memmove (void *__dest, const void *__src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern void *memccpy (void *__restrict __dest, const void *__restrict __src,
        int __c, size_t __n)
    __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2))) __attribute__ ((__access__ (__write_only__, 1, 4)));
extern void *memset (void *__s, int __c, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int memcmp (const void *__s1, const void *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern int __memcmpeq (const void *__s1, const void *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern void *memchr (const void *__s, int __c, size_t __n)
      __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
extern void *rawmemchr (const void *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
extern void *memrchr (const void *__s, int __c, size_t __n)
      __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)))
      __attribute__ ((__access__ (__read_only__, 1, 3)));
extern char *strcpy (char *__restrict __dest, const char *__restrict __src)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *strncpy (char *__restrict __dest,
        const char *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *strcat (char *__restrict __dest, const char *__restrict __src)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *strncat (char *__restrict __dest, const char *__restrict __src,
        size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern int strcmp (const char *__s1, const char *__s2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern int strncmp (const char *__s1, const char *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern int strcoll (const char *__s1, const char *__s2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern size_t strxfrm (char *__restrict __dest,
         const char *__restrict __src, size_t __n)
    __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2))) __attribute__ ((__access__ (__write_only__, 1, 3)));
extern int strcoll_l (const char *__s1, const char *__s2, locale_t __l)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2, 3)));
extern size_t strxfrm_l (char *__dest, const char *__src, size_t __n,
    locale_t __l) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 4)))
     __attribute__ ((__access__ (__write_only__, 1, 3)));
extern char *strdup (const char *__s)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) __attribute__ ((__nonnull__ (1)));
extern char *strndup (const char *__string, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) __attribute__ ((__nonnull__ (1)));
extern char *strchr (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
extern char *strrchr (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
extern char *strchrnul (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
extern size_t strcspn (const char *__s, const char *__reject)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern size_t strspn (const char *__s, const char *__accept)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *strpbrk (const char *__s, const char *__accept)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *strstr (const char *__haystack, const char *__needle)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *strtok (char *__restrict __s, const char *__restrict __delim)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern char *__strtok_r (char *__restrict __s,
    const char *__restrict __delim,
    char **__restrict __save_ptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 3)));
extern char *strtok_r (char *__restrict __s, const char *__restrict __delim,
         char **__restrict __save_ptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 3)));
extern char *strcasestr (const char *__haystack, const char *__needle)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern void *memmem (const void *__haystack, size_t __haystacklen,
       const void *__needle, size_t __needlelen)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 3)))
    __attribute__ ((__access__ (__read_only__, 1, 2)))
    __attribute__ ((__access__ (__read_only__, 3, 4)));
extern void *__mempcpy (void *__restrict __dest,
   const void *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern void *mempcpy (void *__restrict __dest,
        const void *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern size_t strlen (const char *__s)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
extern size_t strnlen (const char *__string, size_t __maxlen)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
extern char *strerror (int __errnum) __attribute__ ((__nothrow__ , __leaf__));
extern char *strerror_r (int __errnum, char *__buf, size_t __buflen)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2))) __attribute__ ((__access__ (__write_only__, 2, 3)));
extern const char *strerrordesc_np (int __err) __attribute__ ((__nothrow__ , __leaf__));
extern const char *strerrorname_np (int __err) __attribute__ ((__nothrow__ , __leaf__));
extern char *strerror_l (int __errnum, locale_t __l) __attribute__ ((__nothrow__ , __leaf__));

extern int bcmp (const void *__s1, const void *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern void bcopy (const void *__src, void *__dest, size_t __n)
  __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern void bzero (void *__s, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern char *index (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
extern char *rindex (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
extern int ffs (int __i) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int ffsl (long int __l) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
__extension__ extern int ffsll (long long int __ll)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int strcasecmp (const char *__s1, const char *__s2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern int strncasecmp (const char *__s1, const char *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern int strcasecmp_l (const char *__s1, const char *__s2, locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2, 3)));
extern int strncasecmp_l (const char *__s1, const char *__s2,
     size_t __n, locale_t __loc)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2, 4)));

extern void explicit_bzero (void *__s, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)))
    __attribute__ ((__access__ (__write_only__, 1, 2)));
extern char *strsep (char **__restrict __stringp,
       const char *__restrict __delim)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *strsignal (int __sig) __attribute__ ((__nothrow__ , __leaf__));
extern const char *sigabbrev_np (int __sig) __attribute__ ((__nothrow__ , __leaf__));
extern const char *sigdescr_np (int __sig) __attribute__ ((__nothrow__ , __leaf__));
extern char *__stpcpy (char *__restrict __dest, const char *__restrict __src)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *stpcpy (char *__restrict __dest, const char *__restrict __src)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *__stpncpy (char *__restrict __dest,
   const char *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *stpncpy (char *__restrict __dest,
        const char *__restrict __src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
extern size_t strlcpy (char *__restrict __dest,
         const char *__restrict __src, size_t __n)
  __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2))) __attribute__ ((__access__ (__write_only__, 1, 3)));
extern size_t strlcat (char *__restrict __dest,
         const char *__restrict __src, size_t __n)
  __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2))) __attribute__ ((__access__ (__read_write__, 1, 3)));
extern int strverscmp (const char *__s1, const char *__s2)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
extern char *strfry (char *__string) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern void *memfrob (void *__s, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)))
    __attribute__ ((__access__ (__read_write__, 1, 2)));
extern char *basename (const char *__filename) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern void closelog (void);
extern void openlog (const char *__ident, int __option, int __facility);
extern int setlogmask (int __mask) __attribute__ ((__nothrow__ , __leaf__));
extern void syslog (int __pri, const char *__fmt, ...)
     __attribute__ ((__format__ (__printf__, 2, 3)));
extern void vsyslog (int __pri, const char *__fmt, __gnuc_va_list __ap)
     __attribute__ ((__format__ (__printf__, 2, 0)));

struct timex
{
  unsigned int modes;
  __syscall_slong_t offset;
  __syscall_slong_t freq;
  __syscall_slong_t maxerror;
  __syscall_slong_t esterror;
  int status;
  __syscall_slong_t constant;
  __syscall_slong_t precision;
  __syscall_slong_t tolerance;
  struct timeval time;
  __syscall_slong_t tick;
  __syscall_slong_t ppsfreq;
  __syscall_slong_t jitter;
  int shift;
  __syscall_slong_t stabil;
  __syscall_slong_t jitcnt;
  __syscall_slong_t calcnt;
  __syscall_slong_t errcnt;
  __syscall_slong_t stbcnt;
  int tai;
  int :32; int :32; int :32; int :32;
  int :32; int :32; int :32; int :32;
  int :32; int :32; int :32;
};

extern int clock_adjtime (__clockid_t __clock_id, struct timex *__utx) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));

struct tm
{
  int tm_sec;
  int tm_min;
  int tm_hour;
  int tm_mday;
  int tm_mon;
  int tm_year;
  int tm_wday;
  int tm_yday;
  int tm_isdst;
  long int tm_gmtoff;
  const char *tm_zone;
};
struct itimerspec
  {
    struct timespec it_interval;
    struct timespec it_value;
  };
struct sigevent;

extern clock_t clock (void) __attribute__ ((__nothrow__ , __leaf__));
extern time_t time (time_t *__timer) __attribute__ ((__nothrow__ , __leaf__));
extern double difftime (time_t __time1, time_t __time0);
extern time_t mktime (struct tm *__tp) __attribute__ ((__nothrow__ , __leaf__));
extern size_t strftime (char *__restrict __s, size_t __maxsize,
   const char *__restrict __format,
   const struct tm *__restrict __tp)
   __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 3, 4)));
extern char *strptime (const char *__restrict __s,
         const char *__restrict __fmt, struct tm *__tp)
     __attribute__ ((__nothrow__ , __leaf__));
extern size_t strftime_l (char *__restrict __s, size_t __maxsize,
     const char *__restrict __format,
     const struct tm *__restrict __tp,
     locale_t __loc) __attribute__ ((__nothrow__ , __leaf__));
extern char *strptime_l (const char *__restrict __s,
    const char *__restrict __fmt, struct tm *__tp,
    locale_t __loc) __attribute__ ((__nothrow__ , __leaf__));
extern struct tm *gmtime (const time_t *__timer) __attribute__ ((__nothrow__ , __leaf__));
extern struct tm *localtime (const time_t *__timer) __attribute__ ((__nothrow__ , __leaf__));
extern struct tm *gmtime_r (const time_t *__restrict __timer,
       struct tm *__restrict __tp) __attribute__ ((__nothrow__ , __leaf__));
extern struct tm *localtime_r (const time_t *__restrict __timer,
          struct tm *__restrict __tp) __attribute__ ((__nothrow__ , __leaf__));
extern char *asctime (const struct tm *__tp) __attribute__ ((__nothrow__ , __leaf__));
extern char *ctime (const time_t *__timer) __attribute__ ((__nothrow__ , __leaf__));
extern char *asctime_r (const struct tm *__restrict __tp,
   char *__restrict __buf) __attribute__ ((__nothrow__ , __leaf__));
extern char *ctime_r (const time_t *__restrict __timer,
        char *__restrict __buf) __attribute__ ((__nothrow__ , __leaf__));
extern char *__tzname[2];
extern int __daylight;
extern long int __timezone;
extern char *tzname[2];
extern void tzset (void) __attribute__ ((__nothrow__ , __leaf__));
extern int daylight;
extern long int timezone;
extern time_t timegm (struct tm *__tp) __attribute__ ((__nothrow__ , __leaf__));
extern time_t timelocal (struct tm *__tp) __attribute__ ((__nothrow__ , __leaf__));
extern int dysize (int __year) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern int nanosleep (const struct timespec *__requested_time,
        struct timespec *__remaining);
extern int clock_getres (clockid_t __clock_id, struct timespec *__res) __attribute__ ((__nothrow__ , __leaf__));
extern int clock_gettime (clockid_t __clock_id, struct timespec *__tp)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int clock_settime (clockid_t __clock_id, const struct timespec *__tp)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
extern int clock_nanosleep (clockid_t __clock_id, int __flags,
       const struct timespec *__req,
       struct timespec *__rem);
extern int clock_getcpuclockid (pid_t __pid, clockid_t *__clock_id) __attribute__ ((__nothrow__ , __leaf__));
extern int timer_create (clockid_t __clock_id,
    struct sigevent *__restrict __evp,
    timer_t *__restrict __timerid) __attribute__ ((__nothrow__ , __leaf__));
extern int timer_delete (timer_t __timerid) __attribute__ ((__nothrow__ , __leaf__));
extern int timer_settime (timer_t __timerid, int __flags,
     const struct itimerspec *__restrict __value,
     struct itimerspec *__restrict __ovalue) __attribute__ ((__nothrow__ , __leaf__));
extern int timer_gettime (timer_t __timerid, struct itimerspec *__value)
     __attribute__ ((__nothrow__ , __leaf__));
extern int timer_getoverrun (timer_t __timerid) __attribute__ ((__nothrow__ , __leaf__));
extern int timespec_get (struct timespec *__ts, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int timespec_getres (struct timespec *__ts, int __base)
     __attribute__ ((__nothrow__ , __leaf__));
extern int getdate_err;
extern struct tm *getdate (const char *__string);
extern int getdate_r (const char *__restrict __string,
        struct tm *__restrict __resbufp);

typedef char __assert148[(sizeof(unsigned long long) >= sizeof(off_t)) ? 1 : -1];

extern void warn (const char *__format, ...)
     __attribute__ ((__format__ (__printf__, 1, 2))) __attribute__ ((__cold__));
extern void vwarn (const char *__format, __gnuc_va_list)
     __attribute__ ((__format__ (__printf__, 1, 0))) __attribute__ ((__cold__));
extern void warnx (const char *__format, ...)
     __attribute__ ((__format__ (__printf__, 1, 2)));
extern void vwarnx (const char *__format, __gnuc_va_list)
     __attribute__ ((__format__ (__printf__, 1, 0)));
extern void err (int __status, const char *__format, ...)
     __attribute__ ((__noreturn__, __format__ (__printf__, 2, 3))) __attribute__ ((__cold__));
extern void verr (int __status, const char *__format, __gnuc_va_list)
     __attribute__ ((__noreturn__, __format__ (__printf__, 2, 0))) __attribute__ ((__cold__));
extern void errx (int __status, const char *__format, ...)
     __attribute__ ((__noreturn__, __format__ (__printf__, 2, 3))) __attribute__ ((__cold__));
extern void verrx (int __status, const char *, __gnuc_va_list)
     __attribute__ ((__noreturn__, __format__ (__printf__, 2, 0))) __attribute__ ((__cold__));

static struct conn_list_head { struct connection *lh_first; } connlist =
    { ((void *)0) };
struct connection {
    struct { struct connection *le_next; struct connection **le_prev; } entries;
    int socket;
    struct in6_addr client;
    time_t last_active;
    enum {
        RECV_REQUEST,
        SEND_HEADER,
        SEND_REPLY,
        DONE
    } state;
    char *request;
    size_t request_length;
    char *method, *url, *referer, *user_agent, *authorization;
    off_t range_begin, range_end;
    off_t range_begin_given, range_end_given;
    char *header;
    size_t header_length, header_sent;
    int header_dont_free, header_only, http_code, conn_close;
    enum { REPLY_GENERATED, REPLY_FROMFILE } reply_type;
    char *reply;
    int reply_dont_free;
    int reply_fd;
    off_t reply_start, reply_length, reply_sent,
          total_sent;
};
struct forward_mapping {
    const char *host, *target_url;
};
static struct forward_mapping *forward_map = ((void *)0);
static size_t forward_map_size = 0;
static const char *forward_all_url = ((void *)0);
static int forward_to_https = 0;
struct mime_mapping {
    char *extension, *mimetype;
};
static struct mime_mapping *mime_map = ((void *)0);
static size_t mime_map_size = 0;
static size_t longest_ext = 0;
static int timeout_secs = 30;
static char *keep_alive_field = ((void *)0);
static time_t now;
static const char *bindaddr;
static uint16_t bindport = 8080;
static int max_connections = -1;
static const char *index_name = "index.html";
static int no_listing = 0;
static int sockin = -1;
static int inet6 = 0;
static char *wwwroot = ((void *)0);
static char *logfile_name = ((void *)0);
static FILE *logfile = ((void *)0);
static char *pidfile_name = ((void *)0);
static int want_chroot = 0, want_daemon = 0, want_accf = 0,
           want_keepalive = 1, want_server_id = 1, want_single_file = 0,
           want_hide_dotfiles = 0;
static char *server_hdr = ((void *)0);
static char *auth_key = ((void *)0);
static char *custom_hdrs = ((void *)0);
static uint64_t num_requests = 0, total_in = 0, total_out = 0;
static int accepting = 1;
static int syslog_enabled = 0;
volatile int running = 0;
static uid_t drop_uid = ((uid_t) -1);
static gid_t drop_gid = ((gid_t) -1);
static const char *default_extension_map[] = {
    "application/json" " json",
    "application/pdf" " pdf",
    "application/wasm" " wasm",
    "application/xml" " xsl xml",
    "application/xml-dtd" " dtd",
    "application/xslt+xml" " xslt",
    "application/zip" " zip",
    "audio/flac" " flac",
    "audio/mpeg" " mp2 mp3 mpga",
    "audio/ogg" " ogg opus oga spx",
    "audio/wav" " wav",
    "audio/x-m4a" " m4a",
    "font/woff" " woff",
    "font/woff2" " woff2",
    "image/apng" " apng",
    "image/avif" " avif",
    "image/gif" " gif",
    "image/jpeg" " jpeg jpe jpg",
    "image/png" " png",
    "image/svg+xml" " svg",
    "image/webp" " webp",
    "text/css" " css",
    "text/html" " html htm",
    "text/javascript" " js",
    "text/plain" " txt asc",
    "video/mpeg" " mpeg mpe mpg",
    "video/quicktime" " qt mov",
    "video/webm" " webm",
    "video/x-msvideo" " avi",
    "video/mp4" " mp4 m4v",
    ((void *)0)
};
static const char octet_stream[] = "application/octet-stream";
static const char *default_mimetype = octet_stream;
static void poll_recv_request(struct connection *conn);
static void poll_send_header(struct connection *conn);
static void poll_send_reply(struct connection *conn);
static void xclose(const int fd) {
    if (close(fd) == -1)
        err(1, "close()");
}
static void *xmalloc(const size_t size) {
    void *ptr = malloc(size);
    if (ptr == ((void *)0))
        errx(1, "can't allocate %zu bytes", size);
    return ptr;
}
static void *xrealloc(void *original, const size_t size) {
    void *ptr = realloc(original, size);
    if (ptr == ((void *)0))
        errx(1, "can't reallocate %zu bytes", size);
    return ptr;
}
static char *xstrdup(const char *src) {
    size_t len = strlen(src) + 1;
    char *dest = xmalloc(len);
    memcpy(dest, src, len);
    return dest;
}
static unsigned int xvasprintf(char **ret, const char *format, va_list ap)
    __attribute__((__format__(__printf__, 2, 0)));
static unsigned int xvasprintf(char **ret, const char *format, va_list ap) {
    int len = vasprintf(ret, format, ap);
    if (ret == ((void *)0) || len == -1)
        errx(1, "out of memory in vasprintf()");
    return (unsigned int)len;
}
static unsigned int xasprintf(char **ret, const char *format, ...)
    __attribute__((__format__(__printf__, 2, 3)));
static unsigned int xasprintf(char **ret, const char *format, ...) {
    va_list va;
    unsigned int len;
    __builtin_va_start(va,format);
    len = xvasprintf(ret, format, va);
    __builtin_va_end(va);
    return len;
}
struct apbuf {
    size_t length, pool;
    char *str;
};
static struct apbuf *make_apbuf(void) {
    struct apbuf *buf = xmalloc(sizeof(struct apbuf));
    buf->length = 0;
    buf->pool = 4096;
    buf->str = xmalloc(buf->pool);
    return buf;
}
static void appendl(struct apbuf *buf, const char *s, const size_t len) {
    size_t need = buf->length + len;
    if (buf->pool < need) {
        while (buf->pool < need)
            buf->pool += 4096;
        buf->str = xrealloc(buf->str, buf->pool);
    }
    memcpy(buf->str + buf->length, s, len);
    buf->length += len;
}
static void appendf(struct apbuf *buf, const char *format, ...)
    __attribute__((__format__(__printf__, 2, 3)));
static void appendf(struct apbuf *buf, const char *format, ...) {
    char *tmp;
    va_list va;
    size_t len;
    __builtin_va_start(va,format);
    len = xvasprintf(&tmp, format, va);
    __builtin_va_end(va);
    appendl(buf, tmp, len);
    free(tmp);
}
static void nonblock_socket(const int sock) {
    int flags = fcntl(sock, 3);
    if (flags == -1)
        err(1, "fcntl(F_GETFL)");
    flags |= 04000;
    if (fcntl(sock, 4, flags) == -1)
        err(1, "fcntl() to set O_NONBLOCK");
}
static char *split_string(const char *src,
        const size_t left, const size_t right) {
    char *dest;
    ((void) (0));
    dest = xmalloc(right - left + 1);
    memcpy(dest, src+left, right-left);
    dest[right-left] = '\0';
    return dest;
}
static char *make_safe_url(char *const url) {
    char *src = url, *dst;
    if (*src != '/')
        return ((void *)0);
    for ( ; *src; ++src) {
        if (*src == '/') {
            if (src[1] == '/')
                break;
            else if (src[1] == '.') {
                if (((src[2]) == '/' || (src[2]) == '\0'))
                    break;
                else if (src[2] == '.' && ((src[3]) == '/' || (src[3]) == '\0'))
                    break;
            }
        }
    }
    dst = src;
    while (*src) {
        if (*src != '/')
            *dst++ = *src++;
        else if (*++src == '/')
            ;
        else if (*src != '.')
            *dst++ = '/';
        else if (((src[1]) == '/' || (src[1]) == '\0'))
            ++src;
        else if (src[1] == '.' && ((src[2]) == '/' || (src[2]) == '\0')) {
            src += 2;
            if (dst == url)
                return ((void *)0);
            else
                while (*--dst != '/' && dst > url);
        }
        else
            *dst++ = '/';
    }
    if (dst == url)
        ++dst;
    *dst = '\0';
    return url;
}
static void add_forward_mapping(const char * const host,
                                const char * const target_url) {
    forward_map_size++;
    forward_map = xrealloc(forward_map,
                           sizeof(*forward_map) * forward_map_size);
    forward_map[forward_map_size - 1].host = host;
    forward_map[forward_map_size - 1].target_url = target_url;
}
static void add_mime_mapping(const char *extension, const char *mimetype) {
    size_t i;
    ((void) (0));
    ((void) (0));
    i = strlen(extension);
    if (i > longest_ext)
        longest_ext = i;
    for (i = 0; i < mime_map_size; i++)
        if (strcmp(mime_map[i].extension, extension) == 0) {
            free(mime_map[i].mimetype);
            mime_map[i].mimetype = xstrdup(mimetype);
            return;
        }
    mime_map_size++;
    mime_map = xrealloc(mime_map,
        sizeof(struct mime_mapping) * mime_map_size);
    mime_map[mime_map_size - 1].extension = xstrdup(extension);
    mime_map[mime_map_size - 1].mimetype = xstrdup(mimetype);
}
static int mime_mapping_cmp(const void *a, const void *b) {
    return strcmp(((const struct mime_mapping *)a)->extension,
                  ((const struct mime_mapping *)b)->extension);
}
static void sort_mime_map(void) {
    qsort(mime_map, mime_map_size, sizeof(struct mime_mapping),
        mime_mapping_cmp);
}
static void parse_mimetype_line(const char *line) {
    unsigned int pad, bound1, lbound, rbound;
    for (pad=0; (line[pad] == ' ') || (line[pad] == '\t'); pad++)
        ;
    if (line[pad] == '\0' ||
        line[pad] == '#')
        return;
    for (bound1=pad+1;
        (line[bound1] != ' ') &&
        (line[bound1] != '\t');
        bound1++) {
        if (line[bound1] == '\0')
            return;
    }
    lbound = bound1;
    for (;;) {
        char *mimetype, *extension;
        for (; (line[lbound] == ' ') || (line[lbound] == '\t'); lbound++)
            ;
        if (line[lbound] == '\0')
            return;
        for (rbound = lbound;
            line[rbound] != ' ' &&
            line[rbound] != '\t' &&
            line[rbound] != '\0';
            rbound++)
            ;
        mimetype = split_string(line, pad, bound1);
        extension = split_string(line, lbound, rbound);
        add_mime_mapping(extension, mimetype);
        free(mimetype);
        free(extension);
        if (line[rbound] == '\0')
            return;
        else
            lbound = rbound + 1;
    }
}
static void parse_default_extension_map(void) {
    size_t i;
    for (i = 0; default_extension_map[i] != ((void *)0); i++)
        parse_mimetype_line(default_extension_map[i]);
}
static char *read_line(FILE *fp) {
    char *buf;
    long startpos, endpos;
    size_t linelen, numread;
    int c;
    startpos = ftell(fp);
    if (startpos == -1)
        err(1, "ftell()");
    linelen = 0;
    for (;;) {
        c = fgetc(fp);
        if ((c == (-1)) || (c == (int)'\n') || (c == (int)'\r'))
            break;
        linelen++;
    }
    if (linelen == 0 && c == (-1))
        return ((void *)0);
    endpos = ftell(fp);
    if (endpos == -1)
        err(1, "ftell()");
    if ((c == (int)'\r') && (fgetc(fp) == (int)'\n'))
        endpos++;
    buf = xmalloc(linelen + 1);
    if (fseek(fp, startpos, 0) == -1)
        err(1, "fseek()");
    numread = fread(buf, 1, linelen, fp);
    if (numread != linelen)
        errx(1, "fread() %zu bytes, expecting %zu bytes", numread, linelen);
    buf[linelen] = 0;
    if (fseek(fp, endpos, 0) == -1)
        err(1, "fseek()");
    return buf;
}
static void parse_extension_map_file(const char *filename) {
    char *buf;
    FILE *fp = fopen(filename, "rb");
    if (fp == ((void *)0))
        err(1, "fopen(\"%s\")", filename);
    while ((buf = read_line(fp)) != ((void *)0)) {
        parse_mimetype_line(buf);
        free(buf);
    }
    fclose(fp);
}
static int mime_mapping_cmp_str(const void *a, const void *b) {
    return strcmp((const char *)a,
                 ((const struct mime_mapping *)b)->extension);
}
static const char *url_content_type(const char *url) {
    int period, urllen = (int)strlen(url);
    for (period = urllen - 1;
         (period > 0) && (url[period] != '.') &&
         (urllen - period - 1 <= (int)longest_ext);
         period--)
            ;
    if ((period >= 0) && (url[period] == '.')) {
        struct mime_mapping *result =
            bsearch((url + period + 1), mime_map, mime_map_size,
                    sizeof(struct mime_mapping), mime_mapping_cmp_str);
        if (result != ((void *)0)) {
            ((void) (0));
            return result->mimetype;
        }
    }
    return default_mimetype;
}
static const char *get_address_text(const void *addr) {
    if (inet6) {
        static char text_addr[46];
        const struct in6_addr *in6_addr = addr;
        inet_ntop(10, in6_addr, text_addr, 46);
        if ((__extension__ ({ const struct in6_addr *__a = (const struct in6_addr *) (in6_addr); __a->__in6_u.__u6_addr32[0] == 0 && __a->__in6_u.__u6_addr32[1] == 0 && __a->__in6_u.__u6_addr32[2] == htonl (0xffff); })))
            return text_addr + 7;
        return text_addr;
    } else
    {
        return inet_ntoa(*(const struct in_addr *)addr);
    }
}
static void init_sockin(void) {
    struct sockaddr_in addrin;
    struct sockaddr_in6 addrin6;
    socklen_t addrin_len;
    int sockopt;
    if (inet6) {
        memset(&addrin6, 0, sizeof(addrin6));
        if (inet_pton(10, bindaddr ? bindaddr : "::",
                      &addrin6.sin6_addr) != 1) {
            errx(1, "malformed --addr argument");
        }
        sockin = socket(10, SOCK_STREAM, 0);
    } else
    {
        memset(&addrin, 0, sizeof(addrin));
        addrin.sin_addr.s_addr = bindaddr ? inet_addr(bindaddr) : ((in_addr_t) 0x00000000);
        if (addrin.sin_addr.s_addr == (in_addr_t)((in_addr_t) 0xffffffff))
            errx(1, "malformed --addr argument");
        sockin = socket(2, SOCK_STREAM, 0);
    }
    if (sockin == -1)
        err(1, "socket()");
    sockopt = 1;
    if (setsockopt(sockin, 1, 2,
                   &sockopt, sizeof(sockopt)) == -1)
        err(1, "setsockopt(SO_REUSEADDR)");
    sockopt = 1;
    if (setsockopt(sockin, IPPROTO_TCP, 1,
            &sockopt, sizeof(sockopt)) == -1)
        err(1, "setsockopt(TCP_NODELAY)");
    if (inet6) {
        sockopt = 0;
        if (setsockopt(sockin, IPPROTO_IPV6, 26,
                &sockopt, sizeof (sockopt)) < 0)
            err(1, "setsockopt (IPV6_V6ONLY)");
    }
    if (inet6) {
        addrin6.sin6_family = 10;
        addrin6.sin6_port = htons(bindport);
        if (bind(sockin, (struct sockaddr *)&addrin6,
                 sizeof(struct sockaddr_in6)) == -1)
            err(1, "bind(port %u)", bindport);
        addrin_len = sizeof(addrin6);
        if (getsockname(sockin, (struct sockaddr *)&addrin6, &addrin_len) == -1)
            err(1, "getsockname()");
        printf("listening on: http://[%s]:%u/\n",
            get_address_text(&addrin6.sin6_addr), ntohs(addrin6.sin6_port));
    } else
    {
        addrin.sin_family = (u_char)2;
        addrin.sin_port = htons(bindport);
        if (bind(sockin, (struct sockaddr *)&addrin,
                 sizeof(struct sockaddr_in)) == -1)
            err(1, "bind(port %u)", bindport);
        addrin_len = sizeof(addrin);
        if (getsockname(sockin, (struct sockaddr *)&addrin, &addrin_len) == -1)
            err(1, "getsockname()");
        printf("listening on: http://%s:%u/\n",
            get_address_text(&addrin.sin_addr), ntohs(addrin.sin_port));
    }
    if (listen(sockin, max_connections) == -1)
        err(1, "listen()");
    if (want_accf) {
        printf("this platform doesn't support acceptfilter\n");
    }
}
static void usage(const char *argv0) {
    printf("usage:\t%s /path/to/wwwroot [flags]\n\n", argv0);
    printf("flags:\t--port number (default: %u, or 80 if running as root)\n"
    "\t\tSpecifies which port to listen on for connections.\n"
    "\t\tPass 0 to let the system choose any free port for you.\n\n", bindport);
    printf("\t--addr ip (default: all)\n"
    "\t\tIf multiple interfaces are present, specifies\n"
    "\t\twhich one to bind the listening port to.\n\n");
    printf("\t--ipv6\n"
    "\t\tListen on IPv6 address.\n\n");
    printf("\t--daemon (default: don't daemonize)\n"
    "\t\tDetach from the controlling terminal and run in the background.\n\n");
    printf("\t--pidfile filename (default: no pidfile)\n"
    "\t\tWrite PID to the specified file. Note that if you are\n"
    "\t\tusing --chroot, then the pidfile must be relative to,\n"
    "\t\tand inside the wwwroot.\n\n");
    printf("\t--maxconn number (default: system maximum)\n"
    "\t\tSpecifies how many concurrent connections to accept.\n\n");
    printf("\t--log filename (default: stdout)\n"
    "\t\tSpecifies which file to append the request log to.\n\n");
    printf("\t--syslog\n"
    "\t\tUse syslog for request log.\n\n");
    printf("\t--index filename (default: %s)\n"
    "\t\tDefault file to serve when a directory is requested.\n\n",
        index_name);
    printf("\t--no-listing\n"
    "\t\tDo not serve listing if directory is requested.\n\n");
    printf("\t--mimetypes filename (optional)\n"
    "\t\tParses specified file for extension-MIME associations.\n\n");
    printf("\t--default-mimetype string (optional, default: %s)\n"
    "\t\tFiles with unknown extensions are served as this mimetype.\n\n",
        octet_stream);
    printf("\t--uid uid/uname, --gid gid/gname (default: don't privdrop)\n"
    "\t\tDrops privileges to given uid:gid after initialization.\n\n");
    printf("\t--chroot (default: don't chroot)\n"
    "\t\tLocks server into wwwroot directory for added security.\n\n");
    printf("\t--no-keepalive\n"
    "\t\tDisables HTTP Keep-Alive functionality.\n\n");
    printf("\t--single-file\n"
    "\t\tOnly serve a single file provided as /path/to/file instead\n"
    "\t\tof a whole directory.\n\n");
    printf("\t--hide-dotfiles\n"
    "\t\tDon't serve dotfiles.\n\n");
    printf("\t--forward host url (default: don't forward)\n"
    "\t\tWeb forward (301 redirect).\n"
    "\t\tRequests to the host are redirected to the corresponding url.\n"
    "\t\tThe option may be specified multiple times, in which case\n"
    "\t\tthe host is matched in order of appearance.\n\n");
    printf("\t--forward-all url (default: don't forward)\n"
    "\t\tWeb forward (301 redirect).\n"
    "\t\tAll requests are redirected to the corresponding url.\n\n");
    printf("\t--forward-https\n"
    "\t\tIf the client requested HTTP, forward to HTTPS.\n"
    "\t\tThis is useful if darkhttpd is behind a reverse proxy\n"
    "\t\tthat supports SSL.\n\n");
    printf("\t--no-server-id\n"
    "\t\tDon't identify the server type in headers\n"
    "\t\tor directory listings.\n\n");
    printf("\t--timeout secs (default: %d)\n"
    "\t\tIf a connection is idle for more than this many seconds,\n"
    "\t\tit will be closed. Set to zero to disable timeouts.\n\n",
    timeout_secs);
    printf("\t--auth username:password\n"
    "\t\tEnable basic authentication. This is *INSECURE*: passwords\n"
    "\t\tare sent unencrypted over HTTP, plus the password is visible\n"
    "\t\tin ps(1) to other users on the system.\n\n");
    printf("\t--header 'Header: Value'\n"
    "\t\tAdd a custom header to all responses.\n"
    "\t\tThis option can be specified multiple times, in which case\n"
    "\t\tthe headers are added in order of appearance.\n\n");
}
static char *base64_encode(char *str) {
    const char base64_table[] = {
        'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H',
        'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P',
        'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X',
        'Y', 'Z', 'a', 'b', 'c', 'd', 'e', 'f',
        'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n',
        'o', 'p', 'q', 'r', 's', 't', 'u', 'v',
        'w', 'x', 'y', 'z', '0', '1', '2', '3',
        '4', '5', '6', '7', '8', '9', '+', '/'};
    int input_length = strlen(str);
    int output_length = 4 * ((input_length + 2) / 3);
    char *encoded_data = malloc(output_length+1);
    if (encoded_data == ((void *)0)) return ((void *)0);
    int i;
    int j;
    for (i = 0, j = 0; i < input_length;) {
        uint32_t octet_a = i < input_length ? (unsigned char)str[i++] : 0;
        uint32_t octet_b = i < input_length ? (unsigned char)str[i++] : 0;
        uint32_t octet_c = i < input_length ? (unsigned char)str[i++] : 0;
        uint32_t triple = (octet_a << 0x10) + (octet_b << 0x08) + octet_c;
        encoded_data[j++] = base64_table[(triple >> 3 * 6) & 0x3F];
        encoded_data[j++] = base64_table[(triple >> 2 * 6) & 0x3F];
        encoded_data[j++] = base64_table[(triple >> 1 * 6) & 0x3F];
        encoded_data[j++] = base64_table[(triple >> 0 * 6) & 0x3F];
    }
    const int mod_table[] = {0, 2, 1};
    for (i = 0; i < mod_table[input_length % 3]; i++)
        encoded_data[output_length - 1 - i] = '=';
    encoded_data[output_length] = '\0';
    return encoded_data;
}
static int str_to_num(const char *str, long long *num) {
    char *endptr;
    long long n;
    (*__errno_location ()) = 0;
    n = strtoll(str, &endptr, 10);
    if (*endptr != '\0')
        return 0;
    if (n == (-0x7fffffffffffffffLL - 1LL) && (*__errno_location ()) == 34)
        return 0;
    if (n == 0x7fffffffffffffffLL && (*__errno_location ()) == 34)
        return 0;
    if (num != ((void *)0))
        *num = n;
    return 1;
}
static long long xstr_to_num(const char *str) {
    long long ret;
    if (!str_to_num(str, &ret)) {
        errx(1, "number \"%s\" is invalid", str);
    }
    return ret;
}
static void parse_commandline(const int argc, char *argv[]) {
    int i;
    size_t len;
    if ((argc < 2) || (argc == 2 && strcmp(argv[1], "--help") == 0)) {
        usage(argv[0]);
        exit(0);
    }
    if (getuid() == 0)
        bindport = 80;
    custom_hdrs = strdup("");
    wwwroot = xstrdup(argv[1]);
    len = strlen(wwwroot);
    if (len == 0)
        errx(1, "/path/to/wwwroot cannot be empty");
    if (len > 1)
        if (wwwroot[len - 1] == '/')
            wwwroot[len - 1] = '\0';
    for (i = 2; i < argc; i++) {
        if (strcmp(argv[i], "--port") == 0) {
            if (++i >= argc)
                errx(1, "missing number after --port");
            bindport = (uint16_t)xstr_to_num(argv[i]);
        }
        else if (strcmp(argv[i], "--addr") == 0) {
            if (++i >= argc)
                errx(1, "missing ip after --addr");
            bindaddr = argv[i];
        }
        else if (strcmp(argv[i], "--maxconn") == 0) {
            if (++i >= argc)
                errx(1, "missing number after --maxconn");
            max_connections = (int)xstr_to_num(argv[i]);
        }
        else if (strcmp(argv[i], "--log") == 0) {
            if (++i >= argc)
                errx(1, "missing filename after --log");
            logfile_name = argv[i];
        }
        else if (strcmp(argv[i], "--chroot") == 0) {
            want_chroot = 1;
        }
        else if (strcmp(argv[i], "--daemon") == 0) {
            want_daemon = 1;
        }
        else if (strcmp(argv[i], "--index") == 0) {
            if (++i >= argc)
                errx(1, "missing filename after --index");
            index_name = argv[i];
        }
        else if (strcmp(argv[i], "--no-listing") == 0) {
            no_listing = 1;
        }
        else if (strcmp(argv[i], "--mimetypes") == 0) {
            if (++i >= argc)
                errx(1, "missing filename after --mimetypes");
            parse_extension_map_file(argv[i]);
        }
        else if (strcmp(argv[i], "--default-mimetype") == 0) {
            if (++i >= argc)
                errx(1, "missing string after --default-mimetype");
            default_mimetype = argv[i];
        }
        else if (strcmp(argv[i], "--uid") == 0) {
            struct passwd *p;
            if (++i >= argc)
                errx(1, "missing uid after --uid");
            p = getpwnam(argv[i]);
            if (!p) {
                p = getpwuid((uid_t)xstr_to_num(argv[i]));
            }
            if (!p)
                errx(1, "no such uid: `%s'", argv[i]);
            drop_uid = p->pw_uid;
        }
        else if (strcmp(argv[i], "--gid") == 0) {
            struct group *g;
            if (++i >= argc)
                errx(1, "missing gid after --gid");
            g = getgrnam(argv[i]);
            if (!g) {
                g = getgrgid((gid_t)xstr_to_num(argv[i]));
            }
            if (!g) {
                errx(1, "no such gid: `%s'", argv[i]);
            }
            drop_gid = g->gr_gid;
        }
        else if (strcmp(argv[i], "--pidfile") == 0) {
            if (++i >= argc)
                errx(1, "missing filename after --pidfile");
            pidfile_name = argv[i];
        }
        else if (strcmp(argv[i], "--no-keepalive") == 0) {
            want_keepalive = 0;
        }
        else if (strcmp(argv[i], "--accf") == 0) {
            want_accf = 1;
        }
        else if (strcmp(argv[i], "--syslog") == 0) {
            syslog_enabled = 1;
        }
        else if (strcmp(argv[i], "--single-file") == 0) {
            want_single_file = 1;
        }
        else if (strcmp(argv[i], "--hide-dotfiles") == 0) {
            want_hide_dotfiles = 1;
        }
        else if (strcmp(argv[i], "--forward") == 0) {
            const char *host, *url;
            if (++i >= argc)
                errx(1, "missing host after --forward");
            host = argv[i];
            if (++i >= argc)
                errx(1, "missing url after --forward");
            url = argv[i];
            add_forward_mapping(host, url);
        }
        else if (strcmp(argv[i], "--forward-all") == 0) {
            if (++i >= argc)
                errx(1, "missing url after --forward-all");
            forward_all_url = argv[i];
        }
        else if (strcmp(argv[i], "--no-server-id") == 0) {
            want_server_id = 0;
        }
        else if (strcmp(argv[i], "--timeout") == 0) {
            if (++i >= argc)
                errx(1, "missing number after --timeout");
            timeout_secs = (int)xstr_to_num(argv[i]);
        }
        else if (strcmp(argv[i], "--auth") == 0) {
            if (++i >= argc || strchr(argv[i], ':') == ((void *)0))
                errx(1, "missing 'user:pass' after --auth");
            char *key = base64_encode(argv[i]);
            xasprintf(&auth_key, "Basic %s", key);
            free(key);
        }
        else if (strcmp(argv[i], "--forward-https") == 0) {
            forward_to_https = 1;
        }
        else if (strcmp(argv[i], "--header") == 0) {
            if (++i >= argc)
                errx(1, "missing argument after --header");
            if (strchr(argv[i], '\n') != ((void *)0) || strstr(argv[i], ": ") == ((void *)0))
                errx(1, "malformed argument after --header");
            char *old_custom_hdrs = custom_hdrs;
            xasprintf(&custom_hdrs, "%s%s\r\n", old_custom_hdrs, argv[i]);
            free(old_custom_hdrs);
        }
        else if (strcmp(argv[i], "--ipv6") == 0) {
            inet6 = 1;
        }
        else
            errx(1, "unknown argument `%s'", argv[i]);
    }
}
static struct connection *new_connection(void) {
    struct connection *conn = xmalloc(sizeof(struct connection));
    conn->socket = -1;
    memset(&conn->client, 0, sizeof(conn->client));
    conn->last_active = now;
    conn->request = ((void *)0);
    conn->request_length = 0;
    conn->method = ((void *)0);
    conn->url = ((void *)0);
    conn->referer = ((void *)0);
    conn->user_agent = ((void *)0);
    conn->authorization = ((void *)0);
    conn->range_begin = 0;
    conn->range_end = 0;
    conn->range_begin_given = 0;
    conn->range_end_given = 0;
    conn->header = ((void *)0);
    conn->header_length = 0;
    conn->header_sent = 0;
    conn->header_dont_free = 0;
    conn->header_only = 0;
    conn->http_code = 0;
    conn->conn_close = 1;
    conn->reply = ((void *)0);
    conn->reply_dont_free = 0;
    conn->reply_fd = -1;
    conn->reply_start = 0;
    conn->reply_length = 0;
    conn->reply_sent = 0;
    conn->total_sent = 0;
    conn->state = DONE;
    return conn;
}
static void accept_connection(void) {
    struct sockaddr_in addrin;
    struct sockaddr_in6 addrin6;
    socklen_t sin_size;
    struct connection *conn;
    int fd;
    if (inet6) {
        sin_size = sizeof(addrin6);
        memset(&addrin6, 0, sin_size);
        fd = accept(sockin, (struct sockaddr *)&addrin6, &sin_size);
    } else
    {
        sin_size = sizeof(addrin);
        memset(&addrin, 0, sin_size);
        fd = accept(sockin, (struct sockaddr *)&addrin, &sin_size);
    }
    if (fd == -1) {
        if ((*__errno_location ()) == 24 || (*__errno_location ()) == 23) accepting = 0;
        warn("accept()");
        return;
    }
    conn = new_connection();
    conn->socket = fd;
    nonblock_socket(conn->socket);
    conn->state = RECV_REQUEST;
    if (inet6) {
        conn->client = addrin6.sin6_addr;
    } else
    {
        *(in_addr_t *)&conn->client = addrin.sin_addr.s_addr;
    }
    do { if (((((conn))->entries.le_next) = (((&connlist))->lh_first)) != ((void *)0)) (((&connlist))->lh_first)->entries.le_prev = &(((conn))->entries.le_next); (((&connlist))->lh_first) = (conn); (conn)->entries.le_prev = &(((&connlist))->lh_first); } while (0);
    if (debug)
        printf("accepted connection from %s:%u (fd %d)\n",
               inet_ntoa(addrin.sin_addr),
               ntohs(addrin.sin_port),
               conn->socket);
    poll_recv_request(conn);
}
static int needs_logencoding(const unsigned char c) {
    return ((c <= 0x1F) || (c >= 0x7F) || (c == '"'));
}
static void logencode(const char *src, char *dest) {
    static const char hex[] = "0123456789ABCDEF";
    int i, j;
    for (i = j = 0; src[i] != '\0'; i++) {
        if (needs_logencoding((unsigned char)src[i])) {
            dest[j++] = '%';
            dest[j++] = hex[(src[i] >> 4) & 0xF];
            dest[j++] = hex[ src[i] & 0xF];
        }
        else
            dest[j++] = src[i];
    }
    dest[j] = '\0';
}
static char *clf_date(char *dest, const time_t when) {
    time_t when_copy = when;
    struct tm tm;
    localtime_r(&when_copy, &tm);
    if (strftime(dest, 29, "[%d/%b/%Y:%H:%M:%S %z]", &tm) == 0) {
        dest[0] = 0;
    }
    return dest;
}
static void log_connection(const struct connection *conn) {
    char *safe_method, *safe_url, *safe_referer, *safe_user_agent,
    dest[29];
    if (logfile == ((void *)0))
        return;
    if (conn->http_code == 0)
        return;
    if (conn->method == ((void *)0))
        return;
    do { if (conn->method) { safe_method = xmalloc(strlen(conn->method)*3 + 1); logencode(conn->method, safe_method); } else { safe_method = ((void *)0); } } while(0);
    do { if (conn->url) { safe_url = xmalloc(strlen(conn->url)*3 + 1); logencode(conn->url, safe_url); } else { safe_url = ((void *)0); } } while(0);
    do { if (conn->referer) { safe_referer = xmalloc(strlen(conn->referer)*3 + 1); logencode(conn->referer, safe_referer); } else { safe_referer = ((void *)0); } } while(0);
    do { if (conn->user_agent) { safe_user_agent = xmalloc(strlen(conn->user_agent)*3 + 1); logencode(conn->user_agent, safe_user_agent); } else { safe_user_agent = ((void *)0); } } while(0);
  if (syslog_enabled) {
    syslog(6, "%s - - %s \"%s %s HTTP/1.1\" %d %llu \"%s\" \"%s\"\n",
        get_address_text(&conn->client),
        clf_date(dest, now),
        safe_method ? safe_method : "",
        safe_url ? safe_url : "",
        conn->http_code,
        ((unsigned long long)(conn->total_sent)),
        safe_referer ? safe_referer : "",
        safe_user_agent ? safe_user_agent : ""
        );
  } else {
    fprintf(logfile, "%s - - %s \"%s %s HTTP/1.1\" %d %llu \"%s\" \"%s\"\n",
        get_address_text(&conn->client),
        clf_date(dest, now),
        safe_method ? safe_method : "",
        safe_url ? safe_url : "",
        conn->http_code,
        ((unsigned long long)(conn->total_sent)),
        safe_referer ? safe_referer : "",
        safe_user_agent ? safe_user_agent : ""
        );
    fflush(logfile);
  }
    if (safe_method) free(safe_method);
    if (safe_url) free(safe_url);
    if (safe_referer) free(safe_referer);
    if (safe_user_agent) free(safe_user_agent);
}
static void free_connection(struct connection *conn) {
    if (debug) printf("free_connection(%d)\n", conn->socket);
    log_connection(conn);
    if (conn->socket != -1) xclose(conn->socket);
    if (conn->request != ((void *)0)) free(conn->request);
    if (conn->method != ((void *)0)) free(conn->method);
    if (conn->url != ((void *)0)) free(conn->url);
    if (conn->referer != ((void *)0)) free(conn->referer);
    if (conn->user_agent != ((void *)0)) free(conn->user_agent);
    if (conn->authorization != ((void *)0)) free(conn->authorization);
    if (conn->header != ((void *)0) && !conn->header_dont_free) free(conn->header);
    if (conn->reply != ((void *)0) && !conn->reply_dont_free) free(conn->reply);
    if (conn->reply_fd != -1) xclose(conn->reply_fd);
    accepting = 1;
}
static void recycle_connection(struct connection *conn) {
    int socket_tmp = conn->socket;
    if (debug)
        printf("recycle_connection(%d)\n", socket_tmp);
    conn->socket = -1;
    free_connection(conn);
    conn->socket = socket_tmp;
    conn->request = ((void *)0);
    conn->request_length = 0;
    conn->method = ((void *)0);
    conn->url = ((void *)0);
    conn->referer = ((void *)0);
    conn->user_agent = ((void *)0);
    conn->authorization = ((void *)0);
    conn->range_begin = 0;
    conn->range_end = 0;
    conn->range_begin_given = 0;
    conn->range_end_given = 0;
    conn->header = ((void *)0);
    conn->header_length = 0;
    conn->header_sent = 0;
    conn->header_dont_free = 0;
    conn->header_only = 0;
    conn->http_code = 0;
    conn->conn_close = 1;
    conn->reply = ((void *)0);
    conn->reply_dont_free = 0;
    conn->reply_fd = -1;
    conn->reply_start = 0;
    conn->reply_length = 0;
    conn->reply_sent = 0;
    conn->total_sent = 0;
    conn->state = RECV_REQUEST;
}
static void strntoupper(char *str, const size_t length) {
    size_t i;
    for (i = 0; i < length; i++)
        str[i] = (char)toupper(str[i]);
}
static void poll_check_timeout(struct connection *conn) {
    if (timeout_secs > 0) {
        if (now - conn->last_active >= timeout_secs) {
            if (debug)
                printf("poll_check_timeout(%d) closing connection\n",
                       conn->socket);
            conn->conn_close = 1;
            conn->state = DONE;
        }
    }
}
static char *rfc1123_date(char *dest, const time_t when) {
    time_t when_copy = when;
    if (strftime(dest, 30,
                 "%a, %d %b %Y %H:%M:%S GMT", gmtime(&when_copy)) == 0) {
        dest[0] = 0;
    }
    return dest;
}
static char *urldecode(const char *url) {
    size_t i, pos, len = strlen(url);
    char *out = xmalloc(len+1);
    for (i = 0, pos = 0; i < len; i++) {
        if ((url[i] == '%') && (i+2 < len) &&
            ((*__ctype_b_loc ())[(int) ((url[i+1]))] & (unsigned short int) _ISxdigit) && ((*__ctype_b_loc ())[(int) ((url[i+2]))] & (unsigned short int) _ISxdigit)) {
            out[pos++] = ( ((url[i+1]) >= 'A' && (url[i+1]) <= 'F') ? ((url[i+1])-'A'+10): ((url[i+1]) >= 'a' && (url[i+1]) <= 'f') ? ((url[i+1])-'a'+10): ((url[i+1])-'0') ) * 16 +
                         ( ((url[i+2]) >= 'A' && (url[i+2]) <= 'F') ? ((url[i+2])-'A'+10): ((url[i+2]) >= 'a' && (url[i+2]) <= 'f') ? ((url[i+2])-'a'+10): ((url[i+2])-'0') );
            i += 2;
        } else {
            out[pos++] = url[i];
        }
    }
    out[pos] = '\0';
    return out;
}
static char *normalize_path(char *url) {
    size_t pos = 0;
    if (url == ((void *)0)) return url;
    if (strncmp(url, "http://", 7) == 0) {
        pos += 7;
    } else if (strncmp(url, "https://", 8) == 0) {
        pos += 8;
    }
    if (pos > 0) {
        while (url[pos] && url[pos] != '/') {
            pos++;
        }
        memmove(url, url+pos, strlen(url)+1-pos);
    }
    return url;
}
static const char *keep_alive(const struct connection *conn)
{
    return (conn->conn_close ? "Connection: close\r\n" : keep_alive_field);
}
static char _generated_on_buf[13 + sizeof(pkgname) - 1 + 4 + 30 + 2];
static const char *generated_on(const char date[30]) {
    if (!want_server_id)
        return "";
    snprintf(_generated_on_buf, sizeof(_generated_on_buf),
            "Generated by %s on %s\n",
            pkgname, date);
    return _generated_on_buf;
}
static void default_reply(struct connection *conn,
        const int errcode, const char *errname, const char *format, ...)
        __attribute__((__format__(__printf__, 4, 5)));
static void default_reply(struct connection *conn,
        const int errcode, const char *errname, const char *format, ...) {
    char *reason, date[30];
    va_list va;
    __builtin_va_start(va,format);
    xvasprintf(&reason, format, va);
    __builtin_va_end(va);
    rfc1123_date(date, now);
    conn->reply_length = xasprintf(&(conn->reply),
     "<!DOCTYPE html><html><head><title>%d %s</title></head><body>\n"
     "<h1>%s</h1>\n"
     "%s\n"
     "<hr>\n"
     "%s"
     "</body></html>\n",
     errcode, errname, errname, reason, generated_on(date));
    free(reason);
    const char auth_header[] =
        "WWW-Authenticate: Basic realm=\"User Visible Realm\"\r\n";
    conn->header_length = xasprintf(&(conn->header),
     "HTTP/1.1 %d %s\r\n"
     "Date: %s\r\n"
     "%s"
     "Accept-Ranges: bytes\r\n"
     "%s"
     "%s"
     "Content-Length: %llu\r\n"
     "Content-Type: text/html; charset=UTF-8\r\n"
     "%s"
     "\r\n",
     errcode, errname, date, server_hdr, keep_alive(conn),
     custom_hdrs, ((unsigned long long)(conn->reply_length)),
     (auth_key != ((void *)0) ? auth_header : ""));
    conn->reply_type = REPLY_GENERATED;
    conn->http_code = errcode;
    conn->reply_start = 0;
}
static void redirect(struct connection *conn, const char *format, ...)
    __attribute__((__format__(__printf__, 2, 3)));
static void redirect(struct connection *conn, const char *format, ...) {
    char *where, date[30];
    va_list va;
    __builtin_va_start(va,format);
    xvasprintf(&where, format, va);
    __builtin_va_end(va);
    rfc1123_date(date, now);
    conn->reply_length = xasprintf(&(conn->reply),
     "<!DOCTYPE html><html><head><title>301 Moved Permanently</title></head><body>\n"
     "<h1>Moved Permanently</h1>\n"
     "Moved to: <a href=\"%s\">%s</a>\n"
     "<hr>\n"
     "%s"
     "</body></html>\n",
     where, where, generated_on(date));
    conn->header_length = xasprintf(&(conn->header),
     "HTTP/1.1 301 Moved Permanently\r\n"
     "Date: %s\r\n"
     "%s"
     "Location: %s\r\n"
     "%s"
     "%s"
     "Content-Length: %llu\r\n"
     "Content-Type: text/html; charset=UTF-8\r\n"
     "\r\n",
     date, server_hdr, where, keep_alive(conn),
     custom_hdrs, ((unsigned long long)(conn->reply_length)));
    free(where);
    conn->reply_type = REPLY_GENERATED;
    conn->http_code = 301;
}
static char *parse_field(const struct connection *conn, const char *field) {
    size_t bound1, bound2;
    char *pos;
    pos = strcasestr(conn->request, field);
    if (pos == ((void *)0))
        return ((void *)0);
    ((void) (0));
    bound1 = (size_t)(pos - conn->request) + strlen(field);
    for (bound2 = bound1;
         ((bound2 < conn->request_length) &&
          (conn->request[bound2] != '\r') &&
          (conn->request[bound2] != '\n'));
         bound2++)
            ;
    return split_string(conn->request, bound1, bound2);
}
static void redirect_https(struct connection *conn) {
    char *host, *url;
    url = urldecode(conn->url);
    url = normalize_path(url);
    if (make_safe_url(url) == ((void *)0)) {
        default_reply(conn, 400, "Bad Request",
                      "You requested an invalid URL.");
        free(url);
        return;
    }
    host = parse_field(conn, "Host: ");
    if (host == ((void *)0)) {
        default_reply(conn, 400, "Bad Request",
                "Missing 'Host' header.");
        free(url);
        return;
    }
    redirect(conn, "https://%s%s", host, url);
    free(host);
    free(url);
}
static int is_https_redirect(struct connection *conn) {
    char *proto = ((void *)0);
    if (forward_to_https == 0)
        return 0;
    proto = parse_field(conn, "X-Forwarded-Proto: ");
    if (proto == ((void *)0) || strcasecmp(proto, "https") == 0) {
        free(proto);
        return 0;
    }
    free(proto);
    return 1;
}
static void parse_range_field(struct connection *conn) {
    char *range;
    range = parse_field(conn, "Range: bytes=");
    if (range == ((void *)0))
        return;
    do {
        size_t bound1, bound2, len;
        len = strlen(range);
        bound1 = 0;
        for (bound2=0;
            (bound2 < len) && ((*__ctype_b_loc ())[(int) (((int)range[bound2]))] & (unsigned short int) _ISdigit);
            bound2++)
                ;
        if ((bound2 == len) || (range[bound2] != '-'))
            break;
        if (bound1 != bound2) {
            conn->range_begin_given = 1;
            conn->range_begin = (off_t)strtoll(range+bound1, ((void *)0), 10);
        }
        bound2++;
        for (bound1=bound2;
            (bound2 < len) && ((*__ctype_b_loc ())[(int) (((int)range[bound2]))] & (unsigned short int) _ISdigit);
            bound2++)
                ;
        if ((bound2 != len) && (range[bound2] != ','))
            break;
        if (bound1 != bound2) {
            conn->range_end_given = 1;
            conn->range_end = (off_t)strtoll(range+bound1, ((void *)0), 10);
        }
    } while(0);
    free(range);
}
static int parse_request(struct connection *conn) {
    size_t bound1, bound2;
    char *tmp;
    for (bound1 = 0;
        (bound1 < conn->request_length) &&
        (conn->request[bound1] != ' ');
        bound1++)
            ;
    conn->method = split_string(conn->request, 0, bound1);
    strntoupper(conn->method, bound1);
    for (;
        (bound1 < conn->request_length) &&
        (conn->request[bound1] == ' ');
        bound1++)
            ;
    if (bound1 == conn->request_length)
        return 0;
    for (bound2 = bound1 + 1;
        (bound2 < conn->request_length) &&
        (conn->request[bound2] != ' ') &&
        (conn->request[bound2] != '\r') &&
        (conn->request[bound2] != '\n');
        bound2++) {
        if (conn->request[bound2] == '\0') {
            return 0;
        }
    }
    conn->url = split_string(conn->request, bound1, bound2);
    if (conn->request[bound2] == ' ') {
        char *proto;
        for (bound1 = bound2;
            (bound1 < conn->request_length) &&
            (conn->request[bound1] == ' ');
            bound1++)
                ;
        for (bound2 = bound1 + 1;
            (bound2 < conn->request_length) &&
            (conn->request[bound2] != ' ') &&
            (conn->request[bound2] != '\r');
            bound2++)
                ;
        proto = split_string(conn->request, bound1, bound2);
        if (strcasecmp(proto, "HTTP/1.1") == 0)
            conn->conn_close = 0;
        free(proto);
    }
    tmp = parse_field(conn, "Connection: ");
    if (tmp != ((void *)0)) {
        if (strcasecmp(tmp, "close") == 0)
            conn->conn_close = 1;
        else if (strcasecmp(tmp, "keep-alive") == 0)
            conn->conn_close = 0;
        free(tmp);
    }
    if (!want_keepalive)
        conn->conn_close = 1;
    conn->referer = parse_field(conn, "Referer: ");
    conn->user_agent = parse_field(conn, "User-Agent: ");
    conn->authorization = parse_field(conn, "Authorization: ");
    parse_range_field(conn);
    return 1;
}
static int file_exists(const char *path) {
    struct stat filestat;
    if ((stat(path, &filestat) == -1) && ((*__errno_location ()) == 2))
        return 0;
    else
        return 1;
}
struct dlent {
    char *name;
    int is_dir;
    off_t size;
    struct timespec mtime;
};
static int dlent_cmp(const void *a, const void *b) {
    return strcmp((*((const struct dlent * const *)a))->name,
                  (*((const struct dlent * const *)b))->name);
}
static ssize_t make_sorted_dirlist(const char *path, struct dlent ***output) {
    DIR *dir;
    struct dirent *ent;
    size_t entries = 0;
    size_t pool = 128;
    char *currname;
    struct dlent **list = ((void *)0);
    dir = opendir(path);
    if (dir == ((void *)0))
        return -1;
    currname = xmalloc(strlen(path) + 255 + 1);
    list = xmalloc(sizeof(struct dlent*) * pool);
    while ((ent = readdir(dir)) != ((void *)0)) {
        struct stat s;
        if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0)
            continue;
        if (want_hide_dotfiles && ent->d_name[0] == '.')
            continue;
        ((void) (0));
        sprintf(currname, "%s%s", path, ent->d_name);
        if (stat(currname, &s) == -1)
            continue;
        if (entries == pool) {
            pool *= 2;
            list = xrealloc(list, sizeof(struct dlent*) * pool);
        }
        list[entries] = xmalloc(sizeof(struct dlent));
        list[entries]->name = xstrdup(ent->d_name);
        list[entries]->is_dir = ((((s.st_mode)) & 0170000) == (0040000));
        list[entries]->size = s.st_size;
        list[entries]->mtime = s.st_mtim;
        entries++;
    }
    closedir(dir);
    free(currname);
    qsort(list, entries, sizeof(struct dlent*), dlent_cmp);
    *output = list;
    return (ssize_t)entries;
}
static void cleanup_sorted_dirlist(struct dlent **list, const ssize_t size) {
    ssize_t i;
    for (i = 0; i < size; i++) {
        free(list[i]->name);
        free(list[i]);
    }
}
static int is_unreserved(const unsigned char c) {
    if (c >= 'a' && c <= 'z') return 1;
    if (c >= 'A' && c <= 'Z') return 1;
    if (c >= '0' && c <= '9') return 1;
    switch (c) {
        case '-':
        case '.':
        case '_':
        case '~':
            return 1;
    }
    return 0;
}
static void urlencode(const char *src, char *dest) {
    static const char hex[] = "0123456789ABCDEF";
    int i, j;
    for (i = j = 0; src[i] != '\0'; i++) {
        if (!is_unreserved((unsigned char)src[i])) {
            dest[j++] = '%';
            dest[j++] = hex[(src[i] >> 4) & 0xF];
            dest[j++] = hex[ src[i] & 0xF];
        }
        else
            dest[j++] = src[i];
    }
    dest[j] = '\0';
}
static void append_escaped(struct apbuf *dst, const char *src) {
    int pos = 0;
    while (src[pos] != '\0') {
        switch (src[pos]) {
            case '<':
                appendl(dst, "&lt;", (__builtin_constant_p("&lt;") ? sizeof("&lt;")-1 : strlen("&lt;")) );
                break;
            case '>':
                appendl(dst, "&gt;", (__builtin_constant_p("&gt;") ? sizeof("&gt;")-1 : strlen("&gt;")) );
                break;
            case '&':
                appendl(dst, "&amp;", (__builtin_constant_p("&amp;") ? sizeof("&amp;")-1 : strlen("&amp;")) );
                break;
            case '\'':
                appendl(dst, "&apos;", (__builtin_constant_p("&apos;") ? sizeof("&apos;")-1 : strlen("&apos;")) );
                break;
            case '"':
                appendl(dst, "&quot;", (__builtin_constant_p("&quot;") ? sizeof("&quot;")-1 : strlen("&quot;")) );
                break;
            default:
                appendl(dst, src+pos, 1);
        }
        pos++;
    }
}
static void generate_dir_listing(struct connection *conn, const char *path,
        const char *decoded_url) {
    char date[30], *spaces;
    struct dlent **list;
    ssize_t listsize;
    size_t maxlen = 3;
    int i;
    struct apbuf *listing;
    listsize = make_sorted_dirlist(path, &list);
    if (listsize == -1) {
        if ((*__errno_location ()) == 13)
            default_reply(conn, 403, "Forbidden",
                "You don't have permission to access this URL.");
        else if ((*__errno_location ()) == 2)
            default_reply(conn, 404, "Not Found",
                "The URL you requested was not found.");
        else
            default_reply(conn, 500, "Internal Server Error",
                "Couldn't list directory: %s", strerror((*__errno_location ())));
        return;
    }
    for (i=0; i<listsize; i++) {
        size_t tmp = strlen(list[i]->name);
        if (list[i]->is_dir)
            tmp++;
        if (maxlen < tmp)
            maxlen = tmp;
    }
    listing = make_apbuf();
    appendl(listing, "<!DOCTYPE html>\n<html>\n<head>\n<title>", (__builtin_constant_p("<!DOCTYPE html>\n<html>\n<head>\n<title>") ? sizeof("<!DOCTYPE html>\n<html>\n<head>\n<title>")-1 : strlen("<!DOCTYPE html>\n<html>\n<head>\n<title>")) );
    append_escaped(listing, decoded_url);
    appendl(listing, "</title>\n" "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n" "</head>\n<body>\n<h1>", (__builtin_constant_p("</title>\n" "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n" "</head>\n<body>\n<h1>") ? sizeof("</title>\n" "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n" "</head>\n<body>\n<h1>")-1 : strlen("</title>\n" "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n" "</head>\n<body>\n<h1>")) );
    append_escaped(listing, decoded_url);
    appendl(listing, "</h1>\n<pre>\n", (__builtin_constant_p("</h1>\n<pre>\n") ? sizeof("</h1>\n<pre>\n")-1 : strlen("</h1>\n<pre>\n")) );
    spaces = xmalloc(maxlen);
    memset(spaces, ' ', maxlen);
    if (strncmp(path, wwwroot, strlen(path) - 1) != 0)
        appendl(listing, "<a href=\"../\">..</a>/\n", (__builtin_constant_p("<a href=\"../\">..</a>/\n") ? sizeof("<a href=\"../\">..</a>/\n")-1 : strlen("<a href=\"../\">..</a>/\n")) );
    for (i=0; i<listsize; i++) {
        char safe_url[255*3 + 1];
        urlencode(list[i]->name, safe_url);
        appendl(listing, "<a href=\"", (__builtin_constant_p("<a href=\"") ? sizeof("<a href=\"")-1 : strlen("<a href=\"")) );
        appendl(listing, safe_url, (__builtin_constant_p(safe_url) ? sizeof(safe_url)-1 : strlen(safe_url)) );
        if (list[i]->is_dir)
            appendl(listing, "/", (__builtin_constant_p("/") ? sizeof("/")-1 : strlen("/")) );
        appendl(listing, "\">", (__builtin_constant_p("\">") ? sizeof("\">")-1 : strlen("\">")) );
        append_escaped(listing, list[i]->name);
        appendl(listing, "</a>", (__builtin_constant_p("</a>") ? sizeof("</a>")-1 : strlen("</a>")) );
        char buf[16 + 1];
        struct tm tm;
        localtime_r(&list[i]->mtime.tv_sec, &tm);
        strftime(buf, sizeof buf, "%Y-%m-%d %R", &tm);
        if (list[i]->is_dir) {
            appendl(listing, "/", (__builtin_constant_p("/") ? sizeof("/")-1 : strlen("/")) );
            appendl(listing, spaces, maxlen-strlen(list[i]->name));
            appendl(listing, buf, (__builtin_constant_p(buf) ? sizeof(buf)-1 : strlen(buf)) );
            appendl(listing, "\n", (__builtin_constant_p("\n") ? sizeof("\n")-1 : strlen("\n")) );
        }
        else {
            appendl(listing, spaces, maxlen-strlen(list[i]->name));
            appendl(listing, " ", (__builtin_constant_p(" ") ? sizeof(" ")-1 : strlen(" ")) );
            appendl(listing, buf, (__builtin_constant_p(buf) ? sizeof(buf)-1 : strlen(buf)) );
            appendf(listing, " %10llu\n", ((unsigned long long)(list[i]->size)));
        }
    }
    cleanup_sorted_dirlist(list, listsize);
    free(list);
    free(spaces);
    appendl(listing, "</pre>\n<hr>\n", (__builtin_constant_p("</pre>\n<hr>\n") ? sizeof("</pre>\n<hr>\n")-1 : strlen("</pre>\n<hr>\n")) );
    rfc1123_date(date, now);
    appendl(listing, generated_on(date), (__builtin_constant_p(generated_on(date)) ? sizeof(generated_on(date))-1 : strlen(generated_on(date))) );
    appendl(listing, "</body>\n</html>\n", (__builtin_constant_p("</body>\n</html>\n") ? sizeof("</body>\n</html>\n")-1 : strlen("</body>\n</html>\n")) );
    conn->reply = listing->str;
    conn->reply_length = (off_t)listing->length;
    free(listing);
    conn->header_length = xasprintf(&(conn->header),
     "HTTP/1.1 200 OK\r\n"
     "Date: %s\r\n"
     "%s"
     "Accept-Ranges: bytes\r\n"
     "%s"
     "%s"
     "Content-Length: %llu\r\n"
     "Content-Type: text/html; charset=UTF-8\r\n"
     "\r\n",
     date, server_hdr, keep_alive(conn), custom_hdrs,
     ((unsigned long long)(conn->reply_length)));
    conn->reply_type = REPLY_GENERATED;
    conn->http_code = 200;
}
static void process_get(struct connection *conn) {
    char *decoded_url, *end, *target, *if_mod_since;
    char date[30], lastmod[30];
    const char *mimetype = ((void *)0);
    const char *forward_to = ((void *)0);
    struct stat filestat;
    if ((end = strchr(conn->url, '?')) != ((void *)0))
        *end = '\0';
    decoded_url = urldecode(conn->url);
    decoded_url = normalize_path(decoded_url);
    if (make_safe_url(decoded_url) == ((void *)0)) {
        default_reply(conn, 400, "Bad Request",
                      "You requested an invalid URL.");
        free(decoded_url);
        return;
    }
    if (forward_map) {
        char *host = parse_field(conn, "Host: ");
        if (host) {
            size_t i;
            if (debug)
                printf("host=\"%s\"\n", host);
            for (i = 0; i < forward_map_size; i++) {
                if (strcasecmp(forward_map[i].host, host) == 0) {
                    forward_to = forward_map[i].target_url;
                    break;
                }
            }
            free(host);
        }
    }
    if (!forward_to) {
        forward_to = forward_all_url;
    }
    if (forward_to) {
        redirect(conn, "%s%s", forward_to, decoded_url);
        free(decoded_url);
        return;
    }
    if (want_hide_dotfiles) {
        size_t i;
        for (i = 0; i < strlen(decoded_url) - 1; i++) {
            if (decoded_url[i] == '/' && decoded_url[i + 1] == '.') {
                free(decoded_url);
                default_reply(conn, 404, "Not Found",
                    "The URL you requested was not found.");
                return;
            }
        }
    }
    if (want_single_file) {
        target = xstrdup(wwwroot);
        mimetype = url_content_type(wwwroot);
    }
    else if (decoded_url[strlen(decoded_url)-1] == '/') {
        xasprintf(&target, "%s%s%s", wwwroot, decoded_url, index_name);
        if (!file_exists(target)) {
            free(target);
            if (no_listing) {
                free(decoded_url);
                default_reply(conn, 404, "Not Found",
                    "The URL you requested was not found.");
                return;
            }
            xasprintf(&target, "%s%s", wwwroot, decoded_url);
            generate_dir_listing(conn, target, decoded_url);
            free(target);
            free(decoded_url);
            return;
        }
        mimetype = url_content_type(index_name);
    }
    else {
        xasprintf(&target, "%s%s", wwwroot, decoded_url);
        mimetype = url_content_type(decoded_url);
    }
    free(decoded_url);
    if (debug)
        printf("url=\"%s\", target=\"%s\", content-type=\"%s\"\n",
               conn->url, target, mimetype);
    conn->reply_fd = open(target, 00 | 04000);
    free(target);
    if (conn->reply_fd == -1) {
        if ((*__errno_location ()) == 13)
            default_reply(conn, 403, "Forbidden",
                "You don't have permission to access this URL.");
        else if ((*__errno_location ()) == 2)
            default_reply(conn, 404, "Not Found",
                "The URL you requested was not found.");
        else
            default_reply(conn, 500, "Internal Server Error",
                "The URL you requested cannot be returned: %s.",
                strerror((*__errno_location ())));
        return;
    }
    if (fstat(conn->reply_fd, &filestat) == -1) {
        default_reply(conn, 500, "Internal Server Error",
            "fstat() failed: %s.", strerror((*__errno_location ())));
        return;
    }
    if ((((((filestat.st_mode)) & 0170000) == (0040000))) && (!want_single_file)) {
        redirect(conn, "%s/", conn->url);
        return;
    }
    else if (!((((filestat.st_mode)) & 0170000) == (0100000))) {
        default_reply(conn, 403, "Forbidden", "Not a regular file.");
        return;
    }
    conn->reply_type = REPLY_FROMFILE;
    rfc1123_date(lastmod, filestat.st_mtim.tv_sec);
    if_mod_since = parse_field(conn, "If-Modified-Since: ");
    if ((if_mod_since != ((void *)0)) &&
            (strcmp(if_mod_since, lastmod) == 0)) {
        if (debug)
            printf("not modified since %s\n", if_mod_since);
        conn->http_code = 304;
        conn->header_length = xasprintf(&(conn->header),
         "HTTP/1.1 304 Not Modified\r\n"
         "Date: %s\r\n"
         "%s"
         "Accept-Ranges: bytes\r\n"
         "%s"
         "%s"
         "\r\n",
         rfc1123_date(date, now), server_hdr, keep_alive(conn),
         custom_hdrs);
        conn->reply_length = 0;
        conn->reply_type = REPLY_GENERATED;
        conn->header_only = 1;
        free(if_mod_since);
        return;
    }
    free(if_mod_since);
    if (conn->range_begin_given || conn->range_end_given) {
        off_t from, to;
        if (conn->range_begin_given && conn->range_end_given) {
            from = conn->range_begin;
            to = conn->range_end;
            if (to > (filestat.st_size - 1))
                to = filestat.st_size - 1;
        }
        else if (conn->range_begin_given && !conn->range_end_given) {
            from = conn->range_begin;
            to = filestat.st_size - 1;
        }
        else if (!conn->range_begin_given && conn->range_end_given) {
            to = filestat.st_size - 1;
            from = to - conn->range_end + 1;
            if (from < 0)
                from = 0;
        }
        else
            errx(1, "internal error - from/to mismatch");
        if (from >= filestat.st_size) {
            default_reply(conn, 416, "Requested Range Not Satisfiable",
                "You requested a range outside of the file.");
            return;
        }
        if (to < from) {
            default_reply(conn, 416, "Requested Range Not Satisfiable",
                "You requested a backward range.");
            return;
        }
        conn->reply_start = from;
        conn->reply_length = to - from + 1;
        conn->header_length = xasprintf(&(conn->header),
            "HTTP/1.1 206 Partial Content\r\n"
            "Date: %s\r\n"
            "%s"
            "Accept-Ranges: bytes\r\n"
            "%s"
            "%s"
            "Content-Length: %llu\r\n"
            "Content-Range: bytes %llu-%llu/%llu\r\n"
            "Content-Type: %s\r\n"
            "Last-Modified: %s\r\n"
            "\r\n"
            ,
            rfc1123_date(date, now), server_hdr, keep_alive(conn),
            custom_hdrs,
            ((unsigned long long)(conn->reply_length)), ((unsigned long long)(from)), ((unsigned long long)(to)),
            ((unsigned long long)(filestat.st_size)), mimetype, lastmod
        );
        conn->http_code = 206;
        if (debug)
            printf("sending %llu-%llu/%llu\n",
                   ((unsigned long long)(from)), ((unsigned long long)(to)), ((unsigned long long)(filestat.st_size)));
    }
    else {
        conn->reply_length = filestat.st_size;
        conn->header_length = xasprintf(&(conn->header),
            "HTTP/1.1 200 OK\r\n"
            "Date: %s\r\n"
            "%s"
            "Accept-Ranges: bytes\r\n"
            "%s"
            "%s"
            "Content-Length: %llu\r\n"
            "Content-Type: %s\r\n"
            "Last-Modified: %s\r\n"
            "\r\n"
            ,
            rfc1123_date(date, now), server_hdr, keep_alive(conn),
            custom_hdrs, ((unsigned long long)(conn->reply_length)), mimetype, lastmod
        );
        conn->http_code = 200;
    }
}
int password_equal(const char *user_input, const char *secret) {
    size_t i = 0;
    size_t j = 0;
    char out = 0;
    while (1) {
        out |= user_input[i] ^ secret[j];
        if (user_input[i] == 0) break;
        i++;
        if (secret[j] != 0) j++;
    }
    out |= (i != j);
    out |= (secret[j] != 0);
    return out == 0;
}
static void process_request(struct connection *conn) {
    num_requests++;
    if (!parse_request(conn)) {
        default_reply(conn, 400, "Bad Request",
            "You sent a request that the server couldn't understand.");
    }
    else if (is_https_redirect(conn)) {
        redirect_https(conn);
    }
    else if (auth_key != ((void *)0) &&
            (conn->authorization == ((void *)0) ||
             !password_equal(conn->authorization, auth_key))) {
        default_reply(conn, 401, "Unauthorized",
            "Access denied due to invalid credentials.");
    }
    else if (strcmp(conn->method, "GET") == 0) {
        process_get(conn);
    }
    else if (strcmp(conn->method, "HEAD") == 0) {
        process_get(conn);
        conn->header_only = 1;
    }
    else {
        default_reply(conn, 501, "Not Implemented",
                      "The method you specified is not implemented.");
    }
    conn->state = SEND_HEADER;
    free(conn->request);
    conn->request = ((void *)0);
}
static void poll_recv_request(struct connection *conn) {
    char buf[1<<15];
    ssize_t recvd;
    ((void) (0));
    recvd = recv(conn->socket, buf, sizeof(buf), 0);
    if (debug)
        printf("poll_recv_request(%d) got %d bytes\n",
               conn->socket, (int)recvd);
    if (recvd < 1) {
        if (recvd == -1) {
            if ((*__errno_location ()) == 11) {
                if (debug) printf("poll_recv_request would have blocked\n");
                return;
            }
            if (debug) printf("recv(%d) error: %s\n",
                conn->socket, strerror((*__errno_location ())));
        }
        conn->conn_close = 1;
        conn->state = DONE;
        return;
    }
    conn->last_active = now;
    ((void) (0));
    conn->request = xrealloc(
        conn->request, conn->request_length + (size_t)recvd + 1);
    memcpy(conn->request+conn->request_length, buf, (size_t)recvd);
    conn->request_length += (size_t)recvd;
    conn->request[conn->request_length] = 0;
    total_in += (size_t)recvd;
    if ((conn->request_length > 2) &&
        (memcmp(conn->request+conn->request_length-2, "\n\n", 2) == 0))
            process_request(conn);
    else if ((conn->request_length > 4) &&
        (memcmp(conn->request+conn->request_length-4, "\r\n\r\n", 4) == 0))
            process_request(conn);
    if (conn->request_length > 4000) {
        default_reply(conn, 413, "Request Entity Too Large",
                      "Your request was dropped because it was too long.");
        conn->state = SEND_HEADER;
    }
    if (conn->state == SEND_HEADER)
        poll_send_header(conn);
}
static void poll_send_header(struct connection *conn) {
    ssize_t sent;
    ((void) (0));
    ((void) (0));
    sent = send(conn->socket,
                conn->header + conn->header_sent,
                conn->header_length - conn->header_sent,
                0);
    conn->last_active = now;
    if (debug)
        printf("poll_send_header(%d) sent %d bytes\n",
               conn->socket, (int)sent);
    if (sent < 1) {
        if ((sent == -1) && ((*__errno_location ()) == 11)) {
            if (debug) printf("poll_send_header would have blocked\n");
            return;
        }
        if (debug && (sent == -1))
            printf("send(%d) error: %s\n", conn->socket, strerror((*__errno_location ())));
        conn->conn_close = 1;
        conn->state = DONE;
        return;
    }
    ((void) (0));
    conn->header_sent += (size_t)sent;
    conn->total_sent += (size_t)sent;
    total_out += (size_t)sent;
    if (conn->header_sent == conn->header_length) {
        if (conn->header_only)
            conn->state = DONE;
        else {
            conn->state = SEND_REPLY;
            poll_send_reply(conn);
        }
    }
}
static ssize_t send_from_file(const int s, const int fd,
        off_t ofs, size_t size) {
    if (size > 1<<20)
        size = 1<<20;
    return sendfile(s, fd, &ofs, size);
}
static void poll_send_reply(struct connection *conn)
{
    ssize_t sent;
    const size_t max_size_t = ~((size_t)0);
    off_t send_len = conn->reply_length - conn->reply_sent;
    if (send_len > max_size_t) send_len = max_size_t;
    ((void) (0));
    ((void) (0));
    if (conn->reply_type == REPLY_GENERATED) {
        ((void) (0));
        sent = send(conn->socket,
            conn->reply + conn->reply_start + conn->reply_sent,
            (size_t)send_len, 0);
    }
    else {
        (*__errno_location ()) = 0;
        ((void) (0));
        sent = send_from_file(conn->socket, conn->reply_fd,
            conn->reply_start + conn->reply_sent, (size_t)send_len);
        if (debug && (sent < 1))
            printf("send_from_file returned %lld (errno=%d %s)\n",
                (long long)sent, (*__errno_location ()), strerror((*__errno_location ())));
    }
    conn->last_active = now;
    if (debug)
        printf("poll_send_reply(%d) sent %d: %llu+[%llu-%llu] of %llu\n",
               conn->socket, (int)sent, ((unsigned long long)(conn->reply_start)),
               ((unsigned long long)(conn->reply_sent)), ((unsigned long long)(conn->reply_sent + sent - 1)),
               ((unsigned long long)(conn->reply_length)));
    if (sent < 1) {
        if (sent == -1) {
            if ((*__errno_location ()) == 11) {
                if (debug)
                    printf("poll_send_reply would have blocked\n");
                return;
            }
            if (debug)
                printf("send(%d) error: %s\n", conn->socket, strerror((*__errno_location ())));
        }
        else if (sent == 0) {
            if (debug)
                printf("send(%d) closure\n", conn->socket);
        }
        conn->conn_close = 1;
        conn->state = DONE;
        return;
    }
    conn->reply_sent += sent;
    conn->total_sent += (size_t)sent;
    total_out += (size_t)sent;
    if (conn->reply_sent == conn->reply_length)
        conn->state = DONE;
}
static void httpd_poll(void) {
    fd_set recv_set, send_set;
    int max_fd, select_ret;
    struct connection *conn, *next;
    int bother_with_timeout = 0;
    struct timeval timeout, t0, t1;
    timeout.tv_sec = timeout_secs;
    timeout.tv_usec = 0;
    do { unsigned int __i; fd_set *__arr = (&recv_set); for (__i = 0; __i < sizeof (fd_set) / sizeof (__fd_mask); ++__i) ((__arr)->fds_bits)[__i] = 0; } while (0);
    do { unsigned int __i; fd_set *__arr = (&send_set); for (__i = 0; __i < sizeof (fd_set) / sizeof (__fd_mask); ++__i) ((__arr)->fds_bits)[__i] = 0; } while (0);
    max_fd = 0;
    if (accepting) do { ((void) (((&recv_set)->fds_bits)[((sockin) / (8 * (int) sizeof (__fd_mask)))] |= ((__fd_mask) (1UL << ((sockin) % (8 * (int) sizeof (__fd_mask))))))); max_fd = (max_fd<sockin) ? sockin : max_fd; } while (0);
    for ((conn) = (((&connlist))->lh_first); (conn) && ((next) = (((conn))->entries.le_next), 1); (conn) = (next)) {
        switch (conn->state) {
        case DONE:
            break;
        case RECV_REQUEST:
            do { ((void) (((&recv_set)->fds_bits)[((conn->socket) / (8 * (int) sizeof (__fd_mask)))] |= ((__fd_mask) (1UL << ((conn->socket) % (8 * (int) sizeof (__fd_mask))))))); max_fd = (max_fd<conn->socket) ? conn->socket : max_fd; } while (0);
            bother_with_timeout = 1;
            break;
        case SEND_HEADER:
        case SEND_REPLY:
            do { ((void) (((&send_set)->fds_bits)[((conn->socket) / (8 * (int) sizeof (__fd_mask)))] |= ((__fd_mask) (1UL << ((conn->socket) % (8 * (int) sizeof (__fd_mask))))))); max_fd = (max_fd<conn->socket) ? conn->socket : max_fd; } while (0);
            bother_with_timeout = 1;
            break;
        }
    }
    if (timeout_secs == 0) {
        bother_with_timeout = 0;
    }
    if (debug) {
        printf("select() with max_fd %d timeout %d\n",
                max_fd, bother_with_timeout ? (int)timeout.tv_sec : 0);
        gettimeofday(&t0, ((void *)0));
    }
    select_ret = select(max_fd + 1, &recv_set, &send_set, ((void *)0),
        (bother_with_timeout) ? &timeout : ((void *)0));
    if (select_ret == 0) {
        if (!bother_with_timeout)
            errx(1, "select() timed out");
    }
    if (select_ret == -1) {
        if ((*__errno_location ()) == 4)
            return;
        else
            err(1, "select() failed");
    }
    if (debug) {
        long long sec, usec;
        gettimeofday(&t1, ((void *)0));
        sec = t1.tv_sec - t0.tv_sec;
        usec = t1.tv_usec - t0.tv_usec;
        if (usec < 0) {
            usec += 1000000;
            sec--;
        }
        printf("select() returned %d after %lld.%06lld secs\n",
                select_ret, sec, usec);
    }
    now = time(((void *)0));
    if (((((&recv_set)->fds_bits)[((sockin) / (8 * (int) sizeof (__fd_mask)))] & ((__fd_mask) (1UL << ((sockin) % (8 * (int) sizeof (__fd_mask)))))) != 0))
        accept_connection();
    for ((conn) = (((&connlist))->lh_first); (conn) && ((next) = (((conn))->entries.le_next), 1); (conn) = (next)) {
        poll_check_timeout(conn);
        switch (conn->state) {
        case RECV_REQUEST:
            if (((((&recv_set)->fds_bits)[((conn->socket) / (8 * (int) sizeof (__fd_mask)))] & ((__fd_mask) (1UL << ((conn->socket) % (8 * (int) sizeof (__fd_mask)))))) != 0)) poll_recv_request(conn);
            break;
        case SEND_HEADER:
            if (((((&send_set)->fds_bits)[((conn->socket) / (8 * (int) sizeof (__fd_mask)))] & ((__fd_mask) (1UL << ((conn->socket) % (8 * (int) sizeof (__fd_mask)))))) != 0)) poll_send_header(conn);
            break;
        case SEND_REPLY:
            if (((((&send_set)->fds_bits)[((conn->socket) / (8 * (int) sizeof (__fd_mask)))] & ((__fd_mask) (1UL << ((conn->socket) % (8 * (int) sizeof (__fd_mask)))))) != 0)) poll_send_reply(conn);
            break;
        case DONE:
            break;
        }
        if (conn->state == DONE) {
            if (conn->conn_close) {
                do { if ((((conn))->entries.le_next) != ((void *)0)) (((conn))->entries.le_next)->entries.le_prev = (conn)->entries.le_prev; *(conn)->entries.le_prev = (((conn))->entries.le_next); } while (0);
                free_connection(conn);
                free(conn);
            } else {
                recycle_connection(conn);
            }
        }
    }
}
static int lifeline[2] = { -1, -1 };
static int fd_null = -1;
static void daemonize_start(void) {
    pid_t f;
    if (pipe(lifeline) == -1)
        err(1, "pipe(lifeline)");
    fd_null = open("/dev/null", 02, 0);
    if (fd_null == -1)
        err(1, "open(" "/dev/null" ")");
    f = fork();
    if (f == -1)
        err(1, "fork");
    else if (f != 0) {
        char tmp[1];
        int status;
        pid_t w;
        if (close(lifeline[1]) == -1)
            warn("close lifeline in parent");
        if (read(lifeline[0], tmp, sizeof(tmp)) == -1)
            warn("read lifeline in parent");
        w = waitpid(f, &status, 1);
        if (w == -1)
            err(1, "waitpid");
        else if (w == 0)
            exit(0);
        else
            exit((((status) & 0xff00) >> 8));
    }
}
static void daemonize_finish(void) {
    if (fd_null == -1)
        return;
    if (setsid() == -1)
        err(1, "setsid");
    if (close(lifeline[0]) == -1)
        warn("close read end of lifeline in child");
    if (close(lifeline[1]) == -1)
        warn("couldn't cut the lifeline");
    if (dup2(fd_null, 0) == -1)
        warn("dup2(stdin)");
    if (dup2(fd_null, 1) == -1)
        warn("dup2(stdout)");
    if (dup2(fd_null, 2) == -1)
        warn("dup2(stderr)");
    if (fd_null > 2)
        close(fd_null);
}
static int pidfile_fd = -1;
static void pidfile_remove(void) {
    if (unlink(pidfile_name) == -1)
        err(1, "unlink(pidfile) failed");
    xclose(pidfile_fd);
    pidfile_fd = -1;
}
static int pidfile_read(void) {
    char buf[16];
    int fd, i;
    long long pid;
    fd = open(pidfile_name, 00);
    if (fd == -1)
        err(1, " after create failed");
    i = (int)read(fd, buf, sizeof(buf) - 1);
    if (i == -1)
        err(1, "read from pidfile failed");
    xclose(fd);
    buf[i] = '\0';
    if (!str_to_num(buf, &pid)) {
        err(1, "invalid pidfile contents: \"%s\"", buf);
    }
    return (int)pid;
}
static void pidfile_create(void) {
    int error, fd;
    char pidstr[16];
    fd = open(pidfile_name,
        01 | 0100 | 0200 | 01000 | 04000, 0600);
    if (fd == -1) {
        if (((*__errno_location ()) == 11) || ((*__errno_location ()) == 17))
            errx(1, "daemon already running with PID %d", pidfile_read());
        else
            err(1, "can't create pidfile %s", pidfile_name);
    }
    pidfile_fd = fd;
    if (ftruncate(fd, 0) == -1) {
        error = (*__errno_location ());
        pidfile_remove();
        (*__errno_location ()) = error;
        err(1, "ftruncate() failed");
    }
    snprintf(pidstr, sizeof(pidstr), "%d", (int)getpid());
    if (pwrite(fd, pidstr, strlen(pidstr), 0) != (ssize_t)strlen(pidstr)) {
        error = (*__errno_location ());
        pidfile_remove();
        (*__errno_location ()) = error;
        err(1, "pwrite() failed");
    }
}
static void change_root(void) {
    tzset();
    if (want_single_file) {
        off_t ofs;
        size_t len = strlen(wwwroot) + 1;
        char *path = xstrdup(wwwroot);
        for (ofs = strlen(wwwroot);
             (ofs >= 0) && (wwwroot[ofs] != '/');
             ofs--)
            ;
        if (ofs >= 0) {
            path[ofs + 1] = '\0';
            if (chdir(path) == -1)
                err(1, "chdir(%s)", path);
            memmove(wwwroot, &wwwroot[ofs], len - ofs);
        } else {
            path[0] = '.';
            path[1] = '\0';
        }
        if (chroot(path) == -1)
            err(1, "chroot(%s)", path);
        printf("chrooted to `%s'\n", path);
        free(path);
    } else {
        if (chdir(wwwroot) == -1)
            err(1, "chdir(%s)", wwwroot);
        if (chroot(wwwroot) == -1)
            err(1, "chroot(%s)", wwwroot);
        printf("chrooted to `%s'\n", wwwroot);
        wwwroot[0] = '\0';
    }
}
static void stop_running(int sig __attribute__((__unused__))) {
    running = 0;
}
int main(int argc, char **argv) {
    printf("%s, %s.\n", pkgname, copyright);
    parse_default_extension_map();
    parse_commandline(argc, argv);
    sort_mime_map();
    xasprintf(&keep_alive_field, "Keep-Alive: timeout=%d\r\n", timeout_secs);
    if (want_server_id)
        xasprintf(&server_hdr, "Server: %s\r\n", pkgname);
    else
        server_hdr = xstrdup("");
    init_sockin();
    if (logfile_name == ((void *)0))
        logfile = stdout;
    else {
        logfile = fopen(logfile_name, "ab");
        if (logfile == ((void *)0))
            err(1, "opening logfile: fopen(\"%s\")", logfile_name);
    }
    if (want_daemon)
        daemonize_start();
    if (signal(13, ((__sighandler_t) 1)) == ((__sighandler_t) -1))
        err(1, "signal(ignore SIGPIPE)");
    if (signal(2, stop_running) == ((__sighandler_t) -1))
        err(1, "signal(SIGINT)");
    if (signal(15, stop_running) == ((__sighandler_t) -1))
        err(1, "signal(SIGTERM)");
    if (want_chroot) {
        change_root();
    }
    if (drop_gid != ((gid_t) -1)) {
        gid_t list[1];
        list[0] = drop_gid;
        if (setgroups(1, list) == -1)
            err(1, "setgroups([%d])", (int)drop_gid);
        if (setgid(drop_gid) == -1)
            err(1, "setgid(%d)", (int)drop_gid);
        printf("set gid to %d\n", (int)drop_gid);
    }
    if (drop_uid != ((uid_t) -1)) {
        if (setuid(drop_uid) == -1)
            err(1, "setuid(%d)", (int)drop_uid);
        printf("set uid to %d\n", (int)drop_uid);
    }
    if (pidfile_name) pidfile_create();
    if (want_daemon) daemonize_finish();
    running = 1;
    while (running) httpd_poll();
    xclose(sockin);
    if (logfile != ((void *)0)) fclose(logfile);
    if (pidfile_name) pidfile_remove();
    {
        struct connection *conn, *next;
        for ((conn) = (((&connlist))->lh_first); (conn) && ((next) = (((conn))->entries.le_next), 1); (conn) = (next)) {
            do { if ((((conn))->entries.le_next) != ((void *)0)) (((conn))->entries.le_next)->entries.le_prev = (conn)->entries.le_prev; *(conn)->entries.le_prev = (((conn))->entries.le_next); } while (0);
            free_connection(conn);
            free(conn);
        }
    }
    {
        size_t i;
        for (i=0; i<mime_map_size; i++) {
            free(mime_map[i].extension);
            free(mime_map[i].mimetype);
        }
        free(mime_map);
        if (forward_map)
            free(forward_map);
        free(keep_alive_field);
        free(wwwroot);
        free(server_hdr);
        free(auth_key);
        free(custom_hdrs);
    }
    {
        struct rusage r;
        getrusage(RUSAGE_SELF, &r);
        printf("CPU time used: %u.%02u user, %u.%02u system\n",
            (unsigned int)r.ru_utime.tv_sec,
                (unsigned int)(r.ru_utime.tv_usec/10000),
            (unsigned int)r.ru_stime.tv_sec,
                (unsigned int)(r.ru_stime.tv_usec/10000)
        );
        printf("Requests: %llu\n", ((unsigned long long)(num_requests)));
        printf("Bytes: %llu in, %llu out\n", ((unsigned long long)(total_in)), ((unsigned long long)(total_out)));
    }
    return 0;
}
