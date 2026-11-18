# 0 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
# 0 "<built-in>"
# 0 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 0 "<command-line>" 2
# 1 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
# 32 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
#pragma GCC visibility push(default)







# 1 "/usr/include/string.h" 1 3 4
# 26 "/usr/include/string.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/libc-header-start.h" 1 3 4
# 33 "/usr/include/x86_64-linux-gnu/bits/libc-header-start.h" 3 4
# 1 "/usr/include/features.h" 1 3 4
# 415 "/usr/include/features.h" 3 4
# 1 "/usr/include/features-time64.h" 1 3 4
# 20 "/usr/include/features-time64.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wordsize.h" 1 3 4
# 21 "/usr/include/features-time64.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/timesize.h" 1 3 4
# 19 "/usr/include/x86_64-linux-gnu/bits/timesize.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wordsize.h" 1 3 4
# 20 "/usr/include/x86_64-linux-gnu/bits/timesize.h" 2 3 4
# 22 "/usr/include/features-time64.h" 2 3 4
# 416 "/usr/include/features.h" 2 3 4
# 523 "/usr/include/features.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/sys/cdefs.h" 1 3 4
# 730 "/usr/include/x86_64-linux-gnu/sys/cdefs.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wordsize.h" 1 3 4
# 731 "/usr/include/x86_64-linux-gnu/sys/cdefs.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/long-double.h" 1 3 4
# 732 "/usr/include/x86_64-linux-gnu/sys/cdefs.h" 2 3 4
# 524 "/usr/include/features.h" 2 3 4
# 547 "/usr/include/features.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/gnu/stubs.h" 1 3 4
# 10 "/usr/include/x86_64-linux-gnu/gnu/stubs.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/gnu/stubs-64.h" 1 3 4
# 11 "/usr/include/x86_64-linux-gnu/gnu/stubs.h" 2 3 4
# 548 "/usr/include/features.h" 2 3 4
# 34 "/usr/include/x86_64-linux-gnu/bits/libc-header-start.h" 2 3 4
# 27 "/usr/include/string.h" 2 3 4






# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 1 3 4
# 214 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 3 4

# 214 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 3 4
typedef long unsigned int size_t;
# 34 "/usr/include/string.h" 2 3 4
# 43 "/usr/include/string.h" 3 4
extern void *memcpy (void *__restrict __dest, const void *__restrict __src,
       size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern void *memmove (void *__dest, const void *__src, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
# 61 "/usr/include/string.h" 3 4
extern void *memset (void *__s, int __c, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int memcmp (const void *__s1, const void *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
# 80 "/usr/include/string.h" 3 4
extern int __memcmpeq (const void *__s1, const void *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
# 107 "/usr/include/string.h" 3 4
extern void *memchr (const void *__s, int __c, size_t __n)
      __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
# 141 "/usr/include/string.h" 3 4
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
# 246 "/usr/include/string.h" 3 4
extern char *strchr (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
# 273 "/usr/include/string.h" 3 4
extern char *strrchr (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
# 293 "/usr/include/string.h" 3 4
extern size_t strcspn (const char *__s, const char *__reject)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));


extern size_t strspn (const char *__s, const char *__accept)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
# 323 "/usr/include/string.h" 3 4
extern char *strpbrk (const char *__s, const char *__accept)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));
# 350 "/usr/include/string.h" 3 4
extern char *strstr (const char *__haystack, const char *__needle)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));




extern char *strtok (char *__restrict __s, const char *__restrict __delim)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));



extern char *__strtok_r (char *__restrict __s,
    const char *__restrict __delim,
    char **__restrict __save_ptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 3)));
# 407 "/usr/include/string.h" 3 4
extern size_t strlen (const char *__s)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
# 419 "/usr/include/string.h" 3 4
extern char *strerror (int __errnum) __attribute__ ((__nothrow__ , __leaf__));
# 552 "/usr/include/string.h" 3 4

# 41 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 2
# 1 "/usr/include/stdio.h" 1 3 4
# 28 "/usr/include/stdio.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/libc-header-start.h" 1 3 4
# 29 "/usr/include/stdio.h" 2 3 4





# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 1 3 4
# 35 "/usr/include/stdio.h" 2 3 4


# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stdarg.h" 1 3 4
# 40 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stdarg.h" 3 4
typedef __builtin_va_list __gnuc_va_list;
# 38 "/usr/include/stdio.h" 2 3 4

# 1 "/usr/include/x86_64-linux-gnu/bits/types.h" 1 3 4
# 27 "/usr/include/x86_64-linux-gnu/bits/types.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wordsize.h" 1 3 4
# 28 "/usr/include/x86_64-linux-gnu/bits/types.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/timesize.h" 1 3 4
# 19 "/usr/include/x86_64-linux-gnu/bits/timesize.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wordsize.h" 1 3 4
# 20 "/usr/include/x86_64-linux-gnu/bits/timesize.h" 2 3 4
# 29 "/usr/include/x86_64-linux-gnu/bits/types.h" 2 3 4


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
# 141 "/usr/include/x86_64-linux-gnu/bits/types.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/typesizes.h" 1 3 4
# 142 "/usr/include/x86_64-linux-gnu/bits/types.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/time64.h" 1 3 4
# 143 "/usr/include/x86_64-linux-gnu/bits/types.h" 2 3 4


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
# 40 "/usr/include/stdio.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/types/__fpos_t.h" 1 3 4




# 1 "/usr/include/x86_64-linux-gnu/bits/types/__mbstate_t.h" 1 3 4
# 13 "/usr/include/x86_64-linux-gnu/bits/types/__mbstate_t.h" 3 4
typedef struct
{
  int __count;
  union
  {
    unsigned int __wch;
    char __wchb[4];
  } __value;
} __mbstate_t;
# 6 "/usr/include/x86_64-linux-gnu/bits/types/__fpos_t.h" 2 3 4




typedef struct _G_fpos_t
{
  __off_t __pos;
  __mbstate_t __state;
} __fpos_t;
# 41 "/usr/include/stdio.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/types/__fpos64_t.h" 1 3 4
# 10 "/usr/include/x86_64-linux-gnu/bits/types/__fpos64_t.h" 3 4
typedef struct _G_fpos64_t
{
  __off64_t __pos;
  __mbstate_t __state;
} __fpos64_t;
# 42 "/usr/include/stdio.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/types/__FILE.h" 1 3 4



struct _IO_FILE;
typedef struct _IO_FILE __FILE;
# 43 "/usr/include/stdio.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/types/FILE.h" 1 3 4



struct _IO_FILE;


typedef struct _IO_FILE FILE;
# 44 "/usr/include/stdio.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/types/struct_FILE.h" 1 3 4
# 36 "/usr/include/x86_64-linux-gnu/bits/types/struct_FILE.h" 3 4
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
# 45 "/usr/include/stdio.h" 2 3 4
# 85 "/usr/include/stdio.h" 3 4
typedef __fpos_t fpos_t;
# 129 "/usr/include/stdio.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/stdio_lim.h" 1 3 4
# 130 "/usr/include/stdio.h" 2 3 4
# 149 "/usr/include/stdio.h" 3 4
extern FILE *stdin;
extern FILE *stdout;
extern FILE *stderr;






extern int remove (const char *__filename) __attribute__ ((__nothrow__ , __leaf__));

extern int rename (const char *__old, const char *__new) __attribute__ ((__nothrow__ , __leaf__));
# 184 "/usr/include/stdio.h" 3 4
extern int fclose (FILE *__stream) __attribute__ ((__nonnull__ (1)));
# 194 "/usr/include/stdio.h" 3 4
extern FILE *tmpfile (void)
  __attribute__ ((__malloc__)) __attribute__ ((__malloc__ (fclose, 1))) ;
# 211 "/usr/include/stdio.h" 3 4
extern char *tmpnam (char[20]) __attribute__ ((__nothrow__ , __leaf__)) ;
# 236 "/usr/include/stdio.h" 3 4
extern int fflush (FILE *__stream);
# 264 "/usr/include/stdio.h" 3 4
extern FILE *fopen (const char *__restrict __filename,
      const char *__restrict __modes)
  __attribute__ ((__malloc__)) __attribute__ ((__malloc__ (fclose, 1))) ;




extern FILE *freopen (const char *__restrict __filename,
        const char *__restrict __modes,
        FILE *__restrict __stream) __attribute__ ((__nonnull__ (3)));
# 334 "/usr/include/stdio.h" 3 4
extern void setbuf (FILE *__restrict __stream, char *__restrict __buf) __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__nonnull__ (1)));



extern int setvbuf (FILE *__restrict __stream, char *__restrict __buf,
      int __modes, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 357 "/usr/include/stdio.h" 3 4
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
# 422 "/usr/include/stdio.h" 3 4
extern int fscanf (FILE *__restrict __stream,
     const char *__restrict __format, ...) __attribute__ ((__nonnull__ (1)));




extern int scanf (const char *__restrict __format, ...) ;

extern int sscanf (const char *__restrict __s,
     const char *__restrict __format, ...) __attribute__ ((__nothrow__ , __leaf__));





# 1 "/usr/include/x86_64-linux-gnu/bits/floatn.h" 1 3 4
# 131 "/usr/include/x86_64-linux-gnu/bits/floatn.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/floatn-common.h" 1 3 4
# 24 "/usr/include/x86_64-linux-gnu/bits/floatn-common.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/long-double.h" 1 3 4
# 25 "/usr/include/x86_64-linux-gnu/bits/floatn-common.h" 2 3 4
# 132 "/usr/include/x86_64-linux-gnu/bits/floatn.h" 2 3 4
# 438 "/usr/include/stdio.h" 2 3 4
# 463 "/usr/include/stdio.h" 3 4
extern int fscanf (FILE *__restrict __stream, const char *__restrict __format, ...) __asm__ ("" "__isoc99_fscanf")

                                __attribute__ ((__nonnull__ (1)));
extern int scanf (const char *__restrict __format, ...) __asm__ ("" "__isoc99_scanf")
                              ;
extern int sscanf (const char *__restrict __s, const char *__restrict __format, ...) __asm__ ("" "__isoc99_sscanf") __attribute__ ((__nothrow__ , __leaf__))

                      ;
# 575 "/usr/include/stdio.h" 3 4
extern int fgetc (FILE *__stream) __attribute__ ((__nonnull__ (1)));
extern int getc (FILE *__stream) __attribute__ ((__nonnull__ (1)));





extern int getchar (void);
# 611 "/usr/include/stdio.h" 3 4
extern int fputc (int __c, FILE *__stream) __attribute__ ((__nonnull__ (2)));
extern int putc (int __c, FILE *__stream) __attribute__ ((__nonnull__ (2)));





extern int putchar (int __c);
# 654 "/usr/include/stdio.h" 3 4
extern char *fgets (char *__restrict __s, int __n, FILE *__restrict __stream)
     __attribute__ ((__access__ (__write_only__, 1, 2))) __attribute__ ((__nonnull__ (3)));
# 667 "/usr/include/stdio.h" 3 4
extern char *gets (char *__s) __attribute__ ((__deprecated__));
# 707 "/usr/include/stdio.h" 3 4
extern int fputs (const char *__restrict __s, FILE *__restrict __stream)
  __attribute__ ((__nonnull__ (2)));





extern int puts (const char *__s);






extern int ungetc (int __c, FILE *__stream) __attribute__ ((__nonnull__ (2)));






extern size_t fread (void *__restrict __ptr, size_t __size,
       size_t __n, FILE *__restrict __stream)
  __attribute__ ((__nonnull__ (4)));




extern size_t fwrite (const void *__restrict __ptr, size_t __size,
        size_t __n, FILE *__restrict __s) __attribute__ ((__nonnull__ (4)));
# 769 "/usr/include/stdio.h" 3 4
extern int fseek (FILE *__stream, long int __off, int __whence)
  __attribute__ ((__nonnull__ (1)));




extern long int ftell (FILE *__stream) __attribute__ ((__nonnull__ (1)));




extern void rewind (FILE *__stream) __attribute__ ((__nonnull__ (1)));
# 819 "/usr/include/stdio.h" 3 4
extern int fgetpos (FILE *__restrict __stream, fpos_t *__restrict __pos)
  __attribute__ ((__nonnull__ (1)));




extern int fsetpos (FILE *__stream, const fpos_t *__pos) __attribute__ ((__nonnull__ (1)));
# 850 "/usr/include/stdio.h" 3 4
extern void clearerr (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));

extern int feof (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));

extern int ferror (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 868 "/usr/include/stdio.h" 3 4
extern void perror (const char *__s) __attribute__ ((__cold__));
# 949 "/usr/include/stdio.h" 3 4
extern int __uflow (FILE *);
extern int __overflow (FILE *, int);
# 966 "/usr/include/stdio.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/stdio.h" 1 3 4
# 38 "/usr/include/x86_64-linux-gnu/bits/stdio.h" 3 4
extern __inline int
vprintf (const char *__restrict __fmt, __gnuc_va_list __arg)
{
  return vfprintf (stdout, __fmt, __arg);
}



extern __inline int
getchar (void)
{
  return getc (stdin);
}
# 81 "/usr/include/x86_64-linux-gnu/bits/stdio.h" 3 4
extern __inline int
putchar (int __c)
{
  return putc (__c, stdout);
}
# 967 "/usr/include/stdio.h" 2 3 4







# 42 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 2
# 1 "/usr/include/math.h" 1 3 4
# 27 "/usr/include/math.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/libc-header-start.h" 1 3 4
# 28 "/usr/include/math.h" 2 3 4












# 1 "/usr/include/x86_64-linux-gnu/bits/math-vector.h" 1 3 4
# 25 "/usr/include/x86_64-linux-gnu/bits/math-vector.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/libm-simd-decl-stubs.h" 1 3 4
# 26 "/usr/include/x86_64-linux-gnu/bits/math-vector.h" 2 3 4
# 41 "/usr/include/math.h" 2 3 4
# 156 "/usr/include/math.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/flt-eval-method.h" 1 3 4
# 157 "/usr/include/math.h" 2 3 4
# 208 "/usr/include/math.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/fp-logb.h" 1 3 4
# 209 "/usr/include/math.h" 2 3 4
# 251 "/usr/include/math.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/fp-fast.h" 1 3 4
# 252 "/usr/include/math.h" 2 3 4
# 275 "/usr/include/math.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/mathcalls-macros.h" 1 3 4
# 276 "/usr/include/math.h" 2 3 4





# 1 "/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h" 1 3 4
# 20 "/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h" 3 4
extern int __fpclassify (double __value) __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__const__));


extern int __signbit (double __value) __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__const__));



extern int __isinf (double __value) __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__const__));


extern int __finite (double __value) __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__const__));


extern int __isnan (double __value) __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__const__));


extern int __iseqsig (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__));


extern int __issignaling (double __value) __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__const__));
# 282 "/usr/include/math.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/mathcalls.h" 1 3 4
# 53 "/usr/include/x86_64-linux-gnu/bits/mathcalls.h" 3 4
 extern double acos (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __acos (double __x) __attribute__ ((__nothrow__ , __leaf__));

 extern double asin (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __asin (double __x) __attribute__ ((__nothrow__ , __leaf__));

 extern double atan (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __atan (double __x) __attribute__ ((__nothrow__ , __leaf__));

 extern double atan2 (double __y, double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __atan2 (double __y, double __x) __attribute__ ((__nothrow__ , __leaf__));


 extern double cos (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __cos (double __x) __attribute__ ((__nothrow__ , __leaf__));

 extern double sin (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __sin (double __x) __attribute__ ((__nothrow__ , __leaf__));

 extern double tan (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __tan (double __x) __attribute__ ((__nothrow__ , __leaf__));
# 89 "/usr/include/x86_64-linux-gnu/bits/mathcalls.h" 3 4
 extern double cosh (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __cosh (double __x) __attribute__ ((__nothrow__ , __leaf__));

 extern double sinh (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __sinh (double __x) __attribute__ ((__nothrow__ , __leaf__));

 extern double tanh (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __tanh (double __x) __attribute__ ((__nothrow__ , __leaf__));
# 113 "/usr/include/x86_64-linux-gnu/bits/mathcalls.h" 3 4
 extern double exp (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __exp (double __x) __attribute__ ((__nothrow__ , __leaf__));


extern double frexp (double __x, int *__exponent) __attribute__ ((__nothrow__ , __leaf__)); extern double __frexp (double __x, int *__exponent) __attribute__ ((__nothrow__ , __leaf__));


extern double ldexp (double __x, int __exponent) __attribute__ ((__nothrow__ , __leaf__)); extern double __ldexp (double __x, int __exponent) __attribute__ ((__nothrow__ , __leaf__));


 extern double log (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __log (double __x) __attribute__ ((__nothrow__ , __leaf__));


 extern double log10 (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __log10 (double __x) __attribute__ ((__nothrow__ , __leaf__));


extern double modf (double __x, double *__iptr) __attribute__ ((__nothrow__ , __leaf__)); extern double __modf (double __x, double *__iptr) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
# 173 "/usr/include/x86_64-linux-gnu/bits/mathcalls.h" 3 4
 extern double pow (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)); extern double __pow (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__));


extern double sqrt (double __x) __attribute__ ((__nothrow__ , __leaf__)); extern double __sqrt (double __x) __attribute__ ((__nothrow__ , __leaf__));
# 192 "/usr/include/x86_64-linux-gnu/bits/mathcalls.h" 3 4
extern double ceil (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));


extern double fabs (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));


extern double floor (double __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));


extern double fmod (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__)); extern double __fmod (double __x, double __y) __attribute__ ((__nothrow__ , __leaf__));
# 283 "/usr/include/math.h" 2 3 4
# 450 "/usr/include/math.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h" 1 3 4
# 20 "/usr/include/x86_64-linux-gnu/bits/mathcalls-helper-functions.h" 3 4
extern int __fpclassifyf128 (_Float128 __value) __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__const__));


extern int __signbitf128 (_Float128 __value) __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__const__));



extern int __isinff128 (_Float128 __value) __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__const__));


extern int __finitef128 (_Float128 __value) __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__const__));


extern int __isnanf128 (_Float128 __value) __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__const__));


extern int __iseqsigf128 (_Float128 __x, _Float128 __y) __attribute__ ((__nothrow__ , __leaf__));


extern int __issignalingf128 (_Float128 __value) __attribute__ ((__nothrow__ , __leaf__))
     __attribute__ ((__const__));
# 451 "/usr/include/math.h" 2 3 4
# 1441 "/usr/include/math.h" 3 4

# 43 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 2
# 1 "/usr/include/stdlib.h" 1 3 4
# 26 "/usr/include/stdlib.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/libc-header-start.h" 1 3 4
# 27 "/usr/include/stdlib.h" 2 3 4





# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 1 3 4
# 329 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 3 4
typedef int wchar_t;
# 33 "/usr/include/stdlib.h" 2 3 4


# 59 "/usr/include/stdlib.h" 3 4
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
# 98 "/usr/include/stdlib.h" 3 4
extern size_t __ctype_get_mb_cur_max (void) __attribute__ ((__nothrow__ , __leaf__)) ;



extern double atof (const char *__nptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1))) ;

extern int atoi (const char *__nptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1))) ;

extern long int atol (const char *__nptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1))) ;
# 118 "/usr/include/stdlib.h" 3 4
extern double strtod (const char *__restrict __nptr,
        char **__restrict __endptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 177 "/usr/include/stdlib.h" 3 4
extern long int strtol (const char *__restrict __nptr,
   char **__restrict __endptr, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));

extern unsigned long int strtoul (const char *__restrict __nptr,
      char **__restrict __endptr, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 480 "/usr/include/stdlib.h" 3 4
extern __inline int
__attribute__ ((__nothrow__ , __leaf__)) atoi (const char *__nptr)
{
  return (int) strtol (__nptr, (char **) ((void *)0), 10);
}
extern __inline long int
__attribute__ ((__nothrow__ , __leaf__)) atol (const char *__nptr)
{
  return strtol (__nptr, (char **) ((void *)0), 10);
}
# 573 "/usr/include/stdlib.h" 3 4
extern int rand (void) __attribute__ ((__nothrow__ , __leaf__));

extern void srand (unsigned int __seed) __attribute__ ((__nothrow__ , __leaf__));
# 672 "/usr/include/stdlib.h" 3 4
extern void *malloc (size_t __size) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__))
     __attribute__ ((__alloc_size__ (1))) ;

extern void *calloc (size_t __nmemb, size_t __size)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) __attribute__ ((__alloc_size__ (1, 2))) ;






extern void *realloc (void *__ptr, size_t __size)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__warn_unused_result__)) __attribute__ ((__alloc_size__ (2)));


extern void free (void *__ptr) __attribute__ ((__nothrow__ , __leaf__));
# 730 "/usr/include/stdlib.h" 3 4
extern void abort (void) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__)) __attribute__ ((__cold__));



extern int atexit (void (*__func) (void)) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 756 "/usr/include/stdlib.h" 3 4
extern void exit (int __status) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
# 773 "/usr/include/stdlib.h" 3 4
extern char *getenv (const char *__name) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
# 923 "/usr/include/stdlib.h" 3 4
extern int system (const char *__command) ;
# 948 "/usr/include/stdlib.h" 3 4
typedef int (*__compar_fn_t) (const void *, const void *);
# 960 "/usr/include/stdlib.h" 3 4
extern void *bsearch (const void *__key, const void *__base,
        size_t __nmemb, size_t __size, __compar_fn_t __compar)
     __attribute__ ((__nonnull__ (1, 2, 5))) ;


# 1 "/usr/include/x86_64-linux-gnu/bits/stdlib-bsearch.h" 1 3 4
# 19 "/usr/include/x86_64-linux-gnu/bits/stdlib-bsearch.h" 3 4
extern __inline void *
bsearch (const void *__key, const void *__base, size_t __nmemb, size_t __size,
  __compar_fn_t __compar)
{
  const void *__p;
  int __comparison;

  while (__nmemb)
    {
      __p = (const void *) (((const char *) __base) + ((__nmemb >> 1) * __size));
      __comparison = (*__compar) (__key, __p);
      if (__comparison == 0)
 {

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wcast-qual"

   return (void *) __p;

#pragma GCC diagnostic pop

 }
      if (__comparison > 0)
 {
   __base = ((const char *) __p) + __size;
   --__nmemb;
 }
      __nmemb >>= 1;
    }

  return ((void *)0);
}
# 966 "/usr/include/stdlib.h" 2 3 4




extern void qsort (void *__base, size_t __nmemb, size_t __size,
     __compar_fn_t __compar) __attribute__ ((__nonnull__ (1, 4)));
# 980 "/usr/include/stdlib.h" 3 4
extern int abs (int __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;
extern long int labs (long int __x) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;
# 992 "/usr/include/stdlib.h" 3 4
extern div_t div (int __numer, int __denom)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;
extern ldiv_t ldiv (long int __numer, long int __denom)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;
# 1062 "/usr/include/stdlib.h" 3 4
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
# 1155 "/usr/include/stdlib.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/stdlib-float.h" 1 3 4
# 24 "/usr/include/x86_64-linux-gnu/bits/stdlib-float.h" 3 4
extern __inline double
__attribute__ ((__nothrow__ , __leaf__)) atof (const char *__nptr)
{
  return strtod (__nptr, (char **) ((void *)0));
}
# 1156 "/usr/include/stdlib.h" 2 3 4
# 1167 "/usr/include/stdlib.h" 3 4

# 44 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 2
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/limits.h" 1 3 4
# 34 "/usr/lib/gcc/x86_64-linux-gnu/14/include/limits.h" 3 4
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/syslimits.h" 1 3 4






# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/limits.h" 1 3 4
# 210 "/usr/lib/gcc/x86_64-linux-gnu/14/include/limits.h" 3 4
# 1 "/usr/include/limits.h" 1 3 4
# 26 "/usr/include/limits.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/libc-header-start.h" 1 3 4
# 27 "/usr/include/limits.h" 2 3 4
# 211 "/usr/lib/gcc/x86_64-linux-gnu/14/include/limits.h" 2 3 4
# 8 "/usr/lib/gcc/x86_64-linux-gnu/14/include/syslimits.h" 2 3 4
# 35 "/usr/lib/gcc/x86_64-linux-gnu/14/include/limits.h" 2 3 4
# 45 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 2
# 1 "/usr/include/ctype.h" 1 3 4
# 28 "/usr/include/ctype.h" 3 4

# 39 "/usr/include/ctype.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/endian.h" 1 3 4
# 35 "/usr/include/x86_64-linux-gnu/bits/endian.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/endianness.h" 1 3 4
# 36 "/usr/include/x86_64-linux-gnu/bits/endian.h" 2 3 4
# 40 "/usr/include/ctype.h" 2 3 4






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
# 79 "/usr/include/ctype.h" 3 4
extern const unsigned short int **__ctype_b_loc (void)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern const __int32_t **__ctype_tolower_loc (void)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
extern const __int32_t **__ctype_toupper_loc (void)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
# 108 "/usr/include/ctype.h" 3 4
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
# 206 "/usr/include/ctype.h" 3 4
extern __inline int
__attribute__ ((__nothrow__ , __leaf__)) tolower (int __c)
{
  return __c >= -128 && __c < 256 ? (*__ctype_tolower_loc ())[__c] : __c;
}

extern __inline int
__attribute__ ((__nothrow__ , __leaf__)) toupper (int __c)
{
  return __c >= -128 && __c < 256 ? (*__ctype_toupper_loc ())[__c] : __c;
}
# 327 "/usr/include/ctype.h" 3 4

# 46 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 2
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/float.h" 1 3 4
# 47 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 2


# 1 "/usr/include/locale.h" 1 3 4
# 28 "/usr/include/locale.h" 3 4
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 1 3 4
# 29 "/usr/include/locale.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/locale.h" 1 3 4
# 30 "/usr/include/locale.h" 2 3 4


# 51 "/usr/include/locale.h" 3 4
struct lconv
{


  char *decimal_point;
  char *thousands_sep;





  char *grouping;





  char *int_curr_symbol;
  char *currency_symbol;
  char *mon_decimal_point;
  char *mon_thousands_sep;
  char *mon_grouping;
  char *positive_sign;
  char *negative_sign;
  char int_frac_digits;
  char frac_digits;

  char p_cs_precedes;

  char p_sep_by_space;

  char n_cs_precedes;

  char n_sep_by_space;






  char p_sign_posn;
  char n_sign_posn;
# 111 "/usr/include/locale.h" 3 4
  char __int_p_cs_precedes;
  char __int_p_sep_by_space;
  char __int_n_cs_precedes;
  char __int_n_sep_by_space;
  char __int_p_sign_posn;
  char __int_n_sign_posn;

};



extern char *setlocale (int __category, const char *__locale) __attribute__ ((__nothrow__ , __leaf__));


extern struct lconv *localeconv (void) __attribute__ ((__nothrow__ , __leaf__));
# 195 "/usr/include/locale.h" 3 4

# 50 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 2






#pragma GCC visibility pop


# 1 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.h" 1
# 86 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.h"
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 1 3 4
# 145 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 3 4
typedef long int ptrdiff_t;
# 87 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.h" 2
# 103 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.h"

# 103 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.h"
typedef struct cJSON
{

    struct cJSON *next;
    struct cJSON *prev;

    struct cJSON *child;


    int type;


    char *valuestring;

    int valueint;

    double valuedouble;


    char *string;
} cJSON;

typedef struct cJSON_Hooks
{

      void *( *malloc_fn)(size_t sz);
      void ( *free_fn)(void *ptr);
} cJSON_Hooks;

typedef int cJSON_bool;
# 147 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.h"
__attribute__((visibility("default"))) const char* cJSON_Version(void);


__attribute__((visibility("default"))) void cJSON_InitHooks(cJSON_Hooks* hooks);



__attribute__((visibility("default"))) cJSON * cJSON_Parse(const char *value);
__attribute__((visibility("default"))) cJSON * cJSON_ParseWithLength(const char *value, size_t buffer_length);


__attribute__((visibility("default"))) cJSON * cJSON_ParseWithOpts(const char *value, const char **return_parse_end, cJSON_bool require_null_terminated);
__attribute__((visibility("default"))) cJSON * cJSON_ParseWithLengthOpts(const char *value, size_t buffer_length, const char **return_parse_end, cJSON_bool require_null_terminated);


__attribute__((visibility("default"))) char * cJSON_Print(const cJSON *item);

__attribute__((visibility("default"))) char * cJSON_PrintUnformatted(const cJSON *item);

__attribute__((visibility("default"))) char * cJSON_PrintBuffered(const cJSON *item, int prebuffer, cJSON_bool fmt);


__attribute__((visibility("default"))) cJSON_bool cJSON_PrintPreallocated(cJSON *item, char *buffer, const int length, const cJSON_bool format);

__attribute__((visibility("default"))) void cJSON_Delete(cJSON *item);


__attribute__((visibility("default"))) int cJSON_GetArraySize(const cJSON *array);

__attribute__((visibility("default"))) cJSON * cJSON_GetArrayItem(const cJSON *array, int index);

__attribute__((visibility("default"))) cJSON * cJSON_GetObjectItem(const cJSON * const object, const char * const string);
__attribute__((visibility("default"))) cJSON * cJSON_GetObjectItemCaseSensitive(const cJSON * const object, const char * const string);
__attribute__((visibility("default"))) cJSON_bool cJSON_HasObjectItem(const cJSON *object, const char *string);

__attribute__((visibility("default"))) const char * cJSON_GetErrorPtr(void);


__attribute__((visibility("default"))) char * cJSON_GetStringValue(const cJSON * const item);
__attribute__((visibility("default"))) double cJSON_GetNumberValue(const cJSON * const item);


__attribute__((visibility("default"))) cJSON_bool cJSON_IsInvalid(const cJSON * const item);
__attribute__((visibility("default"))) cJSON_bool cJSON_IsFalse(const cJSON * const item);
__attribute__((visibility("default"))) cJSON_bool cJSON_IsTrue(const cJSON * const item);
__attribute__((visibility("default"))) cJSON_bool cJSON_IsBool(const cJSON * const item);
__attribute__((visibility("default"))) cJSON_bool cJSON_IsNull(const cJSON * const item);
__attribute__((visibility("default"))) cJSON_bool cJSON_IsNumber(const cJSON * const item);
__attribute__((visibility("default"))) cJSON_bool cJSON_IsString(const cJSON * const item);
__attribute__((visibility("default"))) cJSON_bool cJSON_IsArray(const cJSON * const item);
__attribute__((visibility("default"))) cJSON_bool cJSON_IsObject(const cJSON * const item);
__attribute__((visibility("default"))) cJSON_bool cJSON_IsRaw(const cJSON * const item);


__attribute__((visibility("default"))) cJSON * cJSON_CreateNull(void);
__attribute__((visibility("default"))) cJSON * cJSON_CreateTrue(void);
__attribute__((visibility("default"))) cJSON * cJSON_CreateFalse(void);
__attribute__((visibility("default"))) cJSON * cJSON_CreateBool(cJSON_bool boolean);
__attribute__((visibility("default"))) cJSON * cJSON_CreateNumber(double num);
__attribute__((visibility("default"))) cJSON * cJSON_CreateString(const char *string);

__attribute__((visibility("default"))) cJSON * cJSON_CreateRaw(const char *raw);
__attribute__((visibility("default"))) cJSON * cJSON_CreateArray(void);
__attribute__((visibility("default"))) cJSON * cJSON_CreateObject(void);



__attribute__((visibility("default"))) cJSON * cJSON_CreateStringReference(const char *string);


__attribute__((visibility("default"))) cJSON * cJSON_CreateObjectReference(const cJSON *child);
__attribute__((visibility("default"))) cJSON * cJSON_CreateArrayReference(const cJSON *child);



__attribute__((visibility("default"))) cJSON * cJSON_CreateIntArray(const int *numbers, int count);
__attribute__((visibility("default"))) cJSON * cJSON_CreateFloatArray(const float *numbers, int count);
__attribute__((visibility("default"))) cJSON * cJSON_CreateDoubleArray(const double *numbers, int count);
__attribute__((visibility("default"))) cJSON * cJSON_CreateStringArray(const char *const *strings, int count);


__attribute__((visibility("default"))) cJSON_bool cJSON_AddItemToArray(cJSON *array, cJSON *item);
__attribute__((visibility("default"))) cJSON_bool cJSON_AddItemToObject(cJSON *object, const char *string, cJSON *item);



__attribute__((visibility("default"))) cJSON_bool cJSON_AddItemToObjectCS(cJSON *object, const char *string, cJSON *item);

__attribute__((visibility("default"))) cJSON_bool cJSON_AddItemReferenceToArray(cJSON *array, cJSON *item);
__attribute__((visibility("default"))) cJSON_bool cJSON_AddItemReferenceToObject(cJSON *object, const char *string, cJSON *item);


__attribute__((visibility("default"))) cJSON * cJSON_DetachItemViaPointer(cJSON *parent, cJSON * const item);
__attribute__((visibility("default"))) cJSON * cJSON_DetachItemFromArray(cJSON *array, int which);
__attribute__((visibility("default"))) void cJSON_DeleteItemFromArray(cJSON *array, int which);
__attribute__((visibility("default"))) cJSON * cJSON_DetachItemFromObject(cJSON *object, const char *string);
__attribute__((visibility("default"))) cJSON * cJSON_DetachItemFromObjectCaseSensitive(cJSON *object, const char *string);
__attribute__((visibility("default"))) void cJSON_DeleteItemFromObject(cJSON *object, const char *string);
__attribute__((visibility("default"))) void cJSON_DeleteItemFromObjectCaseSensitive(cJSON *object, const char *string);


__attribute__((visibility("default"))) cJSON_bool cJSON_InsertItemInArray(cJSON *array, int which, cJSON *newitem);
__attribute__((visibility("default"))) cJSON_bool cJSON_ReplaceItemViaPointer(cJSON * const parent, cJSON * const item, cJSON * replacement);
__attribute__((visibility("default"))) cJSON_bool cJSON_ReplaceItemInArray(cJSON *array, int which, cJSON *newitem);
__attribute__((visibility("default"))) cJSON_bool cJSON_ReplaceItemInObject(cJSON *object,const char *string,cJSON *newitem);
__attribute__((visibility("default"))) cJSON_bool cJSON_ReplaceItemInObjectCaseSensitive(cJSON *object,const char *string,cJSON *newitem);


__attribute__((visibility("default"))) cJSON * cJSON_Duplicate(const cJSON *item, cJSON_bool recurse);





__attribute__((visibility("default"))) cJSON_bool cJSON_Compare(const cJSON * const a, const cJSON * const b, const cJSON_bool case_sensitive);




__attribute__((visibility("default"))) void cJSON_Minify(char *json);



__attribute__((visibility("default"))) cJSON* cJSON_AddNullToObject(cJSON * const object, const char * const name);
__attribute__((visibility("default"))) cJSON* cJSON_AddTrueToObject(cJSON * const object, const char * const name);
__attribute__((visibility("default"))) cJSON* cJSON_AddFalseToObject(cJSON * const object, const char * const name);
__attribute__((visibility("default"))) cJSON* cJSON_AddBoolToObject(cJSON * const object, const char * const name, const cJSON_bool boolean);
__attribute__((visibility("default"))) cJSON* cJSON_AddNumberToObject(cJSON * const object, const char * const name, const double number);
__attribute__((visibility("default"))) cJSON* cJSON_AddStringToObject(cJSON * const object, const char * const name, const char * const string);
__attribute__((visibility("default"))) cJSON* cJSON_AddRawToObject(cJSON * const object, const char * const name, const char * const raw);
__attribute__((visibility("default"))) cJSON* cJSON_AddObjectToObject(cJSON * const object, const char * const name);
__attribute__((visibility("default"))) cJSON* cJSON_AddArrayToObject(cJSON * const object, const char * const name);




__attribute__((visibility("default"))) double cJSON_SetNumberHelper(cJSON *object, double number);


__attribute__((visibility("default"))) char* cJSON_SetValuestring(cJSON *object, const char *valuestring);
# 299 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.h"
__attribute__((visibility("default"))) void * cJSON_malloc(size_t size);
__attribute__((visibility("default"))) void cJSON_free(void *object);
# 60 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 2
# 88 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
typedef struct {
    const unsigned char *json;
    size_t position;
} error;
static error global_error = { 
# 92 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                             ((void *)0)
# 92 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                 , 0 };

__attribute__((visibility("default"))) const char * cJSON_GetErrorPtr(void)
{
    return (const char*) (global_error.json + global_error.position);
}

__attribute__((visibility("default"))) char * cJSON_GetStringValue(const cJSON * const item)
{
    if (!cJSON_IsString(item))
    {
        return 
# 103 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 103 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    return item->valuestring;
}

__attribute__((visibility("default"))) double cJSON_GetNumberValue(const cJSON * const item)
{
    if (!cJSON_IsNumber(item))
    {
        return (double) 0.0/0.0;
    }

    return item->valuedouble;
}






__attribute__((visibility("default"))) const char* cJSON_Version(void)
{
    static char version[15];
    sprintf(version, "%i.%i.%i", 1, 7, 19);

    return version;
}


static int case_insensitive_strcmp(const unsigned char *string1, const unsigned char *string2)
{
    if ((string1 == 
# 135 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                   ((void *)0)
# 135 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                       ) || (string2 == 
# 135 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                        ((void *)0)
# 135 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                            ))
    {
        return 1;
    }

    if (string1 == string2)
    {
        return 0;
    }

    for(; 
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
         (__extension__ ({ int __res; if (sizeof (
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
         *string1
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
         ) > 1) { if (__builtin_constant_p (
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
         *string1
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
         )) { int __c = (
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
         *string1
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
         ); __res = __c < -128 || __c > 255 ? __c : (*__ctype_tolower_loc ())[__c]; } else __res = tolower (
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
         *string1
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
         ); } else __res = (*__ctype_tolower_loc ())[(int) (
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
         *string1
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
         )]; __res; })) 
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                           == 
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              (__extension__ ({ int __res; if (sizeof (
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                              *string2
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              ) > 1) { if (__builtin_constant_p (
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                              *string2
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              )) { int __c = (
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                              *string2
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              ); __res = __c < -128 || __c > 255 ? __c : (*__ctype_tolower_loc ())[__c]; } else __res = tolower (
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                              *string2
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              ); } else __res = (*__ctype_tolower_loc ())[(int) (
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                              *string2
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              )]; __res; }))
# 145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                               ; (void)string1++, string2++)
    {
        if (*string1 == '\0')
        {
            return 0;
        }
    }

    return 
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          (__extension__ ({ int __res; if (sizeof (
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
          *string1
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          ) > 1) { if (__builtin_constant_p (
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
          *string1
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          )) { int __c = (
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
          *string1
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          ); __res = __c < -128 || __c > 255 ? __c : (*__ctype_tolower_loc ())[__c]; } else __res = tolower (
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
          *string1
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          ); } else __res = (*__ctype_tolower_loc ())[(int) (
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
          *string1
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          )]; __res; })) 
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                            - 
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              (__extension__ ({ int __res; if (sizeof (
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                              *string2
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              ) > 1) { if (__builtin_constant_p (
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                              *string2
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              )) { int __c = (
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                              *string2
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              ); __res = __c < -128 || __c > 255 ? __c : (*__ctype_tolower_loc ())[__c]; } else __res = tolower (
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                              *string2
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              ); } else __res = (*__ctype_tolower_loc ())[(int) (
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                              *string2
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              )]; __res; }))
# 153 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                               ;
}

typedef struct internal_hooks
{
    void *( *allocate)(size_t size);
    void ( *deallocate)(void *pointer);
    void *( *reallocate)(void *pointer, size_t size);
} internal_hooks;
# 186 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
static internal_hooks global_hooks = { malloc, free, realloc };

static unsigned char* cJSON_strdup(const unsigned char* string, const internal_hooks * const hooks)
{
    size_t length = 0;
    unsigned char *copy = 
# 191 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                         ((void *)0)
# 191 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                             ;

    if (string == 
# 193 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                 ((void *)0)
# 193 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                     )
    {
        return 
# 195 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 195 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    length = strlen((const char*)string) + sizeof("");
    copy = (unsigned char*)hooks->allocate(length);
    if (copy == 
# 200 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 200 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return 
# 202 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 202 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }
    memcpy(copy, string, length);

    return copy;
}

__attribute__((visibility("default"))) void cJSON_InitHooks(cJSON_Hooks* hooks)
{
    if (hooks == 
# 211 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 211 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    )
    {

        global_hooks.allocate = malloc;
        global_hooks.deallocate = free;
        global_hooks.reallocate = realloc;
        return;
    }

    global_hooks.allocate = malloc;
    if (hooks->malloc_fn != 
# 221 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                           ((void *)0)
# 221 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                               )
    {
        global_hooks.allocate = hooks->malloc_fn;
    }

    global_hooks.deallocate = free;
    if (hooks->free_fn != 
# 227 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                         ((void *)0)
# 227 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                             )
    {
        global_hooks.deallocate = hooks->free_fn;
    }


    global_hooks.reallocate = 
# 233 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                             ((void *)0)
# 233 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                 ;
    if ((global_hooks.allocate == malloc) && (global_hooks.deallocate == free))
    {
        global_hooks.reallocate = realloc;
    }
}


static cJSON *cJSON_New_Item(const internal_hooks * const hooks)
{
    cJSON* node = (cJSON*)hooks->allocate(sizeof(cJSON));
    if (node)
    {
        memset(node, '\0', sizeof(cJSON));
    }

    return node;
}


__attribute__((visibility("default"))) void cJSON_Delete(cJSON *item)
{
    cJSON *next = 
# 255 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                 ((void *)0)
# 255 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                     ;
    while (item != 
# 256 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 256 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      )
    {
        next = item->next;
        if (!(item->type & 256) && (item->child != 
# 259 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                                                ((void *)0)
# 259 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                                    ))
        {
            cJSON_Delete(item->child);
        }
        if (!(item->type & 256) && (item->valuestring != 
# 263 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                                                      ((void *)0)
# 263 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                                          ))
        {
            global_hooks.deallocate(item->valuestring);
            item->valuestring = 
# 266 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                               ((void *)0)
# 266 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                   ;
        }
        if (!(item->type & 512) && (item->string != 
# 268 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                                                   ((void *)0)
# 268 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                                       ))
        {
            global_hooks.deallocate(item->string);
            item->string = 
# 271 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                          ((void *)0)
# 271 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                              ;
        }
        global_hooks.deallocate(item);
        item = next;
    }
}


static unsigned char get_decimal_point(void)
{

    struct lconv *lconv = localeconv();
    return (unsigned char) lconv->decimal_point[0];



}

typedef struct
{
    const unsigned char *content;
    size_t length;
    size_t offset;
    size_t depth;
    internal_hooks hooks;
} parse_buffer;
# 307 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
static cJSON_bool parse_number(cJSON * const item, parse_buffer * const input_buffer)
{
    double number = 0;
    unsigned char *after_end = 
# 310 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              ((void *)0)
# 310 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                  ;
    unsigned char *number_c_string;
    unsigned char decimal_point = get_decimal_point();
    size_t i = 0;
    size_t number_string_length = 0;
    cJSON_bool has_decimal_point = ((cJSON_bool)0);

    if ((input_buffer == 
# 317 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                        ((void *)0)
# 317 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                            ) || (input_buffer->content == 
# 317 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                                           ((void *)0)
# 317 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                               ))
    {
        return ((cJSON_bool)0);
    }




    for (i = 0; ((input_buffer != 
# 325 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 325 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
               ) && (((input_buffer)->offset + i) < (input_buffer)->length)); i++)
    {
        switch (((input_buffer)->content + (input_buffer)->offset)[i])
        {
            case '0':
            case '1':
            case '2':
            case '3':
            case '4':
            case '5':
            case '6':
            case '7':
            case '8':
            case '9':
            case '+':
            case '-':
            case 'e':
            case 'E':
                number_string_length++;
                break;

            case '.':
                number_string_length++;
                has_decimal_point = ((cJSON_bool)1);
                break;

            default:
                goto loop_end;
        }
    }
loop_end:

    number_c_string = (unsigned char *) input_buffer->hooks.allocate(number_string_length + 1);
    if (number_c_string == 
# 358 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                          ((void *)0)
# 358 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                              )
    {
        return ((cJSON_bool)0);
    }

    memcpy(number_c_string, ((input_buffer)->content + (input_buffer)->offset), number_string_length);
    number_c_string[number_string_length] = '\0';

    if (has_decimal_point)
    {
        for (i = 0; i < number_string_length; i++)
        {
            if (number_c_string[i] == '.')
            {

                number_c_string[i] = decimal_point;
            }
        }
    }

    number = strtod((const char*)number_c_string, (char**)&after_end);
    if (number_c_string == after_end)
    {

        input_buffer->hooks.deallocate(number_c_string);
        return ((cJSON_bool)0);
    }

    item->valuedouble = number;


    if (number >= 0x7fffffff
# 389 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                        )
    {
        item->valueint = 0x7fffffff
# 391 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                               ;
    }
    else if (number <= (double)
# 393 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              (-0x7fffffff - 1)
# 393 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                     )
    {
        item->valueint = 
# 395 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                        (-0x7fffffff - 1)
# 395 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                               ;
    }
    else
    {
        item->valueint = (int)number;
    }

    item->type = (1 << 3);

    input_buffer->offset += (size_t)(after_end - number_c_string);

    input_buffer->hooks.deallocate(number_c_string);
    return ((cJSON_bool)1);
}


__attribute__((visibility("default"))) double cJSON_SetNumberHelper(cJSON *object, double number)
{
    if (number >= 0x7fffffff
# 413 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                        )
    {
        object->valueint = 0x7fffffff
# 415 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                 ;
    }
    else if (number <= (double)
# 417 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              (-0x7fffffff - 1)
# 417 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                     )
    {
        object->valueint = 
# 419 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                          (-0x7fffffff - 1)
# 419 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                 ;
    }
    else
    {
        object->valueint = (int)number;
    }

    return object->valuedouble = number;
}


__attribute__((visibility("default"))) char* cJSON_SetValuestring(cJSON *object, const char *valuestring)
{
    char *copy = 
# 432 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 432 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    ;
    size_t v1_len;
    size_t v2_len;

    if ((object == 
# 436 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 436 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ) || !(object->type & (1 << 4)) || (object->type & 256))
    {
        return 
# 438 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 438 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    if (object->valuestring == 
# 441 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              ((void *)0) 
# 441 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                   || valuestring == 
# 441 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                                     ((void *)0)
# 441 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                         )
    {
        return 
# 443 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 443 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    v1_len = strlen(valuestring);
    v2_len = strlen(object->valuestring);

    if (v1_len <= v2_len)
    {

        if (!( valuestring + v1_len < object->valuestring || object->valuestring + v2_len < valuestring ))
        {
            return 
# 454 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 454 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ;
        }
        strcpy(object->valuestring, valuestring);
        return object->valuestring;
    }
    copy = (char*) cJSON_strdup((const unsigned char*)valuestring, &global_hooks);
    if (copy == 
# 460 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 460 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return 
# 462 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 462 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }
    if (object->valuestring != 
# 464 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              ((void *)0)
# 464 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                  )
    {
        cJSON_free(object->valuestring);
    }
    object->valuestring = copy;

    return copy;
}

typedef struct
{
    unsigned char *buffer;
    size_t length;
    size_t offset;
    size_t depth;
    cJSON_bool noalloc;
    cJSON_bool format;
    internal_hooks hooks;
} printbuffer;


static unsigned char* ensure(printbuffer * const p, size_t needed)
{
    unsigned char *newbuffer = 
# 487 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              ((void *)0)
# 487 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                  ;
    size_t newsize = 0;

    if ((p == 
# 490 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
             ((void *)0)
# 490 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                 ) || (p->buffer == 
# 490 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                    ((void *)0)
# 490 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                        ))
    {
        return 
# 492 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 492 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    if ((p->length > 0) && (p->offset >= p->length))
    {

        return 
# 498 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 498 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    if (needed > 0x7fffffff
# 501 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                       )
    {

        return 
# 504 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 504 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    needed += p->offset + 1;
    if (needed <= p->length)
    {
        return p->buffer + p->offset;
    }

    if (p->noalloc) {
        return 
# 514 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 514 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }


    if (needed > (0x7fffffff 
# 518 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                         / 2))
    {

        if (needed <= 0x7fffffff
# 521 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                            )
        {
            newsize = 0x7fffffff
# 523 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                            ;
        }
        else
        {
            return 
# 527 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 527 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ;
        }
    }
    else
    {
        newsize = needed * 2;
    }

    if (p->hooks.reallocate != 
# 535 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              ((void *)0)
# 535 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                  )
    {

        newbuffer = (unsigned char*)p->hooks.reallocate(p->buffer, newsize);
        if (newbuffer == 
# 539 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                        ((void *)0)
# 539 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                            )
        {
            p->hooks.deallocate(p->buffer);
            p->length = 0;
            p->buffer = 
# 543 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                       ((void *)0)
# 543 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                           ;

            return 
# 545 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 545 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ;
        }
    }
    else
    {

        newbuffer = (unsigned char*)p->hooks.allocate(newsize);
        if (!newbuffer)
        {
            p->hooks.deallocate(p->buffer);
            p->length = 0;
            p->buffer = 
# 556 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                       ((void *)0)
# 556 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                           ;

            return 
# 558 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 558 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ;
        }

        memcpy(newbuffer, p->buffer, p->offset + 1);
        p->hooks.deallocate(p->buffer);
    }
    p->length = newsize;
    p->buffer = newbuffer;

    return newbuffer + p->offset;
}


static void update_offset(printbuffer * const buffer)
{
    const unsigned char *buffer_pointer = 
# 573 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                         ((void *)0)
# 573 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                             ;
    if ((buffer == 
# 574 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 574 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ) || (buffer->buffer == 
# 574 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                              ((void *)0)
# 574 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                  ))
    {
        return;
    }
    buffer_pointer = buffer->buffer + buffer->offset;

    buffer->offset += strlen((const char*)buffer_pointer);
}


static cJSON_bool compare_double(double a, double b)
{
    double maxVal = fabs(a) > fabs(b) ? fabs(a) : fabs(b);
    return (fabs(a - b) <= maxVal * ((double)2.22044604925031308084726333618164062e-16L)
# 587 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                              );
}


static cJSON_bool print_number(const cJSON * const item, printbuffer * const output_buffer)
{
    unsigned char *output_pointer = 
# 593 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                   ((void *)0)
# 593 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                       ;
    double d = item->valuedouble;
    int length = 0;
    size_t i = 0;
    unsigned char number_buffer[26] = {0};
    unsigned char decimal_point = get_decimal_point();
    double test = 0.0;

    if (output_buffer == 
# 601 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                        ((void *)0)
# 601 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                            )
    {
        return ((cJSON_bool)0);
    }


    if ((d != d) || (((d - d) != (d - d)) && !(d != d)))
    {
        length = sprintf((char*)number_buffer, "null");
    }
    else if(d == (double)item->valueint)
    {
        length = sprintf((char*)number_buffer, "%d", item->valueint);
    }
    else
    {

        length = sprintf((char*)number_buffer, "%1.15g", d);


        if ((sscanf((char*)number_buffer, "%lg", &test) != 1) || !compare_double((double)test, d))
        {

            length = sprintf((char*)number_buffer, "%1.17g", d);
        }
    }


    if ((length < 0) || (length > (int)(sizeof(number_buffer) - 1)))
    {
        return ((cJSON_bool)0);
    }


    output_pointer = ensure(output_buffer, (size_t)length + sizeof(""));
    if (output_pointer == 
# 636 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                         ((void *)0)
# 636 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                             )
    {
        return ((cJSON_bool)0);
    }



    for (i = 0; i < ((size_t)length); i++)
    {
        if (number_buffer[i] == decimal_point)
        {
            output_pointer[i] = '.';
            continue;
        }

        output_pointer[i] = number_buffer[i];
    }
    output_pointer[i] = '\0';

    output_buffer->offset += (size_t)length;

    return ((cJSON_bool)1);
}


static unsigned parse_hex4(const unsigned char * const input)
{
    unsigned int h = 0;
    size_t i = 0;

    for (i = 0; i < 4; i++)
    {

        if ((input[i] >= '0') && (input[i] <= '9'))
        {
            h += (unsigned int) input[i] - '0';
        }
        else if ((input[i] >= 'A') && (input[i] <= 'F'))
        {
            h += (unsigned int) 10 + input[i] - 'A';
        }
        else if ((input[i] >= 'a') && (input[i] <= 'f'))
        {
            h += (unsigned int) 10 + input[i] - 'a';
        }
        else
        {
            return 0;
        }

        if (i < 3)
        {

            h = h << 4;
        }
    }

    return h;
}



static unsigned char utf16_literal_to_utf8(const unsigned char * const input_pointer, const unsigned char * const input_end, unsigned char **output_pointer)
{
    long unsigned int codepoint = 0;
    unsigned int first_code = 0;
    const unsigned char *first_sequence = input_pointer;
    unsigned char utf8_length = 0;
    unsigned char utf8_position = 0;
    unsigned char sequence_length = 0;
    unsigned char first_byte_mark = 0;

    if ((input_end - first_sequence) < 6)
    {

        goto fail;
    }


    first_code = parse_hex4(first_sequence + 2);


    if (((first_code >= 0xDC00) && (first_code <= 0xDFFF)))
    {
        goto fail;
    }


    if ((first_code >= 0xD800) && (first_code <= 0xDBFF))
    {
        const unsigned char *second_sequence = first_sequence + 6;
        unsigned int second_code = 0;
        sequence_length = 12;

        if ((input_end - second_sequence) < 6)
        {

            goto fail;
        }

        if ((second_sequence[0] != '\\') || (second_sequence[1] != 'u'))
        {

            goto fail;
        }


        second_code = parse_hex4(second_sequence + 2);

        if ((second_code < 0xDC00) || (second_code > 0xDFFF))
        {

            goto fail;
        }



        codepoint = 0x10000 + (((first_code & 0x3FF) << 10) | (second_code & 0x3FF));
    }
    else
    {
        sequence_length = 6;
        codepoint = first_code;
    }




    if (codepoint < 0x80)
    {

        utf8_length = 1;
    }
    else if (codepoint < 0x800)
    {

        utf8_length = 2;
        first_byte_mark = 0xC0;
    }
    else if (codepoint < 0x10000)
    {

        utf8_length = 3;
        first_byte_mark = 0xE0;
    }
    else if (codepoint <= 0x10FFFF)
    {

        utf8_length = 4;
        first_byte_mark = 0xF0;
    }
    else
    {

        goto fail;
    }


    for (utf8_position = (unsigned char)(utf8_length - 1); utf8_position > 0; utf8_position--)
    {

        (*output_pointer)[utf8_position] = (unsigned char)((codepoint | 0x80) & 0xBF);
        codepoint >>= 6;
    }

    if (utf8_length > 1)
    {
        (*output_pointer)[0] = (unsigned char)((codepoint | first_byte_mark) & 0xFF);
    }
    else
    {
        (*output_pointer)[0] = (unsigned char)(codepoint & 0x7F);
    }

    *output_pointer += utf8_length;

    return sequence_length;

fail:
    return 0;
}


static cJSON_bool parse_string(cJSON * const item, parse_buffer * const input_buffer)
{
    const unsigned char *input_pointer = ((input_buffer)->content + (input_buffer)->offset) + 1;
    const unsigned char *input_end = ((input_buffer)->content + (input_buffer)->offset) + 1;
    unsigned char *output_pointer = 
# 823 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                   ((void *)0)
# 823 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                       ;
    unsigned char *output = 
# 824 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                           ((void *)0)
# 824 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                               ;


    if (((input_buffer)->content + (input_buffer)->offset)[0] != '\"')
    {
        goto fail;
    }

    {

        size_t allocation_length = 0;
        size_t skipped_bytes = 0;
        while (((size_t)(input_end - input_buffer->content) < input_buffer->length) && (*input_end != '\"'))
        {

            if (input_end[0] == '\\')
            {
                if ((size_t)(input_end + 1 - input_buffer->content) >= input_buffer->length)
                {

                    goto fail;
                }
                skipped_bytes++;
                input_end++;
            }
            input_end++;
        }
        if (((size_t)(input_end - input_buffer->content) >= input_buffer->length) || (*input_end != '\"'))
        {
            goto fail;
        }


        allocation_length = (size_t) (input_end - ((input_buffer)->content + (input_buffer)->offset)) - skipped_bytes;
        output = (unsigned char*)input_buffer->hooks.allocate(allocation_length + sizeof(""));
        if (output == 
# 859 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                     ((void *)0)
# 859 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                         )
        {
            goto fail;
        }
    }

    output_pointer = output;

    while (input_pointer < input_end)
    {
        if (*input_pointer != '\\')
        {
            *output_pointer++ = *input_pointer++;
        }

        else
        {
            unsigned char sequence_length = 2;
            if ((input_end - input_pointer) < 1)
            {
                goto fail;
            }

            switch (input_pointer[1])
            {
                case 'b':
                    *output_pointer++ = '\b';
                    break;
                case 'f':
                    *output_pointer++ = '\f';
                    break;
                case 'n':
                    *output_pointer++ = '\n';
                    break;
                case 'r':
                    *output_pointer++ = '\r';
                    break;
                case 't':
                    *output_pointer++ = '\t';
                    break;
                case '\"':
                case '\\':
                case '/':
                    *output_pointer++ = input_pointer[1];
                    break;


                case 'u':
                    sequence_length = utf16_literal_to_utf8(input_pointer, input_end, &output_pointer);
                    if (sequence_length == 0)
                    {

                        goto fail;
                    }
                    break;

                default:
                    goto fail;
            }
            input_pointer += sequence_length;
        }
    }


    *output_pointer = '\0';

    item->type = (1 << 4);
    item->valuestring = (char*)output;

    input_buffer->offset = (size_t) (input_end - input_buffer->content);
    input_buffer->offset++;

    return ((cJSON_bool)1);

fail:
    if (output != 
# 934 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                 ((void *)0)
# 934 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                     )
    {
        input_buffer->hooks.deallocate(output);
        output = 
# 937 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 937 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    ;
    }

    if (input_pointer != 
# 940 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                        ((void *)0)
# 940 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                            )
    {
        input_buffer->offset = (size_t)(input_pointer - input_buffer->content);
    }

    return ((cJSON_bool)0);
}


static cJSON_bool print_string_ptr(const unsigned char * const input, printbuffer * const output_buffer)
{
    const unsigned char *input_pointer = 
# 951 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                        ((void *)0)
# 951 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                            ;
    unsigned char *output = 
# 952 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                           ((void *)0)
# 952 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                               ;
    unsigned char *output_pointer = 
# 953 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                   ((void *)0)
# 953 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                       ;
    size_t output_length = 0;

    size_t escape_characters = 0;

    if (output_buffer == 
# 958 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                        ((void *)0)
# 958 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                            )
    {
        return ((cJSON_bool)0);
    }


    if (input == 
# 964 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 964 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    )
    {
        output = ensure(output_buffer, sizeof("\"\""));
        if (output == 
# 967 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                     ((void *)0)
# 967 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                         )
        {
            return ((cJSON_bool)0);
        }
        strcpy((char*)output, "\"\"");

        return ((cJSON_bool)1);
    }


    for (input_pointer = input; *input_pointer; input_pointer++)
    {
        switch (*input_pointer)
        {
            case '\"':
            case '\\':
            case '\b':
            case '\f':
            case '\n':
            case '\r':
            case '\t':

                escape_characters++;
                break;
            default:
                if (*input_pointer < 32)
                {

                    escape_characters += 5;
                }
                break;
        }
    }
    output_length = (size_t)(input_pointer - input) + escape_characters;

    output = ensure(output_buffer, output_length + sizeof("\"\""));
    if (output == 
# 1003 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                 ((void *)0)
# 1003 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                     )
    {
        return ((cJSON_bool)0);
    }


    if (escape_characters == 0)
    {
        output[0] = '\"';
        memcpy(output + 1, input, output_length);
        output[output_length + 1] = '\"';
        output[output_length + 2] = '\0';

        return ((cJSON_bool)1);
    }

    output[0] = '\"';
    output_pointer = output + 1;

    for (input_pointer = input; *input_pointer != '\0'; (void)input_pointer++, output_pointer++)
    {
        if ((*input_pointer > 31) && (*input_pointer != '\"') && (*input_pointer != '\\'))
        {

            *output_pointer = *input_pointer;
        }
        else
        {

            *output_pointer++ = '\\';
            switch (*input_pointer)
            {
                case '\\':
                    *output_pointer = '\\';
                    break;
                case '\"':
                    *output_pointer = '\"';
                    break;
                case '\b':
                    *output_pointer = 'b';
                    break;
                case '\f':
                    *output_pointer = 'f';
                    break;
                case '\n':
                    *output_pointer = 'n';
                    break;
                case '\r':
                    *output_pointer = 'r';
                    break;
                case '\t':
                    *output_pointer = 't';
                    break;
                default:

                    sprintf((char*)output_pointer, "u%04x", *input_pointer);
                    output_pointer += 4;
                    break;
            }
        }
    }
    output[output_length + 1] = '\"';
    output[output_length + 2] = '\0';

    return ((cJSON_bool)1);
}


static cJSON_bool print_string(const cJSON * const item, printbuffer * const p)
{
    return print_string_ptr((unsigned char*)item->valuestring, p);
}


static cJSON_bool parse_value(cJSON * const item, parse_buffer * const input_buffer);
static cJSON_bool print_value(const cJSON * const item, printbuffer * const output_buffer);
static cJSON_bool parse_array(cJSON * const item, parse_buffer * const input_buffer);
static cJSON_bool print_array(const cJSON * const item, printbuffer * const output_buffer);
static cJSON_bool parse_object(cJSON * const item, parse_buffer * const input_buffer);
static cJSON_bool print_object(const cJSON * const item, printbuffer * const output_buffer);


static parse_buffer *buffer_skip_whitespace(parse_buffer * const buffer)
{
    if ((buffer == 
# 1087 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 1087 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ) || (buffer->content == 
# 1087 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                               ((void *)0)
# 1087 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                   ))
    {
        return 
# 1089 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 1089 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    if ((!((buffer != 
# 1092 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
       ((void *)0)
# 1092 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
       ) && (((buffer)->offset + 0) < (buffer)->length))))
    {
        return buffer;
    }

    while (((buffer != 
# 1097 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          ((void *)0)
# 1097 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
          ) && (((buffer)->offset + 0) < (buffer)->length)) && (((buffer)->content + (buffer)->offset)[0] <= 32))
    {
       buffer->offset++;
    }

    if (buffer->offset == buffer->length)
    {
        buffer->offset--;
    }

    return buffer;
}


static parse_buffer *skip_utf8_bom(parse_buffer * const buffer)
{
    if ((buffer == 
# 1113 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 1113 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ) || (buffer->content == 
# 1113 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                               ((void *)0)
# 1113 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                   ) || (buffer->offset != 0))
    {
        return 
# 1115 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 1115 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    if (((buffer != 
# 1118 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
       ((void *)0)
# 1118 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
       ) && (((buffer)->offset + 4) < (buffer)->length)) && (strncmp((const char*)((buffer)->content + (buffer)->offset), "\xEF\xBB\xBF", 3) == 0))
    {
        buffer->offset += 3;
    }

    return buffer;
}

__attribute__((visibility("default"))) cJSON * cJSON_ParseWithOpts(const char *value, const char **return_parse_end, cJSON_bool require_null_terminated)
{
    size_t buffer_length;

    if (
# 1130 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
       ((void *)0) 
# 1130 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
            == value)
    {
        return 
# 1132 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 1132 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }


    buffer_length = strlen(value) + sizeof("");

    return cJSON_ParseWithLengthOpts(value, buffer_length, return_parse_end, require_null_terminated);
}


__attribute__((visibility("default"))) cJSON * cJSON_ParseWithLengthOpts(const char *value, size_t buffer_length, const char **return_parse_end, cJSON_bool require_null_terminated)
{
    parse_buffer buffer = { 0, 0, 0, 0, { 0, 0, 0 } };
    cJSON *item = 
# 1145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                 ((void *)0)
# 1145 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                     ;


    global_error.json = 
# 1148 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                       ((void *)0)
# 1148 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                           ;
    global_error.position = 0;

    if (value == 
# 1151 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0) 
# 1151 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                     || 0 == buffer_length)
    {
        goto fail;
    }

    buffer.content = (const unsigned char*)value;
    buffer.length = buffer_length;
    buffer.offset = 0;
    buffer.hooks = global_hooks;

    item = cJSON_New_Item(&global_hooks);
    if (item == 
# 1162 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 1162 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        goto fail;
    }

    if (!parse_value(item, buffer_skip_whitespace(skip_utf8_bom(&buffer))))
    {

        goto fail;
    }


    if (require_null_terminated)
    {
        buffer_skip_whitespace(&buffer);
        if ((buffer.offset >= buffer.length) || ((&buffer)->content + (&buffer)->offset)[0] != '\0')
        {
            goto fail;
        }
    }
    if (return_parse_end)
    {
        *return_parse_end = (const char*)((&buffer)->content + (&buffer)->offset);
    }

    return item;

fail:
    if (item != 
# 1190 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 1190 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        cJSON_Delete(item);
    }

    if (value != 
# 1195 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 1195 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    )
    {
        error local_error;
        local_error.json = (const unsigned char*)value;
        local_error.position = 0;

        if (buffer.offset < buffer.length)
        {
            local_error.position = buffer.offset;
        }
        else if (buffer.length > 0)
        {
            local_error.position = buffer.length - 1;
        }

        if (return_parse_end != 
# 1210 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                               ((void *)0)
# 1210 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                   )
        {
            *return_parse_end = (const char*)local_error.json + local_error.position;
        }

        global_error = local_error;
    }

    return 
# 1218 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          ((void *)0)
# 1218 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
              ;
}


__attribute__((visibility("default"))) cJSON * cJSON_Parse(const char *value)
{
    return cJSON_ParseWithOpts(value, 0, 0);
}

__attribute__((visibility("default"))) cJSON * cJSON_ParseWithLength(const char *value, size_t buffer_length)
{
    return cJSON_ParseWithLengthOpts(value, buffer_length, 0, 0);
}



static unsigned char *print(const cJSON * const item, cJSON_bool format, const internal_hooks * const hooks)
{
    static const size_t default_buffer_size = 256;
    printbuffer buffer[1];
    unsigned char *printed = 
# 1238 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                            ((void *)0)
# 1238 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                ;

    memset(buffer, 0, sizeof(buffer));


    buffer->buffer = (unsigned char*) hooks->allocate(default_buffer_size);
    buffer->length = default_buffer_size;
    buffer->format = format;
    buffer->hooks = *hooks;
    if (buffer->buffer == 
# 1247 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                         ((void *)0)
# 1247 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                             )
    {
        goto fail;
    }


    if (!print_value(item, buffer))
    {
        goto fail;
    }
    update_offset(buffer);


    if (hooks->reallocate != 
# 1260 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                            ((void *)0)
# 1260 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                )
    {
        printed = (unsigned char*) hooks->reallocate(buffer->buffer, buffer->offset + 1);
        if (printed == 
# 1263 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                      ((void *)0)
# 1263 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                          ) {
            goto fail;
        }
        buffer->buffer = 
# 1266 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                        ((void *)0)
# 1266 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                            ;
    }
    else
    {
        printed = (unsigned char*) hooks->allocate(buffer->offset + 1);
        if (printed == 
# 1271 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                      ((void *)0)
# 1271 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                          )
        {
            goto fail;
        }
        memcpy(printed, buffer->buffer, (((buffer->length) < (buffer->offset + 1)) ? (buffer->length) : (buffer->offset + 1)));
        printed[buffer->offset] = '\0';


        hooks->deallocate(buffer->buffer);
        buffer->buffer = 
# 1280 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                        ((void *)0)
# 1280 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                            ;
    }

    return printed;

fail:
    if (buffer->buffer != 
# 1286 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                         ((void *)0)
# 1286 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                             )
    {
        hooks->deallocate(buffer->buffer);
        buffer->buffer = 
# 1289 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                        ((void *)0)
# 1289 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                            ;
    }

    if (printed != 
# 1292 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 1292 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      )
    {
        hooks->deallocate(printed);
        printed = 
# 1295 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                 ((void *)0)
# 1295 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                     ;
    }

    return 
# 1298 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          ((void *)0)
# 1298 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
              ;
}


__attribute__((visibility("default"))) char * cJSON_Print(const cJSON *item)
{
    return (char*)print(item, ((cJSON_bool)1), &global_hooks);
}

__attribute__((visibility("default"))) char * cJSON_PrintUnformatted(const cJSON *item)
{
    return (char*)print(item, ((cJSON_bool)0), &global_hooks);
}

__attribute__((visibility("default"))) char * cJSON_PrintBuffered(const cJSON *item, int prebuffer, cJSON_bool fmt)
{
    printbuffer p = { 0, 0, 0, 0, 0, 0, { 0, 0, 0 } };

    if (prebuffer < 0)
    {
        return 
# 1318 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 1318 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    p.buffer = (unsigned char*)global_hooks.allocate((size_t)prebuffer);
    if (!p.buffer)
    {
        return 
# 1324 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 1324 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    p.length = (size_t)prebuffer;
    p.offset = 0;
    p.noalloc = ((cJSON_bool)0);
    p.format = fmt;
    p.hooks = global_hooks;

    if (!print_value(item, &p))
    {
        global_hooks.deallocate(p.buffer);
        p.buffer = 
# 1336 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 1336 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ;
        return 
# 1337 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 1337 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    return (char*)p.buffer;
}

__attribute__((visibility("default"))) cJSON_bool cJSON_PrintPreallocated(cJSON *item, char *buffer, const int length, const cJSON_bool format)
{
    printbuffer p = { 0, 0, 0, 0, 0, 0, { 0, 0, 0 } };

    if ((length < 0) || (buffer == 
# 1347 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                  ((void *)0)
# 1347 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                      ))
    {
        return ((cJSON_bool)0);
    }

    p.buffer = (unsigned char*)buffer;
    p.length = (size_t)length;
    p.offset = 0;
    p.noalloc = ((cJSON_bool)1);
    p.format = format;
    p.hooks = global_hooks;

    return print_value(item, &p);
}


static cJSON_bool parse_value(cJSON * const item, parse_buffer * const input_buffer)
{
    if ((input_buffer == 
# 1365 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                        ((void *)0)
# 1365 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                            ) || (input_buffer->content == 
# 1365 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                                           ((void *)0)
# 1365 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                               ))
    {
        return ((cJSON_bool)0);
    }



    if (((input_buffer != 
# 1372 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
       ((void *)0)
# 1372 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
       ) && (((input_buffer)->offset + 4) <= (input_buffer)->length)) && (strncmp((const char*)((input_buffer)->content + (input_buffer)->offset), "null", 4) == 0))
    {
        item->type = (1 << 2);
        input_buffer->offset += 4;
        return ((cJSON_bool)1);
    }

    if (((input_buffer != 
# 1379 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
       ((void *)0)
# 1379 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
       ) && (((input_buffer)->offset + 5) <= (input_buffer)->length)) && (strncmp((const char*)((input_buffer)->content + (input_buffer)->offset), "false", 5) == 0))
    {
        item->type = (1 << 0);
        input_buffer->offset += 5;
        return ((cJSON_bool)1);
    }

    if (((input_buffer != 
# 1386 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
       ((void *)0)
# 1386 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
       ) && (((input_buffer)->offset + 4) <= (input_buffer)->length)) && (strncmp((const char*)((input_buffer)->content + (input_buffer)->offset), "true", 4) == 0))
    {
        item->type = (1 << 1);
        item->valueint = 1;
        input_buffer->offset += 4;
        return ((cJSON_bool)1);
    }

    if (((input_buffer != 
# 1394 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
       ((void *)0)
# 1394 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
       ) && (((input_buffer)->offset + 0) < (input_buffer)->length)) && (((input_buffer)->content + (input_buffer)->offset)[0] == '\"'))
    {
        return parse_string(item, input_buffer);
    }

    if (((input_buffer != 
# 1399 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
       ((void *)0)
# 1399 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
       ) && (((input_buffer)->offset + 0) < (input_buffer)->length)) && ((((input_buffer)->content + (input_buffer)->offset)[0] == '-') || ((((input_buffer)->content + (input_buffer)->offset)[0] >= '0') && (((input_buffer)->content + (input_buffer)->offset)[0] <= '9'))))
    {
        return parse_number(item, input_buffer);
    }

    if (((input_buffer != 
# 1404 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
       ((void *)0)
# 1404 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
       ) && (((input_buffer)->offset + 0) < (input_buffer)->length)) && (((input_buffer)->content + (input_buffer)->offset)[0] == '['))
    {
        return parse_array(item, input_buffer);
    }

    if (((input_buffer != 
# 1409 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
       ((void *)0)
# 1409 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
       ) && (((input_buffer)->offset + 0) < (input_buffer)->length)) && (((input_buffer)->content + (input_buffer)->offset)[0] == '{'))
    {
        return parse_object(item, input_buffer);
    }

    return ((cJSON_bool)0);
}


static cJSON_bool print_value(const cJSON * const item, printbuffer * const output_buffer)
{
    unsigned char *output = 
# 1420 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                           ((void *)0)
# 1420 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                               ;

    if ((item == 
# 1422 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 1422 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    ) || (output_buffer == 
# 1422 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                           ((void *)0)
# 1422 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                               ))
    {
        return ((cJSON_bool)0);
    }

    switch ((item->type) & 0xFF)
    {
        case (1 << 2):
            output = ensure(output_buffer, 5);
            if (output == 
# 1431 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                         ((void *)0)
# 1431 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                             )
            {
                return ((cJSON_bool)0);
            }
            strcpy((char*)output, "null");
            return ((cJSON_bool)1);

        case (1 << 0):
            output = ensure(output_buffer, 6);
            if (output == 
# 1440 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                         ((void *)0)
# 1440 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                             )
            {
                return ((cJSON_bool)0);
            }
            strcpy((char*)output, "false");
            return ((cJSON_bool)1);

        case (1 << 1):
            output = ensure(output_buffer, 5);
            if (output == 
# 1449 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                         ((void *)0)
# 1449 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                             )
            {
                return ((cJSON_bool)0);
            }
            strcpy((char*)output, "true");
            return ((cJSON_bool)1);

        case (1 << 3):
            return print_number(item, output_buffer);

        case (1 << 7):
        {
            size_t raw_length = 0;
            if (item->valuestring == 
# 1462 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                    ((void *)0)
# 1462 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                        )
            {
                return ((cJSON_bool)0);
            }

            raw_length = strlen(item->valuestring) + sizeof("");
            output = ensure(output_buffer, raw_length);
            if (output == 
# 1469 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                         ((void *)0)
# 1469 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                             )
            {
                return ((cJSON_bool)0);
            }
            memcpy(output, item->valuestring, raw_length);
            return ((cJSON_bool)1);
        }

        case (1 << 4):
            return print_string(item, output_buffer);

        case (1 << 5):
            return print_array(item, output_buffer);

        case (1 << 6):
            return print_object(item, output_buffer);

        default:
            return ((cJSON_bool)0);
    }
}


static cJSON_bool parse_array(cJSON * const item, parse_buffer * const input_buffer)
{
    cJSON *head = 
# 1494 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                 ((void *)0)
# 1494 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                     ;
    cJSON *current_item = 
# 1495 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                         ((void *)0)
# 1495 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                             ;

    if (input_buffer->depth >= 1000)
    {
        return ((cJSON_bool)0);
    }
    input_buffer->depth++;

    if (((input_buffer)->content + (input_buffer)->offset)[0] != '[')
    {

        goto fail;
    }

    input_buffer->offset++;
    buffer_skip_whitespace(input_buffer);
    if (((input_buffer != 
# 1511 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
       ((void *)0)
# 1511 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
       ) && (((input_buffer)->offset + 0) < (input_buffer)->length)) && (((input_buffer)->content + (input_buffer)->offset)[0] == ']'))
    {

        goto success;
    }


    if ((!((input_buffer != 
# 1518 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
       ((void *)0)
# 1518 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
       ) && (((input_buffer)->offset + 0) < (input_buffer)->length))))
    {
        input_buffer->offset--;
        goto fail;
    }


    input_buffer->offset--;

    do
    {

        cJSON *new_item = cJSON_New_Item(&(input_buffer->hooks));
        if (new_item == 
# 1531 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                       ((void *)0)
# 1531 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                           )
        {
            goto fail;
        }


        if (head == 
# 1537 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                   ((void *)0)
# 1537 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                       )
        {

            current_item = head = new_item;
        }
        else
        {

            current_item->next = new_item;
            new_item->prev = current_item;
            current_item = new_item;
        }


        input_buffer->offset++;
        buffer_skip_whitespace(input_buffer);
        if (!parse_value(current_item, input_buffer))
        {
            goto fail;
        }
        buffer_skip_whitespace(input_buffer);
    }
    while (((input_buffer != 
# 1559 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          ((void *)0)
# 1559 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
          ) && (((input_buffer)->offset + 0) < (input_buffer)->length)) && (((input_buffer)->content + (input_buffer)->offset)[0] == ','));

    if ((!((input_buffer != 
# 1561 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
       ((void *)0)
# 1561 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
       ) && (((input_buffer)->offset + 0) < (input_buffer)->length))) || ((input_buffer)->content + (input_buffer)->offset)[0] != ']')
    {
        goto fail;
    }

success:
    input_buffer->depth--;

    if (head != 
# 1569 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 1569 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   ) {
        head->prev = current_item;
    }

    item->type = (1 << 5);
    item->child = head;

    input_buffer->offset++;

    return ((cJSON_bool)1);

fail:
    if (head != 
# 1581 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 1581 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        cJSON_Delete(head);
    }

    return ((cJSON_bool)0);
}


static cJSON_bool print_array(const cJSON * const item, printbuffer * const output_buffer)
{
    unsigned char *output_pointer = 
# 1592 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                   ((void *)0)
# 1592 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                       ;
    size_t length = 0;
    cJSON *current_element = item->child;

    if (output_buffer == 
# 1596 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                        ((void *)0)
# 1596 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                            )
    {
        return ((cJSON_bool)0);
    }



    output_pointer = ensure(output_buffer, 1);
    if (output_pointer == 
# 1604 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                         ((void *)0)
# 1604 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                             )
    {
        return ((cJSON_bool)0);
    }

    *output_pointer = '[';
    output_buffer->offset++;
    output_buffer->depth++;

    while (current_element != 
# 1613 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                             ((void *)0)
# 1613 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                 )
    {
        if (!print_value(current_element, output_buffer))
        {
            return ((cJSON_bool)0);
        }
        update_offset(output_buffer);
        if (current_element->next)
        {
            length = (size_t) (output_buffer->format ? 2 : 1);
            output_pointer = ensure(output_buffer, length + 1);
            if (output_pointer == 
# 1624 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                 ((void *)0)
# 1624 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                     )
            {
                return ((cJSON_bool)0);
            }
            *output_pointer++ = ',';
            if(output_buffer->format)
            {
                *output_pointer++ = ' ';
            }
            *output_pointer = '\0';
            output_buffer->offset += length;
        }
        current_element = current_element->next;
    }

    output_pointer = ensure(output_buffer, 2);
    if (output_pointer == 
# 1640 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                         ((void *)0)
# 1640 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                             )
    {
        return ((cJSON_bool)0);
    }
    *output_pointer++ = ']';
    *output_pointer = '\0';
    output_buffer->depth--;

    return ((cJSON_bool)1);
}


static cJSON_bool parse_object(cJSON * const item, parse_buffer * const input_buffer)
{
    cJSON *head = 
# 1654 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                 ((void *)0)
# 1654 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                     ;
    cJSON *current_item = 
# 1655 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                         ((void *)0)
# 1655 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                             ;

    if (input_buffer->depth >= 1000)
    {
        return ((cJSON_bool)0);
    }
    input_buffer->depth++;

    if ((!((input_buffer != 
# 1663 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
       ((void *)0)
# 1663 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
       ) && (((input_buffer)->offset + 0) < (input_buffer)->length))) || (((input_buffer)->content + (input_buffer)->offset)[0] != '{'))
    {
        goto fail;
    }

    input_buffer->offset++;
    buffer_skip_whitespace(input_buffer);
    if (((input_buffer != 
# 1670 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
       ((void *)0)
# 1670 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
       ) && (((input_buffer)->offset + 0) < (input_buffer)->length)) && (((input_buffer)->content + (input_buffer)->offset)[0] == '}'))
    {
        goto success;
    }


    if ((!((input_buffer != 
# 1676 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
       ((void *)0)
# 1676 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
       ) && (((input_buffer)->offset + 0) < (input_buffer)->length))))
    {
        input_buffer->offset--;
        goto fail;
    }


    input_buffer->offset--;

    do
    {

        cJSON *new_item = cJSON_New_Item(&(input_buffer->hooks));
        if (new_item == 
# 1689 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                       ((void *)0)
# 1689 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                           )
        {
            goto fail;
        }


        if (head == 
# 1695 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                   ((void *)0)
# 1695 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                       )
        {

            current_item = head = new_item;
        }
        else
        {

            current_item->next = new_item;
            new_item->prev = current_item;
            current_item = new_item;
        }

        if ((!((input_buffer != 
# 1708 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
           ((void *)0)
# 1708 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
           ) && (((input_buffer)->offset + 1) < (input_buffer)->length))))
        {
            goto fail;
        }


        input_buffer->offset++;
        buffer_skip_whitespace(input_buffer);
        if (!parse_string(current_item, input_buffer))
        {
            goto fail;
        }
        buffer_skip_whitespace(input_buffer);


        current_item->string = current_item->valuestring;
        current_item->valuestring = 
# 1724 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                   ((void *)0)
# 1724 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                       ;

        if ((!((input_buffer != 
# 1726 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
           ((void *)0)
# 1726 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
           ) && (((input_buffer)->offset + 0) < (input_buffer)->length))) || (((input_buffer)->content + (input_buffer)->offset)[0] != ':'))
        {
            goto fail;
        }


        input_buffer->offset++;
        buffer_skip_whitespace(input_buffer);
        if (!parse_value(current_item, input_buffer))
        {
            goto fail;
        }
        buffer_skip_whitespace(input_buffer);
    }
    while (((input_buffer != 
# 1740 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          ((void *)0)
# 1740 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
          ) && (((input_buffer)->offset + 0) < (input_buffer)->length)) && (((input_buffer)->content + (input_buffer)->offset)[0] == ','));

    if ((!((input_buffer != 
# 1742 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
       ((void *)0)
# 1742 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
       ) && (((input_buffer)->offset + 0) < (input_buffer)->length))) || (((input_buffer)->content + (input_buffer)->offset)[0] != '}'))
    {
        goto fail;
    }

success:
    input_buffer->depth--;

    if (head != 
# 1750 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 1750 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   ) {
        head->prev = current_item;
    }

    item->type = (1 << 6);
    item->child = head;

    input_buffer->offset++;
    return ((cJSON_bool)1);

fail:
    if (head != 
# 1761 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 1761 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        cJSON_Delete(head);
    }

    return ((cJSON_bool)0);
}


static cJSON_bool print_object(const cJSON * const item, printbuffer * const output_buffer)
{
    unsigned char *output_pointer = 
# 1772 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                   ((void *)0)
# 1772 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                       ;
    size_t length = 0;
    cJSON *current_item = item->child;

    if (output_buffer == 
# 1776 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                        ((void *)0)
# 1776 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                            )
    {
        return ((cJSON_bool)0);
    }


    length = (size_t) (output_buffer->format ? 2 : 1);
    output_pointer = ensure(output_buffer, length + 1);
    if (output_pointer == 
# 1784 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                         ((void *)0)
# 1784 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                             )
    {
        return ((cJSON_bool)0);
    }

    *output_pointer++ = '{';
    output_buffer->depth++;
    if (output_buffer->format)
    {
        *output_pointer++ = '\n';
    }
    output_buffer->offset += length;

    while (current_item)
    {
        if (output_buffer->format)
        {
            size_t i;
            output_pointer = ensure(output_buffer, output_buffer->depth);
            if (output_pointer == 
# 1803 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                 ((void *)0)
# 1803 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                     )
            {
                return ((cJSON_bool)0);
            }
            for (i = 0; i < output_buffer->depth; i++)
            {
                *output_pointer++ = '\t';
            }
            output_buffer->offset += output_buffer->depth;
        }


        if (!print_string_ptr((unsigned char*)current_item->string, output_buffer))
        {
            return ((cJSON_bool)0);
        }
        update_offset(output_buffer);

        length = (size_t) (output_buffer->format ? 2 : 1);
        output_pointer = ensure(output_buffer, length);
        if (output_pointer == 
# 1823 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                             ((void *)0)
# 1823 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                 )
        {
            return ((cJSON_bool)0);
        }
        *output_pointer++ = ':';
        if (output_buffer->format)
        {
            *output_pointer++ = '\t';
        }
        output_buffer->offset += length;


        if (!print_value(current_item, output_buffer))
        {
            return ((cJSON_bool)0);
        }
        update_offset(output_buffer);


        length = ((size_t)(output_buffer->format ? 1 : 0) + (size_t)(current_item->next ? 1 : 0));
        output_pointer = ensure(output_buffer, length + 1);
        if (output_pointer == 
# 1844 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                             ((void *)0)
# 1844 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                 )
        {
            return ((cJSON_bool)0);
        }
        if (current_item->next)
        {
            *output_pointer++ = ',';
        }

        if (output_buffer->format)
        {
            *output_pointer++ = '\n';
        }
        *output_pointer = '\0';
        output_buffer->offset += length;

        current_item = current_item->next;
    }

    output_pointer = ensure(output_buffer, output_buffer->format ? (output_buffer->depth + 1) : 2);
    if (output_pointer == 
# 1864 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                         ((void *)0)
# 1864 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                             )
    {
        return ((cJSON_bool)0);
    }
    if (output_buffer->format)
    {
        size_t i;
        for (i = 0; i < (output_buffer->depth - 1); i++)
        {
            *output_pointer++ = '\t';
        }
    }
    *output_pointer++ = '}';
    *output_pointer = '\0';
    output_buffer->depth--;

    return ((cJSON_bool)1);
}


__attribute__((visibility("default"))) int cJSON_GetArraySize(const cJSON *array)
{
    cJSON *child = 
# 1886 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 1886 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ;
    size_t size = 0;

    if (array == 
# 1889 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 1889 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    )
    {
        return 0;
    }

    child = array->child;

    while(child != 
# 1896 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 1896 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      )
    {
        size++;
        child = child->next;
    }



    return (int)size;
}

static cJSON* get_array_item(const cJSON *array, size_t index)
{
    cJSON *current_child = 
# 1909 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                          ((void *)0)
# 1909 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                              ;

    if (array == 
# 1911 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 1911 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    )
    {
        return 
# 1913 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 1913 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    current_child = array->child;
    while ((current_child != 
# 1917 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                            ((void *)0)
# 1917 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                ) && (index > 0))
    {
        index--;
        current_child = current_child->next;
    }

    return current_child;
}

__attribute__((visibility("default"))) cJSON * cJSON_GetArrayItem(const cJSON *array, int index)
{
    if (index < 0)
    {
        return 
# 1930 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 1930 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    return get_array_item(array, (size_t)index);
}

static cJSON *get_object_item(const cJSON * const object, const char * const name, const cJSON_bool case_sensitive)
{
    cJSON *current_element = 
# 1938 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                            ((void *)0)
# 1938 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                ;

    if ((object == 
# 1940 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 1940 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ) || (name == 
# 1940 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                    ((void *)0)
# 1940 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                        ))
    {
        return 
# 1942 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 1942 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    current_element = object->child;
    if (case_sensitive)
    {
        while ((current_element != 
# 1948 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                  ((void *)0)
# 1948 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                      ) && (current_element->string != 
# 1948 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                                                       ((void *)0)
# 1948 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                                           ) && (strcmp(name, current_element->string) != 0))
        {
            current_element = current_element->next;
        }
    }
    else
    {
        while ((current_element != 
# 1955 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                  ((void *)0)
# 1955 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                      ) && (case_insensitive_strcmp((const unsigned char*)name, (const unsigned char*)(current_element->string)) != 0))
        {
            current_element = current_element->next;
        }
    }

    if ((current_element == 
# 1961 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                           ((void *)0)
# 1961 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                               ) || (current_element->string == 
# 1961 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                                                ((void *)0)
# 1961 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                                    )) {
        return 
# 1962 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 1962 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    return current_element;
}

__attribute__((visibility("default"))) cJSON * cJSON_GetObjectItem(const cJSON * const object, const char * const string)
{
    return get_object_item(object, string, ((cJSON_bool)0));
}

__attribute__((visibility("default"))) cJSON * cJSON_GetObjectItemCaseSensitive(const cJSON * const object, const char * const string)
{
    return get_object_item(object, string, ((cJSON_bool)1));
}

__attribute__((visibility("default"))) cJSON_bool cJSON_HasObjectItem(const cJSON *object, const char *string)
{
    return cJSON_GetObjectItem(object, string) ? 1 : 0;
}


static void suffix_object(cJSON *prev, cJSON *item)
{
    prev->next = item;
    item->prev = prev;
}


static cJSON *create_reference(const cJSON *item, const internal_hooks * const hooks)
{
    cJSON *reference = 
# 1993 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                      ((void *)0)
# 1993 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                          ;
    if (item == 
# 1994 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 1994 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return 
# 1996 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 1996 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    reference = cJSON_New_Item(hooks);
    if (reference == 
# 2000 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                    ((void *)0)
# 2000 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                        )
    {
        return 
# 2002 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 2002 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    memcpy(reference, item, sizeof(cJSON));
    reference->string = 
# 2006 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                       ((void *)0)
# 2006 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                           ;
    reference->type |= 256;
    reference->next = reference->prev = 
# 2008 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                       ((void *)0)
# 2008 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                           ;
    return reference;
}

static cJSON_bool add_item_to_array(cJSON *array, cJSON *item)
{
    cJSON *child = 
# 2014 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 2014 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ;

    if ((item == 
# 2016 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 2016 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    ) || (array == 
# 2016 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                   ((void *)0)
# 2016 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                       ) || (array == item))
    {
        return ((cJSON_bool)0);
    }

    child = array->child;



    if (child == 
# 2025 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 2025 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    )
    {

        array->child = item;
        item->prev = item;
        item->next = 
# 2030 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                    ((void *)0)
# 2030 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                        ;
    }
    else
    {

        if (child->prev)
        {
            suffix_object(child->prev, item);
            array->child->prev = item;
        }
    }

    return ((cJSON_bool)1);
}


__attribute__((visibility("default"))) cJSON_bool cJSON_AddItemToArray(cJSON *array, cJSON *item)
{
    return add_item_to_array(array, item);
}


#pragma GCC diagnostic push


#pragma GCC diagnostic ignored "-Wcast-qual"


static void* cast_away_const(const void* string)
{
    return (void*)string;
}

#pragma GCC diagnostic pop



static cJSON_bool add_item_to_object(cJSON * const object, const char * const string, cJSON * const item, const internal_hooks * const hooks, const cJSON_bool constant_key)
{
    char *new_key = 
# 2069 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                   ((void *)0)
# 2069 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                       ;
    int new_type = (0);

    if ((object == 
# 2072 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 2072 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ) || (string == 
# 2072 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                      ((void *)0)
# 2072 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                          ) || (item == 
# 2072 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                                        ((void *)0)
# 2072 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                            ) || (object == item))
    {
        return ((cJSON_bool)0);
    }

    if (constant_key)
    {
        new_key = (char*)cast_away_const(string);
        new_type = item->type | 512;
    }
    else
    {
        new_key = (char*)cJSON_strdup((const unsigned char*)string, hooks);
        if (new_key == 
# 2085 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                      ((void *)0)
# 2085 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                          )
        {
            return ((cJSON_bool)0);
        }

        new_type = item->type & ~512;
    }

    if (!(item->type & 512) && (item->string != 
# 2093 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                                               ((void *)0)
# 2093 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                                   ))
    {
        hooks->deallocate(item->string);
    }

    item->string = new_key;
    item->type = new_type;

    return add_item_to_array(object, item);
}

__attribute__((visibility("default"))) cJSON_bool cJSON_AddItemToObject(cJSON *object, const char *string, cJSON *item)
{
    return add_item_to_object(object, string, item, &global_hooks, ((cJSON_bool)0));
}


__attribute__((visibility("default"))) cJSON_bool cJSON_AddItemToObjectCS(cJSON *object, const char *string, cJSON *item)
{
    return add_item_to_object(object, string, item, &global_hooks, ((cJSON_bool)1));
}

__attribute__((visibility("default"))) cJSON_bool cJSON_AddItemReferenceToArray(cJSON *array, cJSON *item)
{
    if (array == 
# 2117 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 2117 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    )
    {
        return ((cJSON_bool)0);
    }

    return add_item_to_array(array, create_reference(item, &global_hooks));
}

__attribute__((visibility("default"))) cJSON_bool cJSON_AddItemReferenceToObject(cJSON *object, const char *string, cJSON *item)
{
    if ((object == 
# 2127 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 2127 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ) || (string == 
# 2127 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                      ((void *)0)
# 2127 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                          ))
    {
        return ((cJSON_bool)0);
    }

    return add_item_to_object(object, string, create_reference(item, &global_hooks), &global_hooks, ((cJSON_bool)0));
}

__attribute__((visibility("default"))) cJSON* cJSON_AddNullToObject(cJSON * const object, const char * const name)
{
    cJSON *null = cJSON_CreateNull();
    if (add_item_to_object(object, name, null, &global_hooks, ((cJSON_bool)0)))
    {
        return null;
    }

    cJSON_Delete(null);
    return 
# 2144 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          ((void *)0)
# 2144 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
              ;
}

__attribute__((visibility("default"))) cJSON* cJSON_AddTrueToObject(cJSON * const object, const char * const name)
{
    cJSON *true_item = cJSON_CreateTrue();
    if (add_item_to_object(object, name, true_item, &global_hooks, ((cJSON_bool)0)))
    {
        return true_item;
    }

    cJSON_Delete(true_item);
    return 
# 2156 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          ((void *)0)
# 2156 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
              ;
}

__attribute__((visibility("default"))) cJSON* cJSON_AddFalseToObject(cJSON * const object, const char * const name)
{
    cJSON *false_item = cJSON_CreateFalse();
    if (add_item_to_object(object, name, false_item, &global_hooks, ((cJSON_bool)0)))
    {
        return false_item;
    }

    cJSON_Delete(false_item);
    return 
# 2168 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          ((void *)0)
# 2168 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
              ;
}

__attribute__((visibility("default"))) cJSON* cJSON_AddBoolToObject(cJSON * const object, const char * const name, const cJSON_bool boolean)
{
    cJSON *bool_item = cJSON_CreateBool(boolean);
    if (add_item_to_object(object, name, bool_item, &global_hooks, ((cJSON_bool)0)))
    {
        return bool_item;
    }

    cJSON_Delete(bool_item);
    return 
# 2180 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          ((void *)0)
# 2180 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
              ;
}

__attribute__((visibility("default"))) cJSON* cJSON_AddNumberToObject(cJSON * const object, const char * const name, const double number)
{
    cJSON *number_item = cJSON_CreateNumber(number);
    if (add_item_to_object(object, name, number_item, &global_hooks, ((cJSON_bool)0)))
    {
        return number_item;
    }

    cJSON_Delete(number_item);
    return 
# 2192 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          ((void *)0)
# 2192 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
              ;
}

__attribute__((visibility("default"))) cJSON* cJSON_AddStringToObject(cJSON * const object, const char * const name, const char * const string)
{
    cJSON *string_item = cJSON_CreateString(string);
    if (add_item_to_object(object, name, string_item, &global_hooks, ((cJSON_bool)0)))
    {
        return string_item;
    }

    cJSON_Delete(string_item);
    return 
# 2204 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          ((void *)0)
# 2204 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
              ;
}

__attribute__((visibility("default"))) cJSON* cJSON_AddRawToObject(cJSON * const object, const char * const name, const char * const raw)
{
    cJSON *raw_item = cJSON_CreateRaw(raw);
    if (add_item_to_object(object, name, raw_item, &global_hooks, ((cJSON_bool)0)))
    {
        return raw_item;
    }

    cJSON_Delete(raw_item);
    return 
# 2216 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          ((void *)0)
# 2216 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
              ;
}

__attribute__((visibility("default"))) cJSON* cJSON_AddObjectToObject(cJSON * const object, const char * const name)
{
    cJSON *object_item = cJSON_CreateObject();
    if (add_item_to_object(object, name, object_item, &global_hooks, ((cJSON_bool)0)))
    {
        return object_item;
    }

    cJSON_Delete(object_item);
    return 
# 2228 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          ((void *)0)
# 2228 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
              ;
}

__attribute__((visibility("default"))) cJSON* cJSON_AddArrayToObject(cJSON * const object, const char * const name)
{
    cJSON *array = cJSON_CreateArray();
    if (add_item_to_object(object, name, array, &global_hooks, ((cJSON_bool)0)))
    {
        return array;
    }

    cJSON_Delete(array);
    return 
# 2240 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          ((void *)0)
# 2240 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
              ;
}

__attribute__((visibility("default"))) cJSON * cJSON_DetachItemViaPointer(cJSON *parent, cJSON * const item)
{
    if ((parent == 
# 2245 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 2245 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ) || (item == 
# 2245 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                    ((void *)0)
# 2245 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                        ) || (item != parent->child && item->prev == 
# 2245 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                                                                     ((void *)0)
# 2245 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                                                         ))
    {
        return 
# 2247 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 2247 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    if (item != parent->child)
    {

        item->prev->next = item->next;
    }
    if (item->next != 
# 2255 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                     ((void *)0)
# 2255 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                         )
    {

        item->next->prev = item->prev;
    }

    if (item == parent->child)
    {

        parent->child = item->next;
    }
    else if (item->next == 
# 2266 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                          ((void *)0)
# 2266 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                              )
    {

        parent->child->prev = item->prev;
    }


    item->prev = 
# 2273 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 2273 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    ;
    item->next = 
# 2274 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 2274 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    ;

    return item;
}

__attribute__((visibility("default"))) cJSON * cJSON_DetachItemFromArray(cJSON *array, int which)
{
    if (which < 0)
    {
        return 
# 2283 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 2283 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    return cJSON_DetachItemViaPointer(array, get_array_item(array, (size_t)which));
}

__attribute__((visibility("default"))) void cJSON_DeleteItemFromArray(cJSON *array, int which)
{
    cJSON_Delete(cJSON_DetachItemFromArray(array, which));
}

__attribute__((visibility("default"))) cJSON * cJSON_DetachItemFromObject(cJSON *object, const char *string)
{
    cJSON *to_detach = cJSON_GetObjectItem(object, string);

    return cJSON_DetachItemViaPointer(object, to_detach);
}

__attribute__((visibility("default"))) cJSON * cJSON_DetachItemFromObjectCaseSensitive(cJSON *object, const char *string)
{
    cJSON *to_detach = cJSON_GetObjectItemCaseSensitive(object, string);

    return cJSON_DetachItemViaPointer(object, to_detach);
}

__attribute__((visibility("default"))) void cJSON_DeleteItemFromObject(cJSON *object, const char *string)
{
    cJSON_Delete(cJSON_DetachItemFromObject(object, string));
}

__attribute__((visibility("default"))) void cJSON_DeleteItemFromObjectCaseSensitive(cJSON *object, const char *string)
{
    cJSON_Delete(cJSON_DetachItemFromObjectCaseSensitive(object, string));
}


__attribute__((visibility("default"))) cJSON_bool cJSON_InsertItemInArray(cJSON *array, int which, cJSON *newitem)
{
    cJSON *after_inserted = 
# 2321 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                           ((void *)0)
# 2321 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                               ;

    if (which < 0 || newitem == 
# 2323 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                               ((void *)0)
# 2323 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                   )
    {
        return ((cJSON_bool)0);
    }

    after_inserted = get_array_item(array, (size_t)which);
    if (after_inserted == 
# 2329 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                         ((void *)0)
# 2329 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                             )
    {
        return add_item_to_array(array, newitem);
    }

    if (after_inserted != array->child && after_inserted->prev == 
# 2334 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                                                 ((void *)0)
# 2334 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                                     ) {

        return ((cJSON_bool)0);
    }

    newitem->next = after_inserted;
    newitem->prev = after_inserted->prev;
    after_inserted->prev = newitem;
    if (after_inserted == array->child)
    {
        array->child = newitem;
    }
    else
    {
        newitem->prev->next = newitem;
    }
    return ((cJSON_bool)1);
}

__attribute__((visibility("default"))) cJSON_bool cJSON_ReplaceItemViaPointer(cJSON * const parent, cJSON * const item, cJSON * replacement)
{
    if ((parent == 
# 2355 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 2355 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ) || (parent->child == 
# 2355 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                             ((void *)0)
# 2355 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                 ) || (replacement == 
# 2355 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                                                      ((void *)0)
# 2355 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                                          ) || (item == 
# 2355 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                                                                        ((void *)0)
# 2355 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                                                            ))
    {
        return ((cJSON_bool)0);
    }

    if (replacement == item)
    {
        return ((cJSON_bool)1);
    }

    replacement->next = item->next;
    replacement->prev = item->prev;

    if (replacement->next != 
# 2368 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                            ((void *)0)
# 2368 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                )
    {
        replacement->next->prev = replacement;
    }
    if (parent->child == item)
    {
        if (parent->child->prev == parent->child)
        {
            replacement->prev = replacement;
        }
        parent->child = replacement;
    }
    else
    {



        if (replacement->prev != 
# 2385 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                ((void *)0)
# 2385 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                    )
        {
            replacement->prev->next = replacement;
        }
        if (replacement->next == 
# 2389 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                ((void *)0)
# 2389 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                    )
        {
            parent->child->prev = replacement;
        }
    }

    item->next = 
# 2395 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 2395 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    ;
    item->prev = 
# 2396 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                ((void *)0)
# 2396 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                    ;
    cJSON_Delete(item);

    return ((cJSON_bool)1);
}

__attribute__((visibility("default"))) cJSON_bool cJSON_ReplaceItemInArray(cJSON *array, int which, cJSON *newitem)
{
    if (which < 0)
    {
        return ((cJSON_bool)0);
    }

    return cJSON_ReplaceItemViaPointer(array, get_array_item(array, (size_t)which), newitem);
}

static cJSON_bool replace_item_in_object(cJSON *object, const char *string, cJSON *replacement, cJSON_bool case_sensitive)
{
    if ((replacement == 
# 2414 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                       ((void *)0)
# 2414 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                           ) || (string == 
# 2414 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                           ((void *)0)
# 2414 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                               ))
    {
        return ((cJSON_bool)0);
    }


    if (!(replacement->type & 512) && (replacement->string != 
# 2420 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                                                             ((void *)0)
# 2420 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                                                 ))
    {
        cJSON_free(replacement->string);
    }
    replacement->string = (char*)cJSON_strdup((const unsigned char*)string, &global_hooks);
    if (replacement->string == 
# 2425 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              ((void *)0)
# 2425 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                  )
    {
        return ((cJSON_bool)0);
    }

    replacement->type &= ~512;

    return cJSON_ReplaceItemViaPointer(object, get_object_item(object, string, case_sensitive), replacement);
}

__attribute__((visibility("default"))) cJSON_bool cJSON_ReplaceItemInObject(cJSON *object, const char *string, cJSON *newitem)
{
    return replace_item_in_object(object, string, newitem, ((cJSON_bool)0));
}

__attribute__((visibility("default"))) cJSON_bool cJSON_ReplaceItemInObjectCaseSensitive(cJSON *object, const char *string, cJSON *newitem)
{
    return replace_item_in_object(object, string, newitem, ((cJSON_bool)1));
}


__attribute__((visibility("default"))) cJSON * cJSON_CreateNull(void)
{
    cJSON *item = cJSON_New_Item(&global_hooks);
    if(item)
    {
        item->type = (1 << 2);
    }

    return item;
}

__attribute__((visibility("default"))) cJSON * cJSON_CreateTrue(void)
{
    cJSON *item = cJSON_New_Item(&global_hooks);
    if(item)
    {
        item->type = (1 << 1);
    }

    return item;
}

__attribute__((visibility("default"))) cJSON * cJSON_CreateFalse(void)
{
    cJSON *item = cJSON_New_Item(&global_hooks);
    if(item)
    {
        item->type = (1 << 0);
    }

    return item;
}

__attribute__((visibility("default"))) cJSON * cJSON_CreateBool(cJSON_bool boolean)
{
    cJSON *item = cJSON_New_Item(&global_hooks);
    if(item)
    {
        item->type = boolean ? (1 << 1) : (1 << 0);
    }

    return item;
}

__attribute__((visibility("default"))) cJSON * cJSON_CreateNumber(double num)
{
    cJSON *item = cJSON_New_Item(&global_hooks);
    if(item)
    {
        item->type = (1 << 3);
        item->valuedouble = num;


        if (num >= 0x7fffffff
# 2499 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                         )
        {
            item->valueint = 0x7fffffff
# 2501 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                   ;
        }
        else if (num <= (double)
# 2503 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                               (-0x7fffffff - 1)
# 2503 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                      )
        {
            item->valueint = 
# 2505 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                            (-0x7fffffff - 1)
# 2505 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                   ;
        }
        else
        {
            item->valueint = (int)num;
        }
    }

    return item;
}

__attribute__((visibility("default"))) cJSON * cJSON_CreateString(const char *string)
{
    cJSON *item = cJSON_New_Item(&global_hooks);
    if(item)
    {
        item->type = (1 << 4);
        item->valuestring = (char*)cJSON_strdup((const unsigned char*)string, &global_hooks);
        if(!item->valuestring)
        {
            cJSON_Delete(item);
            return 
# 2526 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 2526 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ;
        }
    }

    return item;
}

__attribute__((visibility("default"))) cJSON * cJSON_CreateStringReference(const char *string)
{
    cJSON *item = cJSON_New_Item(&global_hooks);
    if (item != 
# 2536 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 2536 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        item->type = (1 << 4) | 256;
        item->valuestring = (char*)cast_away_const(string);
    }

    return item;
}

__attribute__((visibility("default"))) cJSON * cJSON_CreateObjectReference(const cJSON *child)
{
    cJSON *item = cJSON_New_Item(&global_hooks);
    if (item != 
# 2548 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 2548 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   ) {
        item->type = (1 << 6) | 256;
        item->child = (cJSON*)cast_away_const(child);
    }

    return item;
}

__attribute__((visibility("default"))) cJSON * cJSON_CreateArrayReference(const cJSON *child) {
    cJSON *item = cJSON_New_Item(&global_hooks);
    if (item != 
# 2558 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 2558 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   ) {
        item->type = (1 << 5) | 256;
        item->child = (cJSON*)cast_away_const(child);
    }

    return item;
}

__attribute__((visibility("default"))) cJSON * cJSON_CreateRaw(const char *raw)
{
    cJSON *item = cJSON_New_Item(&global_hooks);
    if(item)
    {
        item->type = (1 << 7);
        item->valuestring = (char*)cJSON_strdup((const unsigned char*)raw, &global_hooks);
        if(!item->valuestring)
        {
            cJSON_Delete(item);
            return 
# 2576 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 2576 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ;
        }
    }

    return item;
}

__attribute__((visibility("default"))) cJSON * cJSON_CreateArray(void)
{
    cJSON *item = cJSON_New_Item(&global_hooks);
    if(item)
    {
        item->type=(1 << 5);
    }

    return item;
}

__attribute__((visibility("default"))) cJSON * cJSON_CreateObject(void)
{
    cJSON *item = cJSON_New_Item(&global_hooks);
    if (item)
    {
        item->type = (1 << 6);
    }

    return item;
}


__attribute__((visibility("default"))) cJSON * cJSON_CreateIntArray(const int *numbers, int count)
{
    size_t i = 0;
    cJSON *n = 
# 2609 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 2609 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    cJSON *p = 
# 2610 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 2610 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    cJSON *a = 
# 2611 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 2611 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;

    if ((count < 0) || (numbers == 
# 2613 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                  ((void *)0)
# 2613 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                      ))
    {
        return 
# 2615 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 2615 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    a = cJSON_CreateArray();

    for(i = 0; a && (i < (size_t)count); i++)
    {
        n = cJSON_CreateNumber(numbers[i]);
        if (!n)
        {
            cJSON_Delete(a);
            return 
# 2626 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 2626 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ;
        }
        if(!i)
        {
            a->child = n;
        }
        else
        {
            suffix_object(p, n);
        }
        p = n;
    }

    if (a && a->child) {
        a->child->prev = n;
    }

    return a;
}

__attribute__((visibility("default"))) cJSON * cJSON_CreateFloatArray(const float *numbers, int count)
{
    size_t i = 0;
    cJSON *n = 
# 2649 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 2649 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    cJSON *p = 
# 2650 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 2650 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    cJSON *a = 
# 2651 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 2651 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;

    if ((count < 0) || (numbers == 
# 2653 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                  ((void *)0)
# 2653 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                      ))
    {
        return 
# 2655 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 2655 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    a = cJSON_CreateArray();

    for(i = 0; a && (i < (size_t)count); i++)
    {
        n = cJSON_CreateNumber((double)numbers[i]);
        if(!n)
        {
            cJSON_Delete(a);
            return 
# 2666 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 2666 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ;
        }
        if(!i)
        {
            a->child = n;
        }
        else
        {
            suffix_object(p, n);
        }
        p = n;
    }

    if (a && a->child) {
        a->child->prev = n;
    }

    return a;
}

__attribute__((visibility("default"))) cJSON * cJSON_CreateDoubleArray(const double *numbers, int count)
{
    size_t i = 0;
    cJSON *n = 
# 2689 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 2689 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    cJSON *p = 
# 2690 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 2690 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    cJSON *a = 
# 2691 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 2691 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;

    if ((count < 0) || (numbers == 
# 2693 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                  ((void *)0)
# 2693 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                      ))
    {
        return 
# 2695 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 2695 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    a = cJSON_CreateArray();

    for(i = 0; a && (i < (size_t)count); i++)
    {
        n = cJSON_CreateNumber(numbers[i]);
        if(!n)
        {
            cJSON_Delete(a);
            return 
# 2706 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 2706 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ;
        }
        if(!i)
        {
            a->child = n;
        }
        else
        {
            suffix_object(p, n);
        }
        p = n;
    }

    if (a && a->child) {
        a->child->prev = n;
    }

    return a;
}

__attribute__((visibility("default"))) cJSON * cJSON_CreateStringArray(const char *const *strings, int count)
{
    size_t i = 0;
    cJSON *n = 
# 2729 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 2729 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    cJSON *p = 
# 2730 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 2730 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    cJSON *a = 
# 2731 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 2731 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;

    if ((count < 0) || (strings == 
# 2733 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                  ((void *)0)
# 2733 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                      ))
    {
        return 
# 2735 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
              ((void *)0)
# 2735 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                  ;
    }

    a = cJSON_CreateArray();

    for (i = 0; a && (i < (size_t)count); i++)
    {
        n = cJSON_CreateString(strings[i]);
        if(!n)
        {
            cJSON_Delete(a);
            return 
# 2746 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 2746 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ;
        }
        if(!i)
        {
            a->child = n;
        }
        else
        {
            suffix_object(p,n);
        }
        p = n;
    }

    if (a && a->child) {
        a->child->prev = n;
    }

    return a;
}


cJSON * cJSON_Duplicate_rec(const cJSON *item, size_t depth, cJSON_bool recurse);

__attribute__((visibility("default"))) cJSON * cJSON_Duplicate(const cJSON *item, cJSON_bool recurse)
{
    return cJSON_Duplicate_rec(item, 0, recurse );
}

cJSON * cJSON_Duplicate_rec(const cJSON *item, size_t depth, cJSON_bool recurse)
{
    cJSON *newitem = 
# 2776 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                    ((void *)0)
# 2776 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                        ;
    cJSON *child = 
# 2777 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 2777 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      ;
    cJSON *next = 
# 2778 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                 ((void *)0)
# 2778 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                     ;
    cJSON *newchild = 
# 2779 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                     ((void *)0)
# 2779 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                         ;


    if (!item)
    {
        goto fail;
    }

    newitem = cJSON_New_Item(&global_hooks);
    if (!newitem)
    {
        goto fail;
    }

    newitem->type = item->type & (~256);
    newitem->valueint = item->valueint;
    newitem->valuedouble = item->valuedouble;
    if (item->valuestring)
    {
        newitem->valuestring = (char*)cJSON_strdup((unsigned char*)item->valuestring, &global_hooks);
        if (!newitem->valuestring)
        {
            goto fail;
        }
    }
    if (item->string)
    {
        newitem->string = (item->type&512) ? item->string : (char*)cJSON_strdup((unsigned char*)item->string, &global_hooks);
        if (!newitem->string)
        {
            goto fail;
        }
    }

    if (!recurse)
    {
        return newitem;
    }

    child = item->child;
    while (child != 
# 2819 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                   ((void *)0)
# 2819 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                       )
    {
        if(depth >= 10000) {
            goto fail;
        }
        newchild = cJSON_Duplicate_rec(child, depth + 1, ((cJSON_bool)1));
        if (!newchild)
        {
            goto fail;
        }
        if (next != 
# 2829 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                   ((void *)0)
# 2829 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                       )
        {

            next->next = newchild;
            newchild->prev = next;
            next = newchild;
        }
        else
        {

            newitem->child = newchild;
            next = newchild;
        }
        child = child->next;
    }
    if (newitem && newitem->child)
    {
        newitem->child->prev = newchild;
    }

    return newitem;

fail:
    if (newitem != 
# 2852 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                  ((void *)0)
# 2852 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                      )
    {
        cJSON_Delete(newitem);
    }

    return 
# 2857 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
          ((void *)0)
# 2857 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
              ;
}

static void skip_oneline_comment(char **input)
{
    *input += (sizeof("//") - sizeof(""));

    for (; (*input)[0] != '\0'; ++(*input))
    {
        if ((*input)[0] == '\n') {
            *input += (sizeof("\n") - sizeof(""));
            return;
        }
    }
}

static void skip_multiline_comment(char **input)
{
    *input += (sizeof("/*") - sizeof(""));

    for (; (*input)[0] != '\0'; ++(*input))
    {
        if (((*input)[0] == '*') && ((*input)[1] == '/'))
        {
            *input += (sizeof("*/") - sizeof(""));
            return;
        }
    }
}

static void minify_string(char **input, char **output) {
    (*output)[0] = (*input)[0];
    *input += (sizeof("\"") - sizeof(""));
    *output += (sizeof("\"") - sizeof(""));


    for (; (*input)[0] != '\0'; (void)++(*input), ++(*output)) {
        (*output)[0] = (*input)[0];

        if ((*input)[0] == '\"') {
            (*output)[0] = '\"';
            *input += (sizeof("\"") - sizeof(""));
            *output += (sizeof("\"") - sizeof(""));
            return;
        } else if (((*input)[0] == '\\') && ((*input)[1] == '\"')) {
            (*output)[1] = (*input)[1];
            *input += (sizeof("\"") - sizeof(""));
            *output += (sizeof("\"") - sizeof(""));
        }
    }
}

__attribute__((visibility("default"))) void cJSON_Minify(char *json)
{
    char *into = json;

    if (json == 
# 2913 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 2913 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return;
    }

    while (json[0] != '\0')
    {
        switch (json[0])
        {
            case ' ':
            case '\t':
            case '\r':
            case '\n':
                json++;
                break;

            case '/':
                if (json[1] == '/')
                {
                    skip_oneline_comment(&json);
                }
                else if (json[1] == '*')
                {
                    skip_multiline_comment(&json);
                } else {
                    json++;
                }
                break;

            case '\"':
                minify_string(&json, (char**)&into);
                break;

            default:
                into[0] = json[0];
                json++;
                into++;
        }
    }


    *into = '\0';
}

__attribute__((visibility("default"))) cJSON_bool cJSON_IsInvalid(const cJSON * const item)
{
    if (item == 
# 2959 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 2959 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return ((cJSON_bool)0);
    }

    return (item->type & 0xFF) == (0);
}

__attribute__((visibility("default"))) cJSON_bool cJSON_IsFalse(const cJSON * const item)
{
    if (item == 
# 2969 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 2969 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return ((cJSON_bool)0);
    }

    return (item->type & 0xFF) == (1 << 0);
}

__attribute__((visibility("default"))) cJSON_bool cJSON_IsTrue(const cJSON * const item)
{
    if (item == 
# 2979 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 2979 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return ((cJSON_bool)0);
    }

    return (item->type & 0xff) == (1 << 1);
}


__attribute__((visibility("default"))) cJSON_bool cJSON_IsBool(const cJSON * const item)
{
    if (item == 
# 2990 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 2990 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return ((cJSON_bool)0);
    }

    return (item->type & ((1 << 1) | (1 << 0))) != 0;
}
__attribute__((visibility("default"))) cJSON_bool cJSON_IsNull(const cJSON * const item)
{
    if (item == 
# 2999 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 2999 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return ((cJSON_bool)0);
    }

    return (item->type & 0xFF) == (1 << 2);
}

__attribute__((visibility("default"))) cJSON_bool cJSON_IsNumber(const cJSON * const item)
{
    if (item == 
# 3009 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 3009 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return ((cJSON_bool)0);
    }

    return (item->type & 0xFF) == (1 << 3);
}

__attribute__((visibility("default"))) cJSON_bool cJSON_IsString(const cJSON * const item)
{
    if (item == 
# 3019 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 3019 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return ((cJSON_bool)0);
    }

    return (item->type & 0xFF) == (1 << 4);
}

__attribute__((visibility("default"))) cJSON_bool cJSON_IsArray(const cJSON * const item)
{
    if (item == 
# 3029 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 3029 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return ((cJSON_bool)0);
    }

    return (item->type & 0xFF) == (1 << 5);
}

__attribute__((visibility("default"))) cJSON_bool cJSON_IsObject(const cJSON * const item)
{
    if (item == 
# 3039 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 3039 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return ((cJSON_bool)0);
    }

    return (item->type & 0xFF) == (1 << 6);
}

__attribute__((visibility("default"))) cJSON_bool cJSON_IsRaw(const cJSON * const item)
{
    if (item == 
# 3049 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
               ((void *)0)
# 3049 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                   )
    {
        return ((cJSON_bool)0);
    }

    return (item->type & 0xFF) == (1 << 7);
}

__attribute__((visibility("default"))) cJSON_bool cJSON_Compare(const cJSON * const a, const cJSON * const b, const cJSON_bool case_sensitive)
{
    if ((a == 
# 3059 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
             ((void *)0)
# 3059 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                 ) || (b == 
# 3059 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                            ((void *)0)
# 3059 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                ) || ((a->type & 0xFF) != (b->type & 0xFF)))
    {
        return ((cJSON_bool)0);
    }


    switch (a->type & 0xFF)
    {
        case (1 << 0):
        case (1 << 1):
        case (1 << 2):
        case (1 << 3):
        case (1 << 4):
        case (1 << 7):
        case (1 << 5):
        case (1 << 6):
            break;

        default:
            return ((cJSON_bool)0);
    }


    if (a == b)
    {
        return ((cJSON_bool)1);
    }

    switch (a->type & 0xFF)
    {

        case (1 << 0):
        case (1 << 1):
        case (1 << 2):
            return ((cJSON_bool)1);

        case (1 << 3):
            if (compare_double(a->valuedouble, b->valuedouble))
            {
                return ((cJSON_bool)1);
            }
            return ((cJSON_bool)0);

        case (1 << 4):
        case (1 << 7):
            if ((a->valuestring == 
# 3104 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                  ((void *)0)
# 3104 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                      ) || (b->valuestring == 
# 3104 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                                              ((void *)0)
# 3104 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                                  ))
            {
                return ((cJSON_bool)0);
            }
            if (strcmp(a->valuestring, b->valuestring) == 0)
            {
                return ((cJSON_bool)1);
            }

            return ((cJSON_bool)0);

        case (1 << 5):
        {
            cJSON *a_element = a->child;
            cJSON *b_element = b->child;

            for (; (a_element != 
# 3120 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                ((void *)0)
# 3120 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                    ) && (b_element != 
# 3120 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                                       ((void *)0)
# 3120 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                                           );)
            {
                if (!cJSON_Compare(a_element, b_element, case_sensitive))
                {
                    return ((cJSON_bool)0);
                }

                a_element = a_element->next;
                b_element = b_element->next;
            }


            if (a_element != b_element) {
                return ((cJSON_bool)0);
            }

            return ((cJSON_bool)1);
        }

        case (1 << 6):
        {
            cJSON *a_element = 
# 3141 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              ((void *)0)
# 3141 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                  ;
            cJSON *b_element = 
# 3142 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                              ((void *)0)
# 3142 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                  ;
            for(a_element = (a != 
# 3143 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
           ((void *)0)
# 3143 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
           ) ? (a)->child : 
# 3143 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
           ((void *)0)
# 3143 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
           ; a_element != 
# 3143 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
           ((void *)0)
# 3143 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
           ; a_element = a_element->next)
            {

                b_element = get_object_item(b, a_element->string, case_sensitive);
                if (b_element == 
# 3147 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                ((void *)0)
# 3147 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                    )
                {
                    return ((cJSON_bool)0);
                }

                if (!cJSON_Compare(a_element, b_element, case_sensitive))
                {
                    return ((cJSON_bool)0);
                }
            }



            for(b_element = (b != 
# 3160 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
           ((void *)0)
# 3160 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
           ) ? (b)->child : 
# 3160 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
           ((void *)0)
# 3160 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
           ; b_element != 
# 3160 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
           ((void *)0)
# 3160 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
           ; b_element = b_element->next)
            {
                a_element = get_object_item(a, b_element->string, case_sensitive);
                if (a_element == 
# 3163 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
                                ((void *)0)
# 3163 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                                    )
                {
                    return ((cJSON_bool)0);
                }

                if (!cJSON_Compare(b_element, a_element, case_sensitive))
                {
                    return ((cJSON_bool)0);
                }
            }

            return ((cJSON_bool)1);
        }

        default:
            return ((cJSON_bool)0);
    }
}

__attribute__((visibility("default"))) void * cJSON_malloc(size_t size)
{
    return global_hooks.allocate(size);
}

__attribute__((visibility("default"))) void cJSON_free(void *object)
{
    global_hooks.deallocate(object);
    object = 
# 3190 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c" 3 4
            ((void *)0)
# 3190 "corpus/cjson/upstream/cJSON-1.7.19/cJSON.c"
                ;
}
