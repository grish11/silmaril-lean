# 0 "src/options.c"
# 0 "<built-in>"
# 0 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 0 "<command-line>" 2
# 1 "src/options.c"






# 1 "include/mimalloc.h" 1






       
# 98 "include/mimalloc.h"
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 1 3 4
# 145 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 3 4

# 145 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 3 4
typedef long int ptrdiff_t;
# 214 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 3 4
typedef long unsigned int size_t;
# 329 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 3 4
typedef int wchar_t;
# 425 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 3 4
typedef struct {
  long long __max_align_ll __attribute__((__aligned__(__alignof__(long long))));
  long double __max_align_ld __attribute__((__aligned__(__alignof__(long double))));
# 436 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 3 4
} max_align_t;
# 99 "include/mimalloc.h" 2
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stdbool.h" 1 3 4
# 100 "include/mimalloc.h" 2
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stdint.h" 1 3 4
# 9 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stdint.h" 3 4
# 1 "/usr/include/stdint.h" 1 3 4
# 26 "/usr/include/stdint.h" 3 4
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
# 27 "/usr/include/stdint.h" 2 3 4
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
# 28 "/usr/include/stdint.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wchar.h" 1 3 4
# 29 "/usr/include/stdint.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wordsize.h" 1 3 4
# 30 "/usr/include/stdint.h" 2 3 4




# 1 "/usr/include/x86_64-linux-gnu/bits/stdint-intn.h" 1 3 4
# 24 "/usr/include/x86_64-linux-gnu/bits/stdint-intn.h" 3 4
typedef __int8_t int8_t;
typedef __int16_t int16_t;
typedef __int32_t int32_t;
typedef __int64_t int64_t;
# 35 "/usr/include/stdint.h" 2 3 4


# 1 "/usr/include/x86_64-linux-gnu/bits/stdint-uintn.h" 1 3 4
# 24 "/usr/include/x86_64-linux-gnu/bits/stdint-uintn.h" 3 4
typedef __uint8_t uint8_t;
typedef __uint16_t uint16_t;
typedef __uint32_t uint32_t;
typedef __uint64_t uint64_t;
# 38 "/usr/include/stdint.h" 2 3 4



# 1 "/usr/include/x86_64-linux-gnu/bits/stdint-least.h" 1 3 4
# 25 "/usr/include/x86_64-linux-gnu/bits/stdint-least.h" 3 4
typedef __int_least8_t int_least8_t;
typedef __int_least16_t int_least16_t;
typedef __int_least32_t int_least32_t;
typedef __int_least64_t int_least64_t;


typedef __uint_least8_t uint_least8_t;
typedef __uint_least16_t uint_least16_t;
typedef __uint_least32_t uint_least32_t;
typedef __uint_least64_t uint_least64_t;
# 42 "/usr/include/stdint.h" 2 3 4





typedef signed char int_fast8_t;

typedef long int int_fast16_t;
typedef long int int_fast32_t;
typedef long int int_fast64_t;
# 60 "/usr/include/stdint.h" 3 4
typedef unsigned char uint_fast8_t;

typedef unsigned long int uint_fast16_t;
typedef unsigned long int uint_fast32_t;
typedef unsigned long int uint_fast64_t;
# 76 "/usr/include/stdint.h" 3 4
typedef long int intptr_t;


typedef unsigned long int uintptr_t;
# 90 "/usr/include/stdint.h" 3 4
typedef __intmax_t intmax_t;
typedef __uintmax_t uintmax_t;
# 10 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stdint.h" 2 3 4
# 101 "include/mimalloc.h" 2
# 110 "include/mimalloc.h"

# 110 "include/mimalloc.h"
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_malloc(size_t size) __attribute__((malloc)) __attribute__((alloc_size(1)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_calloc(size_t count, size_t size) __attribute__((malloc)) __attribute__((alloc_size(1,2)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_realloc(void* p, size_t newsize) __attribute__((alloc_size(2)));
__attribute__((visibility("default"))) void* mi_expand(void* p, size_t newsize) __attribute__((alloc_size(2)));

__attribute__((visibility("default"))) void mi_free(void* p) ;
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) char* mi_strdup(const char* s) __attribute__((malloc));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) char* mi_strndup(const char* s, size_t n) __attribute__((malloc));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) char* mi_realpath(const char* fname, char* resolved_name) __attribute__((malloc));







__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_malloc_small(size_t size) __attribute__((malloc)) __attribute__((alloc_size(1)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_zalloc_small(size_t size) __attribute__((malloc)) __attribute__((alloc_size(1)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_zalloc(size_t size) __attribute__((malloc)) __attribute__((alloc_size(1)));

__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_mallocn(size_t count, size_t size) __attribute__((malloc)) __attribute__((alloc_size(1,2)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_reallocn(void* p, size_t count, size_t size) __attribute__((alloc_size(2,3)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_reallocf(void* p, size_t newsize) __attribute__((alloc_size(2)));

__attribute__((warn_unused_result)) __attribute__((visibility("default"))) size_t mi_usable_size(const void* p) ;
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) size_t mi_good_size(size_t size) ;






typedef void ( mi_deferred_free_fun)(
# 142 "include/mimalloc.h" 3 4
                                            _Bool 
# 142 "include/mimalloc.h"
                                                 force, unsigned long long heartbeat, void* arg);
__attribute__((visibility("default"))) void mi_register_deferred_free(mi_deferred_free_fun* deferred_free, void* arg) ;

typedef void ( mi_output_fun)(const char* msg, void* arg);
__attribute__((visibility("default"))) void mi_register_output(mi_output_fun* out, void* arg) ;

typedef void ( mi_error_fun)(int err, void* arg);
__attribute__((visibility("default"))) void mi_register_error(mi_error_fun* fun, void* arg);

__attribute__((visibility("default"))) void mi_collect(
# 151 "include/mimalloc.h" 3 4
                              _Bool 
# 151 "include/mimalloc.h"
                                   force) ;
__attribute__((visibility("default"))) void mi_collect_reduce(size_t target_thread_owned) ;
__attribute__((visibility("default"))) int mi_version(void) ;
__attribute__((visibility("default"))) void mi_stats_reset(void) ;
__attribute__((visibility("default"))) void mi_stats_merge(void) ;
__attribute__((visibility("default"))) void mi_stats_print(void* out) ;
__attribute__((visibility("default"))) void mi_stats_print_out(mi_output_fun* out, void* arg) ;

__attribute__((visibility("default"))) void mi_process_init(void) ;
__attribute__((visibility("default"))) void mi_thread_init(void) ;
__attribute__((visibility("default"))) void mi_thread_done(void) ;
__attribute__((visibility("default"))) void mi_thread_stats_print_out(mi_output_fun* out, void* arg) ;

__attribute__((visibility("default"))) void mi_process_info(size_t* elapsed_msecs, size_t* user_msecs, size_t* system_msecs,
                                    size_t* current_rss, size_t* peak_rss,
                                    size_t* current_commit, size_t* peak_commit, size_t* page_faults) ;







__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_malloc_aligned(size_t size, size_t alignment) __attribute__((malloc)) __attribute__((alloc_size(1))) __attribute__((alloc_align(2)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_malloc_aligned_at(size_t size, size_t alignment, size_t offset) __attribute__((malloc)) __attribute__((alloc_size(1)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_zalloc_aligned(size_t size, size_t alignment) __attribute__((malloc)) __attribute__((alloc_size(1))) __attribute__((alloc_align(2)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_zalloc_aligned_at(size_t size, size_t alignment, size_t offset) __attribute__((malloc)) __attribute__((alloc_size(1)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_calloc_aligned(size_t count, size_t size, size_t alignment) __attribute__((malloc)) __attribute__((alloc_size(1,2))) __attribute__((alloc_align(3)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_calloc_aligned_at(size_t count, size_t size, size_t alignment, size_t offset) __attribute__((malloc)) __attribute__((alloc_size(1,2)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_realloc_aligned(void* p, size_t newsize, size_t alignment) __attribute__((alloc_size(2))) __attribute__((alloc_align(3)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_realloc_aligned_at(void* p, size_t newsize, size_t alignment, size_t offset) __attribute__((alloc_size(2)));






struct mi_heap_s;
typedef struct mi_heap_s mi_heap_t;

__attribute__((warn_unused_result)) __attribute__((visibility("default"))) mi_heap_t* mi_heap_new(void);
__attribute__((visibility("default"))) void mi_heap_delete(mi_heap_t* heap);
__attribute__((visibility("default"))) void mi_heap_destroy(mi_heap_t* heap);
__attribute__((visibility("default"))) mi_heap_t* mi_heap_set_default(mi_heap_t* heap);
__attribute__((visibility("default"))) mi_heap_t* mi_heap_get_default(void);
__attribute__((visibility("default"))) mi_heap_t* mi_heap_get_backing(void);
__attribute__((visibility("default"))) void mi_heap_collect(mi_heap_t* heap, 
# 197 "include/mimalloc.h" 3 4
                                                          _Bool 
# 197 "include/mimalloc.h"
                                                               force) ;

__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_malloc(mi_heap_t* heap, size_t size) __attribute__((malloc)) __attribute__((alloc_size(2)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_zalloc(mi_heap_t* heap, size_t size) __attribute__((malloc)) __attribute__((alloc_size(2)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_calloc(mi_heap_t* heap, size_t count, size_t size) __attribute__((malloc)) __attribute__((alloc_size(2,3)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_mallocn(mi_heap_t* heap, size_t count, size_t size) __attribute__((malloc)) __attribute__((alloc_size(2,3)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_malloc_small(mi_heap_t* heap, size_t size) __attribute__((malloc)) __attribute__((alloc_size(2)));

__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_realloc(mi_heap_t* heap, void* p, size_t newsize) __attribute__((alloc_size(3)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_reallocn(mi_heap_t* heap, void* p, size_t count, size_t size) __attribute__((alloc_size(3,4)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_reallocf(mi_heap_t* heap, void* p, size_t newsize) __attribute__((alloc_size(3)));

__attribute__((warn_unused_result)) __attribute__((visibility("default"))) char* mi_heap_strdup(mi_heap_t* heap, const char* s) __attribute__((malloc));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) char* mi_heap_strndup(mi_heap_t* heap, const char* s, size_t n) __attribute__((malloc));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) char* mi_heap_realpath(mi_heap_t* heap, const char* fname, char* resolved_name) __attribute__((malloc));

__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_malloc_aligned(mi_heap_t* heap, size_t size, size_t alignment) __attribute__((malloc)) __attribute__((alloc_size(2))) __attribute__((alloc_align(3)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_malloc_aligned_at(mi_heap_t* heap, size_t size, size_t alignment, size_t offset) __attribute__((malloc)) __attribute__((alloc_size(2)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_zalloc_aligned(mi_heap_t* heap, size_t size, size_t alignment) __attribute__((malloc)) __attribute__((alloc_size(2))) __attribute__((alloc_align(3)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_zalloc_aligned_at(mi_heap_t* heap, size_t size, size_t alignment, size_t offset) __attribute__((malloc)) __attribute__((alloc_size(2)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_calloc_aligned(mi_heap_t* heap, size_t count, size_t size, size_t alignment) __attribute__((malloc)) __attribute__((alloc_size(2,3))) __attribute__((alloc_align(4)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_calloc_aligned_at(mi_heap_t* heap, size_t count, size_t size, size_t alignment, size_t offset) __attribute__((malloc)) __attribute__((alloc_size(2,3)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_realloc_aligned(mi_heap_t* heap, void* p, size_t newsize, size_t alignment) __attribute__((alloc_size(3))) __attribute__((alloc_align(4)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_realloc_aligned_at(mi_heap_t* heap, void* p, size_t newsize, size_t alignment, size_t offset) __attribute__((alloc_size(3)));
# 230 "include/mimalloc.h"
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_rezalloc(void* p, size_t newsize) __attribute__((alloc_size(2)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_recalloc(void* p, size_t newcount, size_t size) __attribute__((alloc_size(2,3)));

__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_rezalloc_aligned(void* p, size_t newsize, size_t alignment) __attribute__((alloc_size(2))) __attribute__((alloc_align(3)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_rezalloc_aligned_at(void* p, size_t newsize, size_t alignment, size_t offset) __attribute__((alloc_size(2)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_recalloc_aligned(void* p, size_t newcount, size_t size, size_t alignment) __attribute__((alloc_size(2,3))) __attribute__((alloc_align(4)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_recalloc_aligned_at(void* p, size_t newcount, size_t size, size_t alignment, size_t offset) __attribute__((alloc_size(2,3)));

__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_rezalloc(mi_heap_t* heap, void* p, size_t newsize) __attribute__((alloc_size(3)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_recalloc(mi_heap_t* heap, void* p, size_t newcount, size_t size) __attribute__((alloc_size(3,4)));

__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_rezalloc_aligned(mi_heap_t* heap, void* p, size_t newsize, size_t alignment) __attribute__((alloc_size(3))) __attribute__((alloc_align(4)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_rezalloc_aligned_at(mi_heap_t* heap, void* p, size_t newsize, size_t alignment, size_t offset) __attribute__((alloc_size(3)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_recalloc_aligned(mi_heap_t* heap, void* p, size_t newcount, size_t size, size_t alignment) __attribute__((alloc_size(3,4))) __attribute__((alloc_align(5)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_recalloc_aligned_at(mi_heap_t* heap, void* p, size_t newcount, size_t size, size_t alignment, size_t offset) __attribute__((alloc_size(3,4)));






__attribute__((visibility("default"))) 
# 251 "include/mimalloc.h" 3 4
              _Bool 
# 251 "include/mimalloc.h"
                   mi_heap_contains_block(mi_heap_t* heap, const void* p);
__attribute__((visibility("default"))) 
# 252 "include/mimalloc.h" 3 4
              _Bool 
# 252 "include/mimalloc.h"
                   mi_heap_check_owned(mi_heap_t* heap, const void* p);
__attribute__((visibility("default"))) 
# 253 "include/mimalloc.h" 3 4
              _Bool 
# 253 "include/mimalloc.h"
                   mi_check_owned(const void* p);


typedef struct mi_heap_area_s {
  void* blocks;
  size_t reserved;
  size_t committed;
  size_t used;
  size_t block_size;
  size_t full_block_size;
  int heap_tag;
} mi_heap_area_t;

typedef 
# 266 "include/mimalloc.h" 3 4
       _Bool 
# 266 "include/mimalloc.h"
            ( mi_block_visit_fun)(const mi_heap_t* heap, const mi_heap_area_t* area, void* block, size_t block_size, void* arg);

__attribute__((visibility("default"))) 
# 268 "include/mimalloc.h" 3 4
              _Bool 
# 268 "include/mimalloc.h"
                   mi_heap_visit_blocks(const mi_heap_t* heap, 
# 268 "include/mimalloc.h" 3 4
                                                               _Bool 
# 268 "include/mimalloc.h"
                                                                    visit_blocks, mi_block_visit_fun* visitor, void* arg);


__attribute__((warn_unused_result)) __attribute__((visibility("default"))) 
# 271 "include/mimalloc.h" 3 4
                                _Bool 
# 271 "include/mimalloc.h"
                                     mi_is_in_heap_region(const void* p) ;
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) 
# 272 "include/mimalloc.h" 3 4
                                _Bool 
# 272 "include/mimalloc.h"
                                     mi_is_redirected(void) ;

__attribute__((visibility("default"))) int mi_reserve_huge_os_pages_interleave(size_t pages, size_t numa_nodes, size_t timeout_msecs) ;
__attribute__((visibility("default"))) int mi_reserve_huge_os_pages_at(size_t pages, int numa_node, size_t timeout_msecs) ;

__attribute__((visibility("default"))) int mi_reserve_os_memory(size_t size, 
# 277 "include/mimalloc.h" 3 4
                                                     _Bool 
# 277 "include/mimalloc.h"
                                                          commit, 
# 277 "include/mimalloc.h" 3 4
                                                                  _Bool 
# 277 "include/mimalloc.h"
                                                                       allow_large) ;
__attribute__((visibility("default"))) 
# 278 "include/mimalloc.h" 3 4
              _Bool 
# 278 "include/mimalloc.h"
                   mi_manage_os_memory(void* start, size_t size, 
# 278 "include/mimalloc.h" 3 4
                                                                 _Bool 
# 278 "include/mimalloc.h"
                                                                      is_committed, 
# 278 "include/mimalloc.h" 3 4
                                                                                    _Bool 
# 278 "include/mimalloc.h"
                                                                                         is_large, 
# 278 "include/mimalloc.h" 3 4
                                                                                                   _Bool 
# 278 "include/mimalloc.h"
                                                                                                        is_zero, int numa_node) ;

__attribute__((visibility("default"))) void mi_debug_show_arenas(
# 280 "include/mimalloc.h" 3 4
                                        _Bool 
# 280 "include/mimalloc.h"
                                             show_inuse) ;


typedef int mi_arena_id_t;
__attribute__((visibility("default"))) void* mi_arena_area(mi_arena_id_t arena_id, size_t* size);
__attribute__((visibility("default"))) int mi_reserve_huge_os_pages_at_ex(size_t pages, int numa_node, size_t timeout_msecs, 
# 285 "include/mimalloc.h" 3 4
                                                                                                      _Bool 
# 285 "include/mimalloc.h"
                                                                                                           exclusive, mi_arena_id_t* arena_id) ;
__attribute__((visibility("default"))) int mi_reserve_os_memory_ex(size_t size, 
# 286 "include/mimalloc.h" 3 4
                                                         _Bool 
# 286 "include/mimalloc.h"
                                                              commit, 
# 286 "include/mimalloc.h" 3 4
                                                                      _Bool 
# 286 "include/mimalloc.h"
                                                                           allow_large, 
# 286 "include/mimalloc.h" 3 4
                                                                                        _Bool 
# 286 "include/mimalloc.h"
                                                                                             exclusive, mi_arena_id_t* arena_id) ;
__attribute__((visibility("default"))) 
# 287 "include/mimalloc.h" 3 4
              _Bool 
# 287 "include/mimalloc.h"
                    mi_manage_os_memory_ex(void* start, size_t size, 
# 287 "include/mimalloc.h" 3 4
                                                                     _Bool 
# 287 "include/mimalloc.h"
                                                                          is_committed, 
# 287 "include/mimalloc.h" 3 4
                                                                                        _Bool 
# 287 "include/mimalloc.h"
                                                                                             is_large, 
# 287 "include/mimalloc.h" 3 4
                                                                                                       _Bool 
# 287 "include/mimalloc.h"
                                                                                                            is_zero, int numa_node, 
# 287 "include/mimalloc.h" 3 4
                                                                                                                                    _Bool 
# 287 "include/mimalloc.h"
                                                                                                                                         exclusive, mi_arena_id_t* arena_id) ;



__attribute__((warn_unused_result)) __attribute__((visibility("default"))) mi_heap_t* mi_heap_new_in_arena(mi_arena_id_t arena_id);





typedef void* mi_subproc_id_t;
__attribute__((visibility("default"))) mi_subproc_id_t mi_subproc_main(void);
__attribute__((visibility("default"))) mi_subproc_id_t mi_subproc_new(void);
__attribute__((visibility("default"))) void mi_subproc_delete(mi_subproc_id_t subproc);
__attribute__((visibility("default"))) void mi_subproc_add_current_thread(mi_subproc_id_t subproc);


__attribute__((visibility("default"))) 
# 304 "include/mimalloc.h" 3 4
              _Bool 
# 304 "include/mimalloc.h"
                   mi_abandoned_visit_blocks(mi_subproc_id_t subproc_id, int heap_tag, 
# 304 "include/mimalloc.h" 3 4
                                                                                       _Bool 
# 304 "include/mimalloc.h"
                                                                                            visit_blocks, mi_block_visit_fun* visitor, void* arg);




__attribute__((warn_unused_result)) __attribute__((visibility("default"))) mi_heap_t* mi_heap_new_ex(int heap_tag, 
# 309 "include/mimalloc.h" 3 4
                                                                        _Bool 
# 309 "include/mimalloc.h"
                                                                             allow_destroy, mi_arena_id_t arena_id);


__attribute__((visibility("default"))) int mi_reserve_huge_os_pages(size_t pages, double max_secs, size_t* pages_reserved) ;




__attribute__((visibility("default"))) void mi_heap_guarded_set_sample_rate(mi_heap_t* heap, size_t sample_rate, size_t seed);
__attribute__((visibility("default"))) void mi_heap_guarded_set_size_bound(mi_heap_t* heap, size_t min, size_t max);
# 344 "include/mimalloc.h"
typedef enum mi_option_e {

  mi_option_show_errors,
  mi_option_show_stats,
  mi_option_verbose,

  mi_option_eager_commit,
  mi_option_arena_eager_commit,
  mi_option_purge_decommits,
  mi_option_allow_large_os_pages,
  mi_option_reserve_huge_os_pages,
  mi_option_reserve_huge_os_pages_at,
  mi_option_reserve_os_memory,
  mi_option_deprecated_segment_cache,
  mi_option_deprecated_page_reset,
  mi_option_abandoned_page_purge,
  mi_option_deprecated_segment_reset,
  mi_option_eager_commit_delay,
  mi_option_purge_delay,
  mi_option_use_numa_nodes,
  mi_option_disallow_os_alloc,
  mi_option_os_tag,
  mi_option_max_errors,
  mi_option_max_warnings,
  mi_option_max_segment_reclaim,
  mi_option_destroy_on_exit,
  mi_option_arena_reserve,
  mi_option_arena_purge_mult,
  mi_option_purge_extend_delay,
  mi_option_abandoned_reclaim_on_free,
  mi_option_disallow_arena_alloc,
  mi_option_retry_on_oom,
  mi_option_visit_abandoned,
  mi_option_guarded_min,
  mi_option_guarded_max,
  mi_option_guarded_precise,
  mi_option_guarded_sample_rate,
  mi_option_guarded_sample_seed,
  mi_option_target_segments_per_thread,
  _mi_option_last,

  mi_option_large_os_pages = mi_option_allow_large_os_pages,
  mi_option_eager_region_commit = mi_option_arena_eager_commit,
  mi_option_reset_decommits = mi_option_purge_decommits,
  mi_option_reset_delay = mi_option_purge_delay,
  mi_option_abandoned_page_reset = mi_option_abandoned_page_purge,
  mi_option_limit_os_alloc = mi_option_disallow_os_alloc
} mi_option_t;


__attribute__((warn_unused_result)) __attribute__((visibility("default"))) 
# 394 "include/mimalloc.h" 3 4
                                _Bool 
# 394 "include/mimalloc.h"
                                     mi_option_is_enabled(mi_option_t option);
__attribute__((visibility("default"))) void mi_option_enable(mi_option_t option);
__attribute__((visibility("default"))) void mi_option_disable(mi_option_t option);
__attribute__((visibility("default"))) void mi_option_set_enabled(mi_option_t option, 
# 397 "include/mimalloc.h" 3 4
                                                             _Bool 
# 397 "include/mimalloc.h"
                                                                  enable);
__attribute__((visibility("default"))) void mi_option_set_enabled_default(mi_option_t option, 
# 398 "include/mimalloc.h" 3 4
                                                                     _Bool 
# 398 "include/mimalloc.h"
                                                                          enable);

__attribute__((warn_unused_result)) __attribute__((visibility("default"))) long mi_option_get(mi_option_t option);
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) long mi_option_get_clamp(mi_option_t option, long min, long max);
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) size_t mi_option_get_size(mi_option_t option);
__attribute__((visibility("default"))) void mi_option_set(mi_option_t option, long value);
__attribute__((visibility("default"))) void mi_option_set_default(mi_option_t option, long value);
# 413 "include/mimalloc.h"
__attribute__((visibility("default"))) void mi_cfree(void* p) ;
__attribute__((visibility("default"))) void* mi__expand(void* p, size_t newsize) ;
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) size_t mi_malloc_size(const void* p) ;
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) size_t mi_malloc_good_size(size_t size) ;
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) size_t mi_malloc_usable_size(const void *p) ;

__attribute__((visibility("default"))) int mi_posix_memalign(void** p, size_t alignment, size_t size) ;
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_memalign(size_t alignment, size_t size) __attribute__((malloc)) __attribute__((alloc_size(2))) __attribute__((alloc_align(1)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_valloc(size_t size) __attribute__((malloc)) __attribute__((alloc_size(1)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_pvalloc(size_t size) __attribute__((malloc)) __attribute__((alloc_size(1)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_aligned_alloc(size_t alignment, size_t size) __attribute__((malloc)) __attribute__((alloc_size(2))) __attribute__((alloc_align(1)));

__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_reallocarray(void* p, size_t count, size_t size) __attribute__((alloc_size(2,3)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) int mi_reallocarr(void* p, size_t count, size_t size) ;
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_aligned_recalloc(void* p, size_t newcount, size_t size, size_t alignment) ;
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_aligned_offset_recalloc(void* p, size_t newcount, size_t size, size_t alignment, size_t offset) ;

__attribute__((warn_unused_result)) __attribute__((visibility("default"))) unsigned short* mi_wcsdup(const unsigned short* s) __attribute__((malloc));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) unsigned char* mi_mbsdup(const unsigned char* s) __attribute__((malloc));
__attribute__((visibility("default"))) int mi_dupenv_s(char** buf, size_t* size, const char* name) ;
__attribute__((visibility("default"))) int mi_wdupenv_s(unsigned short** buf, size_t* size, const unsigned short* name) ;

__attribute__((visibility("default"))) void mi_free_size(void* p, size_t size) ;
__attribute__((visibility("default"))) void mi_free_size_aligned(void* p, size_t size, size_t alignment) ;
__attribute__((visibility("default"))) void mi_free_aligned(void* p, size_t alignment) ;



__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_new(size_t size) __attribute__((malloc)) __attribute__((alloc_size(1)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_new_aligned(size_t size, size_t alignment) __attribute__((malloc)) __attribute__((alloc_size(1))) __attribute__((alloc_align(2)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_new_nothrow(size_t size) __attribute__((malloc)) __attribute__((alloc_size(1)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_new_aligned_nothrow(size_t size, size_t alignment) __attribute__((malloc)) __attribute__((alloc_size(1))) __attribute__((alloc_align(2)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_new_n(size_t count, size_t size) __attribute__((malloc)) __attribute__((alloc_size(1,2)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_new_realloc(void* p, size_t newsize) __attribute__((alloc_size(2)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_new_reallocn(void* p, size_t newcount, size_t size) __attribute__((alloc_size(2,3)));

__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_alloc_new(mi_heap_t* heap, size_t size) __attribute__((malloc)) __attribute__((alloc_size(2)));
__attribute__((warn_unused_result)) __attribute__((visibility("default"))) void* mi_heap_alloc_new_n(mi_heap_t* heap, size_t count, size_t size) __attribute__((malloc)) __attribute__((alloc_size(2,3)));
# 8 "src/options.c" 2
# 1 "include/mimalloc/internal.h" 1






       
# 17 "include/mimalloc/internal.h"
# 1 "include/mimalloc/types.h" 1






       
# 25 "include/mimalloc/types.h"
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 1 3 4
# 26 "include/mimalloc/types.h" 2

# 1 "include/mimalloc/atomic.h" 1






       
# 19 "include/mimalloc/atomic.h"
# 1 "/usr/include/pthread.h" 1 3 4
# 22 "/usr/include/pthread.h" 3 4
# 1 "/usr/include/sched.h" 1 3 4
# 29 "/usr/include/sched.h" 3 4
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 1 3 4
# 30 "/usr/include/sched.h" 2 3 4

# 1 "/usr/include/x86_64-linux-gnu/bits/types/time_t.h" 1 3 4
# 10 "/usr/include/x86_64-linux-gnu/bits/types/time_t.h" 3 4

# 10 "/usr/include/x86_64-linux-gnu/bits/types/time_t.h" 3 4
typedef __time_t time_t;
# 32 "/usr/include/sched.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/types/struct_timespec.h" 1 3 4





# 1 "/usr/include/x86_64-linux-gnu/bits/endian.h" 1 3 4
# 35 "/usr/include/x86_64-linux-gnu/bits/endian.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/endianness.h" 1 3 4
# 36 "/usr/include/x86_64-linux-gnu/bits/endian.h" 2 3 4
# 7 "/usr/include/x86_64-linux-gnu/bits/types/struct_timespec.h" 2 3 4




struct timespec
{



  __time_t tv_sec;




  __syscall_slong_t tv_nsec;
# 31 "/usr/include/x86_64-linux-gnu/bits/types/struct_timespec.h" 3 4
};
# 33 "/usr/include/sched.h" 2 3 4





typedef __pid_t pid_t;




# 1 "/usr/include/x86_64-linux-gnu/bits/sched.h" 1 3 4
# 126 "/usr/include/x86_64-linux-gnu/bits/sched.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/types/struct_sched_param.h" 1 3 4
# 23 "/usr/include/x86_64-linux-gnu/bits/types/struct_sched_param.h" 3 4
struct sched_param
{
  int sched_priority;
};
# 127 "/usr/include/x86_64-linux-gnu/bits/sched.h" 2 3 4


# 159 "/usr/include/x86_64-linux-gnu/bits/sched.h" 3 4

# 44 "/usr/include/sched.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/cpu-set.h" 1 3 4
# 32 "/usr/include/x86_64-linux-gnu/bits/cpu-set.h" 3 4
typedef unsigned long int __cpu_mask;






typedef struct
{
  __cpu_mask __bits[1024 / (8 * sizeof (__cpu_mask))];
} cpu_set_t;
# 115 "/usr/include/x86_64-linux-gnu/bits/cpu-set.h" 3 4


extern int __sched_cpucount (size_t __setsize, const cpu_set_t *__setp)
     __attribute__ ((__nothrow__ , __leaf__));
extern cpu_set_t *__sched_cpualloc (size_t __count) __attribute__ ((__nothrow__ , __leaf__)) ;
extern void __sched_cpufree (cpu_set_t *__set) __attribute__ ((__nothrow__ , __leaf__));


# 45 "/usr/include/sched.h" 2 3 4









extern int sched_setparam (__pid_t __pid, const struct sched_param *__param)
     __attribute__ ((__nothrow__ , __leaf__));


extern int sched_getparam (__pid_t __pid, struct sched_param *__param) __attribute__ ((__nothrow__ , __leaf__));


extern int sched_setscheduler (__pid_t __pid, int __policy,
          const struct sched_param *__param) __attribute__ ((__nothrow__ , __leaf__));


extern int sched_getscheduler (__pid_t __pid) __attribute__ ((__nothrow__ , __leaf__));


extern int sched_yield (void) __attribute__ ((__nothrow__ , __leaf__));


extern int sched_get_priority_max (int __algorithm) __attribute__ ((__nothrow__ , __leaf__));


extern int sched_get_priority_min (int __algorithm) __attribute__ ((__nothrow__ , __leaf__));



extern int sched_rr_get_interval (__pid_t __pid, struct timespec *__t) __attribute__ ((__nothrow__ , __leaf__));
# 138 "/usr/include/sched.h" 3 4

# 23 "/usr/include/pthread.h" 2 3 4
# 1 "/usr/include/time.h" 1 3 4
# 29 "/usr/include/time.h" 3 4
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 1 3 4
# 30 "/usr/include/time.h" 2 3 4



# 1 "/usr/include/x86_64-linux-gnu/bits/time.h" 1 3 4
# 34 "/usr/include/time.h" 2 3 4



# 1 "/usr/include/x86_64-linux-gnu/bits/types/clock_t.h" 1 3 4






typedef __clock_t clock_t;
# 38 "/usr/include/time.h" 2 3 4

# 1 "/usr/include/x86_64-linux-gnu/bits/types/struct_tm.h" 1 3 4






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
# 40 "/usr/include/time.h" 2 3 4






# 1 "/usr/include/x86_64-linux-gnu/bits/types/clockid_t.h" 1 3 4






typedef __clockid_t clockid_t;
# 47 "/usr/include/time.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/types/timer_t.h" 1 3 4






typedef __timer_t timer_t;
# 48 "/usr/include/time.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/types/struct_itimerspec.h" 1 3 4







struct itimerspec
  {
    struct timespec it_interval;
    struct timespec it_value;
  };
# 49 "/usr/include/time.h" 2 3 4
struct sigevent;
# 60 "/usr/include/time.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/types/locale_t.h" 1 3 4
# 22 "/usr/include/x86_64-linux-gnu/bits/types/locale_t.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/types/__locale_t.h" 1 3 4
# 27 "/usr/include/x86_64-linux-gnu/bits/types/__locale_t.h" 3 4
struct __locale_struct
{

  struct __locale_data *__locales[13];


  const unsigned short int *__ctype_b;
  const int *__ctype_tolower;
  const int *__ctype_toupper;


  const char *__names[13];
};

typedef struct __locale_struct *__locale_t;
# 23 "/usr/include/x86_64-linux-gnu/bits/types/locale_t.h" 2 3 4

typedef __locale_t locale_t;
# 61 "/usr/include/time.h" 2 3 4











extern clock_t clock (void) __attribute__ ((__nothrow__ , __leaf__));



extern time_t time (time_t *__timer) __attribute__ ((__nothrow__ , __leaf__));


extern double difftime (time_t __time1, time_t __time0);


extern time_t mktime (struct tm *__tp) __attribute__ ((__nothrow__ , __leaf__));
# 99 "/usr/include/time.h" 3 4
extern size_t strftime (char *__restrict __s, size_t __maxsize,
   const char *__restrict __format,
   const struct tm *__restrict __tp)
   __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 3, 4)));
# 116 "/usr/include/time.h" 3 4
extern size_t strftime_l (char *__restrict __s, size_t __maxsize,
     const char *__restrict __format,
     const struct tm *__restrict __tp,
     locale_t __loc) __attribute__ ((__nothrow__ , __leaf__));
# 132 "/usr/include/time.h" 3 4
extern struct tm *gmtime (const time_t *__timer) __attribute__ ((__nothrow__ , __leaf__));



extern struct tm *localtime (const time_t *__timer) __attribute__ ((__nothrow__ , __leaf__));
# 154 "/usr/include/time.h" 3 4
extern struct tm *gmtime_r (const time_t *__restrict __timer,
       struct tm *__restrict __tp) __attribute__ ((__nothrow__ , __leaf__));



extern struct tm *localtime_r (const time_t *__restrict __timer,
          struct tm *__restrict __tp) __attribute__ ((__nothrow__ , __leaf__));
# 179 "/usr/include/time.h" 3 4
extern char *asctime (const struct tm *__tp) __attribute__ ((__nothrow__ , __leaf__));



extern char *ctime (const time_t *__timer) __attribute__ ((__nothrow__ , __leaf__));
# 197 "/usr/include/time.h" 3 4
extern char *asctime_r (const struct tm *__restrict __tp,
   char *__restrict __buf) __attribute__ ((__nothrow__ , __leaf__));



extern char *ctime_r (const time_t *__restrict __timer,
        char *__restrict __buf) __attribute__ ((__nothrow__ , __leaf__));
# 217 "/usr/include/time.h" 3 4
extern char *__tzname[2];
extern int __daylight;
extern long int __timezone;




extern char *tzname[2];



extern void tzset (void) __attribute__ ((__nothrow__ , __leaf__));



extern int daylight;
extern long int timezone;
# 246 "/usr/include/time.h" 3 4
extern time_t timegm (struct tm *__tp) __attribute__ ((__nothrow__ , __leaf__));
# 263 "/usr/include/time.h" 3 4
extern time_t timelocal (struct tm *__tp) __attribute__ ((__nothrow__ , __leaf__));







extern int dysize (int __year) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
# 281 "/usr/include/time.h" 3 4
extern int nanosleep (const struct timespec *__requested_time,
        struct timespec *__remaining);


extern int clock_getres (clockid_t __clock_id, struct timespec *__res) __attribute__ ((__nothrow__ , __leaf__));


extern int clock_gettime (clockid_t __clock_id, struct timespec *__tp)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));


extern int clock_settime (clockid_t __clock_id, const struct timespec *__tp)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
# 323 "/usr/include/time.h" 3 4
extern int clock_nanosleep (clockid_t __clock_id, int __flags,
       const struct timespec *__req,
       struct timespec *__rem);
# 338 "/usr/include/time.h" 3 4
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
# 376 "/usr/include/time.h" 3 4
extern int timer_getoverrun (timer_t __timerid) __attribute__ ((__nothrow__ , __leaf__));






extern int timespec_get (struct timespec *__ts, int __base)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 452 "/usr/include/time.h" 3 4

# 24 "/usr/include/pthread.h" 2 3 4


# 1 "/usr/include/x86_64-linux-gnu/bits/pthreadtypes.h" 1 3 4
# 23 "/usr/include/x86_64-linux-gnu/bits/pthreadtypes.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/thread-shared-types.h" 1 3 4
# 44 "/usr/include/x86_64-linux-gnu/bits/thread-shared-types.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/pthreadtypes-arch.h" 1 3 4
# 21 "/usr/include/x86_64-linux-gnu/bits/pthreadtypes-arch.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wordsize.h" 1 3 4
# 22 "/usr/include/x86_64-linux-gnu/bits/pthreadtypes-arch.h" 2 3 4
# 45 "/usr/include/x86_64-linux-gnu/bits/thread-shared-types.h" 2 3 4

# 1 "/usr/include/x86_64-linux-gnu/bits/atomic_wide_counter.h" 1 3 4
# 25 "/usr/include/x86_64-linux-gnu/bits/atomic_wide_counter.h" 3 4
typedef union
{
  __extension__ unsigned long long int __value64;
  struct
  {
    unsigned int __low;
    unsigned int __high;
  } __value32;
} __atomic_wide_counter;
# 47 "/usr/include/x86_64-linux-gnu/bits/thread-shared-types.h" 2 3 4




typedef struct __pthread_internal_list
{
  struct __pthread_internal_list *__prev;
  struct __pthread_internal_list *__next;
} __pthread_list_t;

typedef struct __pthread_internal_slist
{
  struct __pthread_internal_slist *__next;
} __pthread_slist_t;
# 76 "/usr/include/x86_64-linux-gnu/bits/thread-shared-types.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/struct_mutex.h" 1 3 4
# 22 "/usr/include/x86_64-linux-gnu/bits/struct_mutex.h" 3 4
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
# 53 "/usr/include/x86_64-linux-gnu/bits/struct_mutex.h" 3 4
};
# 77 "/usr/include/x86_64-linux-gnu/bits/thread-shared-types.h" 2 3 4
# 89 "/usr/include/x86_64-linux-gnu/bits/thread-shared-types.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/struct_rwlock.h" 1 3 4
# 23 "/usr/include/x86_64-linux-gnu/bits/struct_rwlock.h" 3 4
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
# 55 "/usr/include/x86_64-linux-gnu/bits/struct_rwlock.h" 3 4
};
# 90 "/usr/include/x86_64-linux-gnu/bits/thread-shared-types.h" 2 3 4




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
# 24 "/usr/include/x86_64-linux-gnu/bits/pthreadtypes.h" 2 3 4



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
# 27 "/usr/include/pthread.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/setjmp.h" 1 3 4
# 26 "/usr/include/x86_64-linux-gnu/bits/setjmp.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wordsize.h" 1 3 4
# 27 "/usr/include/x86_64-linux-gnu/bits/setjmp.h" 2 3 4




typedef long int __jmp_buf[8];
# 28 "/usr/include/pthread.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wordsize.h" 1 3 4
# 29 "/usr/include/pthread.h" 2 3 4

# 1 "/usr/include/x86_64-linux-gnu/bits/types/__sigset_t.h" 1 3 4




typedef struct
{
  unsigned long int __val[(1024 / (8 * sizeof (unsigned long int)))];
} __sigset_t;
# 31 "/usr/include/pthread.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/types/struct___jmp_buf_tag.h" 1 3 4
# 26 "/usr/include/x86_64-linux-gnu/bits/types/struct___jmp_buf_tag.h" 3 4
struct __jmp_buf_tag
  {




    __jmp_buf __jmpbuf;
    int __mask_was_saved;
    __sigset_t __saved_mask;
  };
# 32 "/usr/include/pthread.h" 2 3 4

# 1 "/usr/include/x86_64-linux-gnu/bits/pthread_stack_min-dynamic.h" 1 3 4
# 29 "/usr/include/x86_64-linux-gnu/bits/pthread_stack_min-dynamic.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/pthread_stack_min.h" 1 3 4
# 30 "/usr/include/x86_64-linux-gnu/bits/pthread_stack_min-dynamic.h" 2 3 4
# 34 "/usr/include/pthread.h" 2 3 4



enum
{
  PTHREAD_CREATE_JOINABLE,

  PTHREAD_CREATE_DETACHED

};



enum
{
  PTHREAD_MUTEX_TIMED_NP,
  PTHREAD_MUTEX_RECURSIVE_NP,
  PTHREAD_MUTEX_ERRORCHECK_NP,
  PTHREAD_MUTEX_ADAPTIVE_NP

  ,
  PTHREAD_MUTEX_NORMAL = PTHREAD_MUTEX_TIMED_NP,
  PTHREAD_MUTEX_RECURSIVE = PTHREAD_MUTEX_RECURSIVE_NP,
  PTHREAD_MUTEX_ERRORCHECK = PTHREAD_MUTEX_ERRORCHECK_NP,
  PTHREAD_MUTEX_DEFAULT = PTHREAD_MUTEX_NORMAL





};




enum
{
  PTHREAD_MUTEX_STALLED,
  PTHREAD_MUTEX_STALLED_NP = PTHREAD_MUTEX_STALLED,
  PTHREAD_MUTEX_ROBUST,
  PTHREAD_MUTEX_ROBUST_NP = PTHREAD_MUTEX_ROBUST
};





enum
{
  PTHREAD_PRIO_NONE,
  PTHREAD_PRIO_INHERIT,
  PTHREAD_PRIO_PROTECT
};
# 104 "/usr/include/pthread.h" 3 4
enum
{
  PTHREAD_RWLOCK_PREFER_READER_NP,
  PTHREAD_RWLOCK_PREFER_WRITER_NP,
  PTHREAD_RWLOCK_PREFER_WRITER_NONRECURSIVE_NP,
  PTHREAD_RWLOCK_DEFAULT_NP = PTHREAD_RWLOCK_PREFER_READER_NP
};
# 124 "/usr/include/pthread.h" 3 4
enum
{
  PTHREAD_INHERIT_SCHED,

  PTHREAD_EXPLICIT_SCHED

};



enum
{
  PTHREAD_SCOPE_SYSTEM,

  PTHREAD_SCOPE_PROCESS

};



enum
{
  PTHREAD_PROCESS_PRIVATE,

  PTHREAD_PROCESS_SHARED

};
# 159 "/usr/include/pthread.h" 3 4
struct _pthread_cleanup_buffer
{
  void (*__routine) (void *);
  void *__arg;
  int __canceltype;
  struct _pthread_cleanup_buffer *__prev;
};


enum
{
  PTHREAD_CANCEL_ENABLE,

  PTHREAD_CANCEL_DISABLE

};
enum
{
  PTHREAD_CANCEL_DEFERRED,

  PTHREAD_CANCEL_ASYNCHRONOUS

};
# 197 "/usr/include/pthread.h" 3 4





extern int pthread_create (pthread_t *__restrict __newthread,
      const pthread_attr_t *__restrict __attr,
      void *(*__start_routine) (void *),
      void *__restrict __arg) __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1, 3)));





extern void pthread_exit (void *__retval) __attribute__ ((__noreturn__));







extern int pthread_join (pthread_t __th, void **__thread_return);
# 269 "/usr/include/pthread.h" 3 4
extern int pthread_detach (pthread_t __th) __attribute__ ((__nothrow__ , __leaf__));



extern pthread_t pthread_self (void) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));


extern int pthread_equal (pthread_t __thread1, pthread_t __thread2)
  __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));







extern int pthread_attr_init (pthread_attr_t *__attr) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_attr_destroy (pthread_attr_t *__attr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_attr_getdetachstate (const pthread_attr_t *__attr,
     int *__detachstate)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern int pthread_attr_setdetachstate (pthread_attr_t *__attr,
     int __detachstate)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));



extern int pthread_attr_getguardsize (const pthread_attr_t *__attr,
          size_t *__guardsize)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern int pthread_attr_setguardsize (pthread_attr_t *__attr,
          size_t __guardsize)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));



extern int pthread_attr_getschedparam (const pthread_attr_t *__restrict __attr,
           struct sched_param *__restrict __param)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern int pthread_attr_setschedparam (pthread_attr_t *__restrict __attr,
           const struct sched_param *__restrict
           __param) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern int pthread_attr_getschedpolicy (const pthread_attr_t *__restrict
     __attr, int *__restrict __policy)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern int pthread_attr_setschedpolicy (pthread_attr_t *__attr, int __policy)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_attr_getinheritsched (const pthread_attr_t *__restrict
      __attr, int *__restrict __inherit)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern int pthread_attr_setinheritsched (pthread_attr_t *__attr,
      int __inherit)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));



extern int pthread_attr_getscope (const pthread_attr_t *__restrict __attr,
      int *__restrict __scope)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern int pthread_attr_setscope (pthread_attr_t *__attr, int __scope)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_attr_getstackaddr (const pthread_attr_t *__restrict
          __attr, void **__restrict __stackaddr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2))) __attribute__ ((__deprecated__));





extern int pthread_attr_setstackaddr (pthread_attr_t *__attr,
          void *__stackaddr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) __attribute__ ((__deprecated__));


extern int pthread_attr_getstacksize (const pthread_attr_t *__restrict
          __attr, size_t *__restrict __stacksize)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));




extern int pthread_attr_setstacksize (pthread_attr_t *__attr,
          size_t __stacksize)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));



extern int pthread_attr_getstack (const pthread_attr_t *__restrict __attr,
      void **__restrict __stackaddr,
      size_t *__restrict __stacksize)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2, 3)));




extern int pthread_attr_setstack (pthread_attr_t *__attr, void *__stackaddr,
      size_t __stacksize) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 441 "/usr/include/pthread.h" 3 4
extern int pthread_setschedparam (pthread_t __target_thread, int __policy,
      const struct sched_param *__param)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (3)));


extern int pthread_getschedparam (pthread_t __target_thread,
      int *__restrict __policy,
      struct sched_param *__restrict __param)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 3)));


extern int pthread_setschedprio (pthread_t __target_thread, int __prio)
     __attribute__ ((__nothrow__ , __leaf__));
# 509 "/usr/include/pthread.h" 3 4
extern int pthread_once (pthread_once_t *__once_control,
    void (*__init_routine) (void)) __attribute__ ((__nonnull__ (1, 2)));
# 521 "/usr/include/pthread.h" 3 4
extern int pthread_setcancelstate (int __state, int *__oldstate);



extern int pthread_setcanceltype (int __type, int *__oldtype);


extern int pthread_cancel (pthread_t __th);




extern void pthread_testcancel (void);




struct __cancel_jmp_buf_tag
{
  __jmp_buf __cancel_jmp_buf;
  int __mask_was_saved;
};

typedef struct
{
  struct __cancel_jmp_buf_tag __cancel_jmp_buf[1];
  void *__pad[4];
} __pthread_unwind_buf_t __attribute__ ((__aligned__));
# 557 "/usr/include/pthread.h" 3 4
struct __pthread_cleanup_frame
{
  void (*__cancel_routine) (void *);
  void *__cancel_arg;
  int __do_it;
  int __cancel_type;
};
# 697 "/usr/include/pthread.h" 3 4
extern void __pthread_register_cancel (__pthread_unwind_buf_t *__buf)
     ;
# 709 "/usr/include/pthread.h" 3 4
extern void __pthread_unregister_cancel (__pthread_unwind_buf_t *__buf)
  ;
# 750 "/usr/include/pthread.h" 3 4
extern void __pthread_unwind_next (__pthread_unwind_buf_t *__buf)
     __attribute__ ((__noreturn__))

     __attribute__ ((__weak__))

     ;
# 766 "/usr/include/pthread.h" 3 4
extern int __sigsetjmp_cancel (struct __cancel_jmp_buf_tag __env[1], int __savemask) __asm__ ("" "__sigsetjmp") __attribute__ ((__nothrow__))


                     __attribute__ ((__returns_twice__));
# 781 "/usr/include/pthread.h" 3 4
extern int pthread_mutex_init (pthread_mutex_t *__mutex,
          const pthread_mutexattr_t *__mutexattr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_mutex_destroy (pthread_mutex_t *__mutex)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_mutex_trylock (pthread_mutex_t *__mutex)
     __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_mutex_lock (pthread_mutex_t *__mutex)
     __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1)));




extern int pthread_mutex_timedlock (pthread_mutex_t *__restrict __mutex,
        const struct timespec *__restrict
        __abstime) __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1, 2)));
# 835 "/usr/include/pthread.h" 3 4
extern int pthread_mutex_unlock (pthread_mutex_t *__mutex)
     __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1)));



extern int pthread_mutex_getprioceiling (const pthread_mutex_t *
      __restrict __mutex,
      int *__restrict __prioceiling)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));



extern int pthread_mutex_setprioceiling (pthread_mutex_t *__restrict __mutex,
      int __prioceiling,
      int *__restrict __old_ceiling)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 3)));




extern int pthread_mutex_consistent (pthread_mutex_t *__mutex)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 874 "/usr/include/pthread.h" 3 4
extern int pthread_mutexattr_init (pthread_mutexattr_t *__attr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_mutexattr_destroy (pthread_mutexattr_t *__attr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_mutexattr_getpshared (const pthread_mutexattr_t *
      __restrict __attr,
      int *__restrict __pshared)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern int pthread_mutexattr_setpshared (pthread_mutexattr_t *__attr,
      int __pshared)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));



extern int pthread_mutexattr_gettype (const pthread_mutexattr_t *__restrict
          __attr, int *__restrict __kind)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));




extern int pthread_mutexattr_settype (pthread_mutexattr_t *__attr, int __kind)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));



extern int pthread_mutexattr_getprotocol (const pthread_mutexattr_t *
       __restrict __attr,
       int *__restrict __protocol)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));



extern int pthread_mutexattr_setprotocol (pthread_mutexattr_t *__attr,
       int __protocol)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_mutexattr_getprioceiling (const pthread_mutexattr_t *
          __restrict __attr,
          int *__restrict __prioceiling)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern int pthread_mutexattr_setprioceiling (pthread_mutexattr_t *__attr,
          int __prioceiling)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));



extern int pthread_mutexattr_getrobust (const pthread_mutexattr_t *__attr,
     int *__robustness)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));
# 946 "/usr/include/pthread.h" 3 4
extern int pthread_mutexattr_setrobust (pthread_mutexattr_t *__attr,
     int __robustness)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 967 "/usr/include/pthread.h" 3 4
extern int pthread_rwlock_init (pthread_rwlock_t *__restrict __rwlock,
    const pthread_rwlockattr_t *__restrict
    __attr) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_rwlock_destroy (pthread_rwlock_t *__rwlock)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_rwlock_rdlock (pthread_rwlock_t *__rwlock)
     __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_rwlock_tryrdlock (pthread_rwlock_t *__rwlock)
  __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1)));




extern int pthread_rwlock_timedrdlock (pthread_rwlock_t *__restrict __rwlock,
           const struct timespec *__restrict
           __abstime) __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1, 2)));
# 1023 "/usr/include/pthread.h" 3 4
extern int pthread_rwlock_wrlock (pthread_rwlock_t *__rwlock)
     __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_rwlock_trywrlock (pthread_rwlock_t *__rwlock)
     __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1)));




extern int pthread_rwlock_timedwrlock (pthread_rwlock_t *__restrict __rwlock,
           const struct timespec *__restrict
           __abstime) __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1, 2)));
# 1071 "/usr/include/pthread.h" 3 4
extern int pthread_rwlock_unlock (pthread_rwlock_t *__rwlock)
     __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1)));





extern int pthread_rwlockattr_init (pthread_rwlockattr_t *__attr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_rwlockattr_destroy (pthread_rwlockattr_t *__attr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_rwlockattr_getpshared (const pthread_rwlockattr_t *
       __restrict __attr,
       int *__restrict __pshared)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern int pthread_rwlockattr_setpshared (pthread_rwlockattr_t *__attr,
       int __pshared)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_rwlockattr_getkind_np (const pthread_rwlockattr_t *
       __restrict __attr,
       int *__restrict __pref)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern int pthread_rwlockattr_setkind_np (pthread_rwlockattr_t *__attr,
       int __pref) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));







extern int pthread_cond_init (pthread_cond_t *__restrict __cond,
         const pthread_condattr_t *__restrict __cond_attr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_cond_destroy (pthread_cond_t *__cond)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_cond_signal (pthread_cond_t *__cond)
     __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_cond_broadcast (pthread_cond_t *__cond)
     __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1)));






extern int pthread_cond_wait (pthread_cond_t *__restrict __cond,
         pthread_mutex_t *__restrict __mutex)
     __attribute__ ((__nonnull__ (1, 2)));
# 1145 "/usr/include/pthread.h" 3 4
extern int pthread_cond_timedwait (pthread_cond_t *__restrict __cond,
       pthread_mutex_t *__restrict __mutex,
       const struct timespec *__restrict __abstime)
     __attribute__ ((__nonnull__ (1, 2, 3)));
# 1194 "/usr/include/pthread.h" 3 4
extern int pthread_condattr_init (pthread_condattr_t *__attr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_condattr_destroy (pthread_condattr_t *__attr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_condattr_getpshared (const pthread_condattr_t *
     __restrict __attr,
     int *__restrict __pshared)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern int pthread_condattr_setpshared (pthread_condattr_t *__attr,
     int __pshared) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));



extern int pthread_condattr_getclock (const pthread_condattr_t *
          __restrict __attr,
          __clockid_t *__restrict __clock_id)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern int pthread_condattr_setclock (pthread_condattr_t *__attr,
          __clockid_t __clock_id)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 1230 "/usr/include/pthread.h" 3 4
extern int pthread_spin_init (pthread_spinlock_t *__lock, int __pshared)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_spin_destroy (pthread_spinlock_t *__lock)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_spin_lock (pthread_spinlock_t *__lock)
     __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_spin_trylock (pthread_spinlock_t *__lock)
     __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_spin_unlock (pthread_spinlock_t *__lock)
     __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1)));






extern int pthread_barrier_init (pthread_barrier_t *__restrict __barrier,
     const pthread_barrierattr_t *__restrict
     __attr, unsigned int __count)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_barrier_destroy (pthread_barrier_t *__barrier)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_barrier_wait (pthread_barrier_t *__barrier)
     __attribute__ ((__nothrow__)) __attribute__ ((__nonnull__ (1)));



extern int pthread_barrierattr_init (pthread_barrierattr_t *__attr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_barrierattr_destroy (pthread_barrierattr_t *__attr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_barrierattr_getpshared (const pthread_barrierattr_t *
        __restrict __attr,
        int *__restrict __pshared)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern int pthread_barrierattr_setpshared (pthread_barrierattr_t *__attr,
        int __pshared)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 1297 "/usr/include/pthread.h" 3 4
extern int pthread_key_create (pthread_key_t *__key,
          void (*__destr_function) (void *))
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern int pthread_key_delete (pthread_key_t __key) __attribute__ ((__nothrow__ , __leaf__));


extern void *pthread_getspecific (pthread_key_t __key) __attribute__ ((__nothrow__ , __leaf__));


extern int pthread_setspecific (pthread_key_t __key,
    const void *__pointer)
  __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__access__ (__none__, 2)));




extern int pthread_getcpuclockid (pthread_t __thread_id,
      __clockid_t *__clock_id)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));
# 1332 "/usr/include/pthread.h" 3 4
extern int pthread_atfork (void (*__prepare) (void),
      void (*__parent) (void),
      void (*__child) (void)) __attribute__ ((__nothrow__ , __leaf__));




extern __inline __attribute__ ((__gnu_inline__)) int
__attribute__ ((__nothrow__ , __leaf__)) pthread_equal (pthread_t __thread1, pthread_t __thread2)
{
  return __thread1 == __thread2;
}



# 20 "include/mimalloc/atomic.h" 2
# 52 "include/mimalloc/atomic.h"
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stdatomic.h" 1 3 4
# 29 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stdatomic.h" 3 4
typedef enum
  {
    memory_order_relaxed = 0,
    memory_order_consume = 1,
    memory_order_acquire = 2,
    memory_order_release = 3,
    memory_order_acq_rel = 4,
    memory_order_seq_cst = 5
  } memory_order;


typedef _Atomic _Bool atomic_bool;
typedef _Atomic char atomic_char;
typedef _Atomic signed char atomic_schar;
typedef _Atomic unsigned char atomic_uchar;
typedef _Atomic short atomic_short;
typedef _Atomic unsigned short atomic_ushort;
typedef _Atomic int atomic_int;
typedef _Atomic unsigned int atomic_uint;
typedef _Atomic long atomic_long;
typedef _Atomic unsigned long atomic_ulong;
typedef _Atomic long long atomic_llong;
typedef _Atomic unsigned long long atomic_ullong;



typedef _Atomic short unsigned int atomic_char16_t;
typedef _Atomic unsigned int atomic_char32_t;
typedef _Atomic int atomic_wchar_t;
typedef _Atomic signed char atomic_int_least8_t;
typedef _Atomic unsigned char atomic_uint_least8_t;
typedef _Atomic short int atomic_int_least16_t;
typedef _Atomic short unsigned int atomic_uint_least16_t;
typedef _Atomic int atomic_int_least32_t;
typedef _Atomic unsigned int atomic_uint_least32_t;
typedef _Atomic long int atomic_int_least64_t;
typedef _Atomic long unsigned int atomic_uint_least64_t;
typedef _Atomic signed char atomic_int_fast8_t;
typedef _Atomic unsigned char atomic_uint_fast8_t;
typedef _Atomic long int atomic_int_fast16_t;
typedef _Atomic long unsigned int atomic_uint_fast16_t;
typedef _Atomic long int atomic_int_fast32_t;
typedef _Atomic long unsigned int atomic_uint_fast32_t;
typedef _Atomic long int atomic_int_fast64_t;
typedef _Atomic long unsigned int atomic_uint_fast64_t;
typedef _Atomic long int atomic_intptr_t;
typedef _Atomic long unsigned int atomic_uintptr_t;
typedef _Atomic long unsigned int atomic_size_t;
typedef _Atomic long int atomic_ptrdiff_t;
typedef _Atomic long int atomic_intmax_t;
typedef _Atomic long unsigned int atomic_uintmax_t;
# 97 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stdatomic.h" 3 4
extern void atomic_thread_fence (memory_order);

extern void atomic_signal_fence (memory_order);
# 226 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stdatomic.h" 3 4
typedef _Atomic struct
{

  _Bool __val;



} atomic_flag;




extern _Bool atomic_flag_test_and_set (volatile atomic_flag *);


extern _Bool atomic_flag_test_and_set_explicit (volatile atomic_flag *,
      memory_order);



extern void atomic_flag_clear (volatile atomic_flag *);

extern void atomic_flag_clear_explicit (volatile atomic_flag *, memory_order);
# 53 "include/mimalloc/atomic.h" 2
# 95 "include/mimalloc/atomic.h"

# 95 "include/mimalloc/atomic.h"
static inline void mi_atomic_yield(void);
static inline intptr_t mi_atomic_addi(_Atomic(intptr_t)*p, intptr_t add);
static inline intptr_t mi_atomic_subi(_Atomic(intptr_t)*p, intptr_t sub);
# 129 "include/mimalloc/atomic.h"
static inline int64_t mi_atomic_addi64_relaxed(volatile int64_t* p, int64_t add) {
  return 
# 130 "include/mimalloc/atomic.h" 3 4
        __atomic_fetch_add ((
# 130 "include/mimalloc/atomic.h"
        (_Atomic(int64_t)*)p
# 130 "include/mimalloc/atomic.h" 3 4
        ), (
# 130 "include/mimalloc/atomic.h"
        add
# 130 "include/mimalloc/atomic.h" 3 4
        ), (
# 130 "include/mimalloc/atomic.h"
        memory_order_relaxed
# 130 "include/mimalloc/atomic.h" 3 4
        ))
# 130 "include/mimalloc/atomic.h"
                                                                                          ;
}
static inline void mi_atomic_maxi64_relaxed(volatile int64_t* p, int64_t x) {
  int64_t current = 
# 133 "include/mimalloc/atomic.h" 3 4
                   __extension__ ({ __auto_type __atomic_load_ptr = (
# 133 "include/mimalloc/atomic.h"
                   (_Atomic(int64_t)*)p
# 133 "include/mimalloc/atomic.h" 3 4
                   ); __typeof__ ((void)0, *__atomic_load_ptr) __atomic_load_tmp; __atomic_load (__atomic_load_ptr, &__atomic_load_tmp, (
# 133 "include/mimalloc/atomic.h"
                   memory_order_relaxed
# 133 "include/mimalloc/atomic.h" 3 4
                   )); __atomic_load_tmp; })
# 133 "include/mimalloc/atomic.h"
                                                               ;
  while (current < x && !
# 134 "include/mimalloc/atomic.h" 3 4
                        __extension__ ({ __auto_type __atomic_compare_exchange_ptr = (
# 134 "include/mimalloc/atomic.h"
                        (_Atomic(int64_t)*)p
# 134 "include/mimalloc/atomic.h" 3 4
                        ); __typeof__ ((void)0, *__atomic_compare_exchange_ptr) __atomic_compare_exchange_tmp = (
# 134 "include/mimalloc/atomic.h"
                        x
# 134 "include/mimalloc/atomic.h" 3 4
                        ); __atomic_compare_exchange (__atomic_compare_exchange_ptr, (
# 134 "include/mimalloc/atomic.h"
                        &current
# 134 "include/mimalloc/atomic.h" 3 4
                        ), &__atomic_compare_exchange_tmp, 1, (
# 134 "include/mimalloc/atomic.h"
                        memory_order_release
# 134 "include/mimalloc/atomic.h" 3 4
                        ), (
# 134 "include/mimalloc/atomic.h"
                        memory_order_relaxed
# 134 "include/mimalloc/atomic.h" 3 4
                        )); })
# 134 "include/mimalloc/atomic.h"
                                                                                     ) { };
}
# 306 "include/mimalloc/atomic.h"
static inline intptr_t mi_atomic_addi(_Atomic(intptr_t)*p, intptr_t add) {
  return (intptr_t)
# 307 "include/mimalloc/atomic.h" 3 4
                  __atomic_fetch_add ((
# 307 "include/mimalloc/atomic.h"
                  (_Atomic(uintptr_t)*)p
# 307 "include/mimalloc/atomic.h" 3 4
                  ), (
# 307 "include/mimalloc/atomic.h"
                  (uintptr_t)add
# 307 "include/mimalloc/atomic.h" 3 4
                  ), (
# 307 "include/mimalloc/atomic.h"
                  memory_order_acq_rel
# 307 "include/mimalloc/atomic.h" 3 4
                  ))
# 307 "include/mimalloc/atomic.h"
                                                                               ;
}


static inline intptr_t mi_atomic_subi(_Atomic(intptr_t)*p, intptr_t sub) {
  return (intptr_t)mi_atomic_addi(p, -sub);
}






typedef _Atomic(uintptr_t) mi_atomic_once_t;


static inline 
# 323 "include/mimalloc/atomic.h" 3 4
             _Bool 
# 323 "include/mimalloc/atomic.h"
                  mi_atomic_once( mi_atomic_once_t* once ) {
  if (
# 324 "include/mimalloc/atomic.h" 3 4
     __extension__ ({ __auto_type __atomic_load_ptr = (
# 324 "include/mimalloc/atomic.h"
     once
# 324 "include/mimalloc/atomic.h" 3 4
     ); __typeof__ ((void)0, *__atomic_load_ptr) __atomic_load_tmp; __atomic_load (__atomic_load_ptr, &__atomic_load_tmp, (
# 324 "include/mimalloc/atomic.h"
     memory_order_relaxed
# 324 "include/mimalloc/atomic.h" 3 4
     )); __atomic_load_tmp; }) 
# 324 "include/mimalloc/atomic.h"
                                  != 0) return 
# 324 "include/mimalloc/atomic.h" 3 4
                                               0
# 324 "include/mimalloc/atomic.h"
                                                    ;
  uintptr_t expected = 0;
  return 
# 326 "include/mimalloc/atomic.h" 3 4
        __extension__ ({ __auto_type __atomic_compare_exchange_ptr = (
# 326 "include/mimalloc/atomic.h"
        once
# 326 "include/mimalloc/atomic.h" 3 4
        ); __typeof__ ((void)0, *__atomic_compare_exchange_ptr) __atomic_compare_exchange_tmp = (
# 326 "include/mimalloc/atomic.h"
        (uintptr_t)1
# 326 "include/mimalloc/atomic.h" 3 4
        ); __atomic_compare_exchange (__atomic_compare_exchange_ptr, (
# 326 "include/mimalloc/atomic.h"
        &expected
# 326 "include/mimalloc/atomic.h" 3 4
        ), &__atomic_compare_exchange_tmp, 0, (
# 326 "include/mimalloc/atomic.h"
        memory_order_acq_rel
# 326 "include/mimalloc/atomic.h" 3 4
        ), (
# 326 "include/mimalloc/atomic.h"
        memory_order_acquire
# 326 "include/mimalloc/atomic.h" 3 4
        )); })
# 326 "include/mimalloc/atomic.h"
                                                                   ;
}

typedef _Atomic(uintptr_t) mi_atomic_guard_t;
# 354 "include/mimalloc/atomic.h"
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/emmintrin.h" 1 3 4
# 31 "/usr/lib/gcc/x86_64-linux-gnu/14/include/emmintrin.h" 3 4
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/xmmintrin.h" 1 3 4
# 31 "/usr/lib/gcc/x86_64-linux-gnu/14/include/xmmintrin.h" 3 4
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/mmintrin.h" 1 3 4
# 44 "/usr/lib/gcc/x86_64-linux-gnu/14/include/mmintrin.h" 3 4

# 44 "/usr/lib/gcc/x86_64-linux-gnu/14/include/mmintrin.h" 3 4
typedef int __m64 __attribute__ ((__vector_size__ (8), __may_alias__));
typedef int __m32 __attribute__ ((__vector_size__ (4), __may_alias__));
typedef short __m16 __attribute__ ((__vector_size__ (2), __may_alias__));


typedef int __m64_u __attribute__ ((__vector_size__ (8), __may_alias__, __aligned__ (1)));
typedef int __m32_u __attribute__ ((__vector_size__ (4),
        __may_alias__, __aligned__ (1)));
typedef short __m16_u __attribute__ ((__vector_size__ (2),
          __may_alias__, __aligned__ (1)));


typedef int __v2si __attribute__ ((__vector_size__ (8)));
typedef short __v4hi __attribute__ ((__vector_size__ (8)));
typedef char __v8qi __attribute__ ((__vector_size__ (8)));
typedef long long __v1di __attribute__ ((__vector_size__ (8)));
typedef float __v2sf __attribute__ ((__vector_size__ (8)));


extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_empty (void)
{
  __builtin_ia32_emms ();
}

extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_empty (void)
{
  _mm_empty ();
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsi32_si64 (int __i)
{
  return (__m64) __builtin_ia32_vec_init_v2si (__i, 0);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_from_int (int __i)
{
  return _mm_cvtsi32_si64 (__i);
}





extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_from_int64 (long long __i)
{
  return (__m64) __i;
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsi64_m64 (long long __i)
{
  return (__m64) __i;
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsi64x_si64 (long long __i)
{
  return (__m64) __i;
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set_pi64x (long long __i)
{
  return (__m64) __i;
}



extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsi64_si32 (__m64 __i)
{
  return __builtin_ia32_vec_ext_v2si ((__v2si)__i, 0);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_to_int (__m64 __i)
{
  return _mm_cvtsi64_si32 (__i);
}





extern __inline long long __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_to_int64 (__m64 __i)
{
  return (long long)__i;
}

extern __inline long long __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtm64_si64 (__m64 __i)
{
  return (long long)__i;
}


extern __inline long long __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsi64_si64x (__m64 __i)
{
  return (long long)__i;
}





extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_packs_pi16 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_packsswb ((__v4hi)__m1, (__v4hi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_packsswb (__m64 __m1, __m64 __m2)
{
  return _mm_packs_pi16 (__m1, __m2);
}




extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_packs_pi32 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_packssdw ((__v2si)__m1, (__v2si)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_packssdw (__m64 __m1, __m64 __m2)
{
  return _mm_packs_pi32 (__m1, __m2);
}




extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_packs_pu16 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_packuswb ((__v4hi)__m1, (__v4hi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_packuswb (__m64 __m1, __m64 __m2)
{
  return _mm_packs_pu16 (__m1, __m2);
}



extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_unpackhi_pi8 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_punpckhbw ((__v8qi)__m1, (__v8qi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_punpckhbw (__m64 __m1, __m64 __m2)
{
  return _mm_unpackhi_pi8 (__m1, __m2);
}



extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_unpackhi_pi16 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_punpckhwd ((__v4hi)__m1, (__v4hi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_punpckhwd (__m64 __m1, __m64 __m2)
{
  return _mm_unpackhi_pi16 (__m1, __m2);
}



extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_unpackhi_pi32 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_punpckhdq ((__v2si)__m1, (__v2si)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_punpckhdq (__m64 __m1, __m64 __m2)
{
  return _mm_unpackhi_pi32 (__m1, __m2);
}



extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_unpacklo_pi8 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_punpcklbw ((__v8qi)__m1, (__v8qi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_punpcklbw (__m64 __m1, __m64 __m2)
{
  return _mm_unpacklo_pi8 (__m1, __m2);
}



extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_unpacklo_pi16 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_punpcklwd ((__v4hi)__m1, (__v4hi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_punpcklwd (__m64 __m1, __m64 __m2)
{
  return _mm_unpacklo_pi16 (__m1, __m2);
}



extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_unpacklo_pi32 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_punpckldq ((__v2si)__m1, (__v2si)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_punpckldq (__m64 __m1, __m64 __m2)
{
  return _mm_unpacklo_pi32 (__m1, __m2);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_add_pi8 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_paddb ((__v8qi)__m1, (__v8qi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_paddb (__m64 __m1, __m64 __m2)
{
  return _mm_add_pi8 (__m1, __m2);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_add_pi16 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_paddw ((__v4hi)__m1, (__v4hi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_paddw (__m64 __m1, __m64 __m2)
{
  return _mm_add_pi16 (__m1, __m2);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_add_pi32 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_paddd ((__v2si)__m1, (__v2si)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_paddd (__m64 __m1, __m64 __m2)
{
  return _mm_add_pi32 (__m1, __m2);
}
# 334 "/usr/lib/gcc/x86_64-linux-gnu/14/include/mmintrin.h" 3 4
extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_add_si64 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_paddq ((__v1di)__m1, (__v1di)__m2);
}







extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_adds_pi8 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_paddsb ((__v8qi)__m1, (__v8qi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_paddsb (__m64 __m1, __m64 __m2)
{
  return _mm_adds_pi8 (__m1, __m2);
}



extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_adds_pi16 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_paddsw ((__v4hi)__m1, (__v4hi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_paddsw (__m64 __m1, __m64 __m2)
{
  return _mm_adds_pi16 (__m1, __m2);
}



extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_adds_pu8 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_paddusb ((__v8qi)__m1, (__v8qi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_paddusb (__m64 __m1, __m64 __m2)
{
  return _mm_adds_pu8 (__m1, __m2);
}



extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_adds_pu16 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_paddusw ((__v4hi)__m1, (__v4hi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_paddusw (__m64 __m1, __m64 __m2)
{
  return _mm_adds_pu16 (__m1, __m2);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sub_pi8 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_psubb ((__v8qi)__m1, (__v8qi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psubb (__m64 __m1, __m64 __m2)
{
  return _mm_sub_pi8 (__m1, __m2);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sub_pi16 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_psubw ((__v4hi)__m1, (__v4hi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psubw (__m64 __m1, __m64 __m2)
{
  return _mm_sub_pi16 (__m1, __m2);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sub_pi32 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_psubd ((__v2si)__m1, (__v2si)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psubd (__m64 __m1, __m64 __m2)
{
  return _mm_sub_pi32 (__m1, __m2);
}
# 450 "/usr/lib/gcc/x86_64-linux-gnu/14/include/mmintrin.h" 3 4
extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sub_si64 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_psubq ((__v1di)__m1, (__v1di)__m2);
}







extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_subs_pi8 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_psubsb ((__v8qi)__m1, (__v8qi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psubsb (__m64 __m1, __m64 __m2)
{
  return _mm_subs_pi8 (__m1, __m2);
}



extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_subs_pi16 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_psubsw ((__v4hi)__m1, (__v4hi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psubsw (__m64 __m1, __m64 __m2)
{
  return _mm_subs_pi16 (__m1, __m2);
}



extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_subs_pu8 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_psubusb ((__v8qi)__m1, (__v8qi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psubusb (__m64 __m1, __m64 __m2)
{
  return _mm_subs_pu8 (__m1, __m2);
}



extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_subs_pu16 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_psubusw ((__v4hi)__m1, (__v4hi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psubusw (__m64 __m1, __m64 __m2)
{
  return _mm_subs_pu16 (__m1, __m2);
}




extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_madd_pi16 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_pmaddwd ((__v4hi)__m1, (__v4hi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pmaddwd (__m64 __m1, __m64 __m2)
{
  return _mm_madd_pi16 (__m1, __m2);
}



extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_mulhi_pi16 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_pmulhw ((__v4hi)__m1, (__v4hi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pmulhw (__m64 __m1, __m64 __m2)
{
  return _mm_mulhi_pi16 (__m1, __m2);
}



extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_mullo_pi16 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_pmullw ((__v4hi)__m1, (__v4hi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pmullw (__m64 __m1, __m64 __m2)
{
  return _mm_mullo_pi16 (__m1, __m2);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sll_pi16 (__m64 __m, __m64 __count)
{
  return (__m64) __builtin_ia32_psllw ((__v4hi)__m, (__v4hi)__count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psllw (__m64 __m, __m64 __count)
{
  return _mm_sll_pi16 (__m, __count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_slli_pi16 (__m64 __m, int __count)
{
  return (__m64) __builtin_ia32_psllwi ((__v4hi)__m, __count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psllwi (__m64 __m, int __count)
{
  return _mm_slli_pi16 (__m, __count);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sll_pi32 (__m64 __m, __m64 __count)
{
  return (__m64) __builtin_ia32_pslld ((__v2si)__m, (__v2si)__count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pslld (__m64 __m, __m64 __count)
{
  return _mm_sll_pi32 (__m, __count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_slli_pi32 (__m64 __m, int __count)
{
  return (__m64) __builtin_ia32_pslldi ((__v2si)__m, __count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pslldi (__m64 __m, int __count)
{
  return _mm_slli_pi32 (__m, __count);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sll_si64 (__m64 __m, __m64 __count)
{
  return (__m64) __builtin_ia32_psllq ((__v1di)__m, (__v1di)__count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psllq (__m64 __m, __m64 __count)
{
  return _mm_sll_si64 (__m, __count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_slli_si64 (__m64 __m, int __count)
{
  return (__m64) __builtin_ia32_psllqi ((__v1di)__m, __count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psllqi (__m64 __m, int __count)
{
  return _mm_slli_si64 (__m, __count);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sra_pi16 (__m64 __m, __m64 __count)
{
  return (__m64) __builtin_ia32_psraw ((__v4hi)__m, (__v4hi)__count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psraw (__m64 __m, __m64 __count)
{
  return _mm_sra_pi16 (__m, __count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_srai_pi16 (__m64 __m, int __count)
{
  return (__m64) __builtin_ia32_psrawi ((__v4hi)__m, __count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psrawi (__m64 __m, int __count)
{
  return _mm_srai_pi16 (__m, __count);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sra_pi32 (__m64 __m, __m64 __count)
{
  return (__m64) __builtin_ia32_psrad ((__v2si)__m, (__v2si)__count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psrad (__m64 __m, __m64 __count)
{
  return _mm_sra_pi32 (__m, __count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_srai_pi32 (__m64 __m, int __count)
{
  return (__m64) __builtin_ia32_psradi ((__v2si)__m, __count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psradi (__m64 __m, int __count)
{
  return _mm_srai_pi32 (__m, __count);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_srl_pi16 (__m64 __m, __m64 __count)
{
  return (__m64) __builtin_ia32_psrlw ((__v4hi)__m, (__v4hi)__count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psrlw (__m64 __m, __m64 __count)
{
  return _mm_srl_pi16 (__m, __count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_srli_pi16 (__m64 __m, int __count)
{
  return (__m64) __builtin_ia32_psrlwi ((__v4hi)__m, __count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psrlwi (__m64 __m, int __count)
{
  return _mm_srli_pi16 (__m, __count);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_srl_pi32 (__m64 __m, __m64 __count)
{
  return (__m64) __builtin_ia32_psrld ((__v2si)__m, (__v2si)__count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psrld (__m64 __m, __m64 __count)
{
  return _mm_srl_pi32 (__m, __count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_srli_pi32 (__m64 __m, int __count)
{
  return (__m64) __builtin_ia32_psrldi ((__v2si)__m, __count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psrldi (__m64 __m, int __count)
{
  return _mm_srli_pi32 (__m, __count);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_srl_si64 (__m64 __m, __m64 __count)
{
  return (__m64) __builtin_ia32_psrlq ((__v1di)__m, (__v1di)__count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psrlq (__m64 __m, __m64 __count)
{
  return _mm_srl_si64 (__m, __count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_srli_si64 (__m64 __m, int __count)
{
  return (__m64) __builtin_ia32_psrlqi ((__v1di)__m, __count);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psrlqi (__m64 __m, int __count)
{
  return _mm_srli_si64 (__m, __count);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_and_si64 (__m64 __m1, __m64 __m2)
{
  return __builtin_ia32_pand (__m1, __m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pand (__m64 __m1, __m64 __m2)
{
  return _mm_and_si64 (__m1, __m2);
}



extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_andnot_si64 (__m64 __m1, __m64 __m2)
{
  return __builtin_ia32_pandn (__m1, __m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pandn (__m64 __m1, __m64 __m2)
{
  return _mm_andnot_si64 (__m1, __m2);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_or_si64 (__m64 __m1, __m64 __m2)
{
  return __builtin_ia32_por (__m1, __m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_por (__m64 __m1, __m64 __m2)
{
  return _mm_or_si64 (__m1, __m2);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_xor_si64 (__m64 __m1, __m64 __m2)
{
  return __builtin_ia32_pxor (__m1, __m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pxor (__m64 __m1, __m64 __m2)
{
  return _mm_xor_si64 (__m1, __m2);
}



extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpeq_pi8 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_pcmpeqb ((__v8qi)__m1, (__v8qi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pcmpeqb (__m64 __m1, __m64 __m2)
{
  return _mm_cmpeq_pi8 (__m1, __m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpgt_pi8 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_pcmpgtb ((__v8qi)__m1, (__v8qi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pcmpgtb (__m64 __m1, __m64 __m2)
{
  return _mm_cmpgt_pi8 (__m1, __m2);
}



extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpeq_pi16 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_pcmpeqw ((__v4hi)__m1, (__v4hi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pcmpeqw (__m64 __m1, __m64 __m2)
{
  return _mm_cmpeq_pi16 (__m1, __m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpgt_pi16 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_pcmpgtw ((__v4hi)__m1, (__v4hi)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pcmpgtw (__m64 __m1, __m64 __m2)
{
  return _mm_cmpgt_pi16 (__m1, __m2);
}



extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpeq_pi32 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_pcmpeqd ((__v2si)__m1, (__v2si)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pcmpeqd (__m64 __m1, __m64 __m2)
{
  return _mm_cmpeq_pi32 (__m1, __m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpgt_pi32 (__m64 __m1, __m64 __m2)
{
  return (__m64) __builtin_ia32_pcmpgtd ((__v2si)__m1, (__v2si)__m2);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pcmpgtd (__m64 __m1, __m64 __m2)
{
  return _mm_cmpgt_pi32 (__m1, __m2);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_setzero_si64 (void)
{
  return (__m64)0LL;
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set_pi32 (int __i1, int __i0)
{
  return (__m64) __builtin_ia32_vec_init_v2si (__i0, __i1);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set_pi16 (short __w3, short __w2, short __w1, short __w0)
{
  return (__m64) __builtin_ia32_vec_init_v4hi (__w0, __w1, __w2, __w3);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set_pi8 (char __b7, char __b6, char __b5, char __b4,
      char __b3, char __b2, char __b1, char __b0)
{
  return (__m64) __builtin_ia32_vec_init_v8qi (__b0, __b1, __b2, __b3,
            __b4, __b5, __b6, __b7);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_setr_pi32 (int __i0, int __i1)
{
  return _mm_set_pi32 (__i1, __i0);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_setr_pi16 (short __w0, short __w1, short __w2, short __w3)
{
  return _mm_set_pi16 (__w3, __w2, __w1, __w0);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_setr_pi8 (char __b0, char __b1, char __b2, char __b3,
       char __b4, char __b5, char __b6, char __b7)
{
  return _mm_set_pi8 (__b7, __b6, __b5, __b4, __b3, __b2, __b1, __b0);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set1_pi32 (int __i)
{
  return _mm_set_pi32 (__i, __i);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set1_pi16 (short __w)
{
  return _mm_set_pi16 (__w, __w, __w, __w);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set1_pi8 (char __b)
{
  return _mm_set_pi8 (__b, __b, __b, __b, __b, __b, __b, __b);
}
# 32 "/usr/lib/gcc/x86_64-linux-gnu/14/include/xmmintrin.h" 2 3 4


# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/mm_malloc.h" 1 3 4
# 27 "/usr/lib/gcc/x86_64-linux-gnu/14/include/mm_malloc.h" 3 4
# 1 "/usr/include/stdlib.h" 1 3 4
# 26 "/usr/include/stdlib.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/libc-header-start.h" 1 3 4
# 27 "/usr/include/stdlib.h" 2 3 4





# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 1 3 4
# 33 "/usr/include/stdlib.h" 2 3 4







# 1 "/usr/include/x86_64-linux-gnu/bits/waitflags.h" 1 3 4
# 41 "/usr/include/stdlib.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/waitstatus.h" 1 3 4
# 42 "/usr/include/stdlib.h" 2 3 4
# 56 "/usr/include/stdlib.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/floatn.h" 1 3 4
# 131 "/usr/include/x86_64-linux-gnu/bits/floatn.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/floatn-common.h" 1 3 4
# 24 "/usr/include/x86_64-linux-gnu/bits/floatn-common.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/long-double.h" 1 3 4
# 25 "/usr/include/x86_64-linux-gnu/bits/floatn-common.h" 2 3 4
# 132 "/usr/include/x86_64-linux-gnu/bits/floatn.h" 2 3 4
# 57 "/usr/include/stdlib.h" 2 3 4


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
# 98 "/usr/include/stdlib.h" 3 4
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
# 177 "/usr/include/stdlib.h" 3 4
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
# 480 "/usr/include/stdlib.h" 3 4
extern __inline __attribute__ ((__gnu_inline__)) int
__attribute__ ((__nothrow__ , __leaf__)) atoi (const char *__nptr)
{
  return (int) strtol (__nptr, (char **) ((void *)0), 10);
}
extern __inline __attribute__ ((__gnu_inline__)) long int
__attribute__ ((__nothrow__ , __leaf__)) atol (const char *__nptr)
{
  return strtol (__nptr, (char **) ((void *)0), 10);
}


__extension__ extern __inline __attribute__ ((__gnu_inline__)) long long int
__attribute__ ((__nothrow__ , __leaf__)) atoll (const char *__nptr)
{
  return strtoll (__nptr, (char **) ((void *)0), 10);
}
# 505 "/usr/include/stdlib.h" 3 4
extern char *l64a (long int __n) __attribute__ ((__nothrow__ , __leaf__)) ;


extern long int a64l (const char *__s)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1))) ;




# 1 "/usr/include/x86_64-linux-gnu/sys/types.h" 1 3 4
# 27 "/usr/include/x86_64-linux-gnu/sys/types.h" 3 4






typedef __u_char u_char;
typedef __u_short u_short;
typedef __u_int u_int;
typedef __u_long u_long;
typedef __quad_t quad_t;
typedef __u_quad_t u_quad_t;
typedef __fsid_t fsid_t;


typedef __loff_t loff_t;




typedef __ino_t ino_t;
# 59 "/usr/include/x86_64-linux-gnu/sys/types.h" 3 4
typedef __dev_t dev_t;




typedef __gid_t gid_t;




typedef __mode_t mode_t;




typedef __nlink_t nlink_t;




typedef __uid_t uid_t;





typedef __off_t off_t;
# 103 "/usr/include/x86_64-linux-gnu/sys/types.h" 3 4
typedef __id_t id_t;




typedef __ssize_t ssize_t;





typedef __daddr_t daddr_t;
typedef __caddr_t caddr_t;





typedef __key_t key_t;
# 144 "/usr/include/x86_64-linux-gnu/sys/types.h" 3 4
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 1 3 4
# 145 "/usr/include/x86_64-linux-gnu/sys/types.h" 2 3 4



typedef unsigned long int ulong;
typedef unsigned short int ushort;
typedef unsigned int uint;







typedef __uint8_t u_int8_t;
typedef __uint16_t u_int16_t;
typedef __uint32_t u_int32_t;
typedef __uint64_t u_int64_t;


typedef int register_t __attribute__ ((__mode__ (__word__)));
# 176 "/usr/include/x86_64-linux-gnu/sys/types.h" 3 4
# 1 "/usr/include/endian.h" 1 3 4
# 35 "/usr/include/endian.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/byteswap.h" 1 3 4
# 33 "/usr/include/x86_64-linux-gnu/bits/byteswap.h" 3 4
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
# 69 "/usr/include/x86_64-linux-gnu/bits/byteswap.h" 3 4
__extension__ static __inline __uint64_t
__bswap_64 (__uint64_t __bsx)
{

  return __builtin_bswap64 (__bsx);



}
# 36 "/usr/include/endian.h" 2 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/uintn-identity.h" 1 3 4
# 32 "/usr/include/x86_64-linux-gnu/bits/uintn-identity.h" 3 4
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
# 37 "/usr/include/endian.h" 2 3 4
# 177 "/usr/include/x86_64-linux-gnu/sys/types.h" 2 3 4


# 1 "/usr/include/x86_64-linux-gnu/sys/select.h" 1 3 4
# 30 "/usr/include/x86_64-linux-gnu/sys/select.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/select.h" 1 3 4
# 31 "/usr/include/x86_64-linux-gnu/sys/select.h" 2 3 4


# 1 "/usr/include/x86_64-linux-gnu/bits/types/sigset_t.h" 1 3 4






typedef __sigset_t sigset_t;
# 34 "/usr/include/x86_64-linux-gnu/sys/select.h" 2 3 4



# 1 "/usr/include/x86_64-linux-gnu/bits/types/struct_timeval.h" 1 3 4







struct timeval
{




  __time_t tv_sec;
  __suseconds_t tv_usec;

};
# 38 "/usr/include/x86_64-linux-gnu/sys/select.h" 2 3 4





typedef __suseconds_t suseconds_t;





typedef long int __fd_mask;
# 59 "/usr/include/x86_64-linux-gnu/sys/select.h" 3 4
typedef struct
  {






    __fd_mask __fds_bits[1024 / (8 * (int) sizeof (__fd_mask))];


  } fd_set;






typedef __fd_mask fd_mask;
# 91 "/usr/include/x86_64-linux-gnu/sys/select.h" 3 4

# 102 "/usr/include/x86_64-linux-gnu/sys/select.h" 3 4
extern int select (int __nfds, fd_set *__restrict __readfds,
     fd_set *__restrict __writefds,
     fd_set *__restrict __exceptfds,
     struct timeval *__restrict __timeout);
# 127 "/usr/include/x86_64-linux-gnu/sys/select.h" 3 4
extern int pselect (int __nfds, fd_set *__restrict __readfds,
      fd_set *__restrict __writefds,
      fd_set *__restrict __exceptfds,
      const struct timespec *__restrict __timeout,
      const __sigset_t *__restrict __sigmask);
# 153 "/usr/include/x86_64-linux-gnu/sys/select.h" 3 4

# 180 "/usr/include/x86_64-linux-gnu/sys/types.h" 2 3 4





typedef __blksize_t blksize_t;






typedef __blkcnt_t blkcnt_t;



typedef __fsblkcnt_t fsblkcnt_t;



typedef __fsfilcnt_t fsfilcnt_t;
# 230 "/usr/include/x86_64-linux-gnu/sys/types.h" 3 4

# 515 "/usr/include/stdlib.h" 2 3 4






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



# 1 "/usr/include/alloca.h" 1 3 4
# 24 "/usr/include/alloca.h" 3 4
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 1 3 4
# 25 "/usr/include/alloca.h" 2 3 4







extern void *alloca (size_t __size) __attribute__ ((__nothrow__ , __leaf__));






# 707 "/usr/include/stdlib.h" 2 3 4





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
# 786 "/usr/include/stdlib.h" 3 4
extern int putenv (char *__string) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));





extern int setenv (const char *__name, const char *__value, int __replace)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2)));


extern int unsetenv (const char *__name) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));






extern int clearenv (void) __attribute__ ((__nothrow__ , __leaf__));
# 814 "/usr/include/stdlib.h" 3 4
extern char *mktemp (char *__template) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 827 "/usr/include/stdlib.h" 3 4
extern int mkstemp (char *__template) __attribute__ ((__nonnull__ (1))) ;
# 849 "/usr/include/stdlib.h" 3 4
extern int mkstemps (char *__template, int __suffixlen) __attribute__ ((__nonnull__ (1))) ;
# 870 "/usr/include/stdlib.h" 3 4
extern char *mkdtemp (char *__template) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1))) ;
# 923 "/usr/include/stdlib.h" 3 4
extern int system (const char *__command) ;
# 940 "/usr/include/stdlib.h" 3 4
extern char *realpath (const char *__restrict __name,
         char *__restrict __resolved) __attribute__ ((__nothrow__ , __leaf__)) ;






typedef int (*__compar_fn_t) (const void *, const void *);
# 960 "/usr/include/stdlib.h" 3 4
extern void *bsearch (const void *__key, const void *__base,
        size_t __nmemb, size_t __size, __compar_fn_t __compar)
     __attribute__ ((__nonnull__ (1, 2, 5))) ;


# 1 "/usr/include/x86_64-linux-gnu/bits/stdlib-bsearch.h" 1 3 4
# 19 "/usr/include/x86_64-linux-gnu/bits/stdlib-bsearch.h" 3 4
extern __inline __attribute__ ((__gnu_inline__)) void *
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


__extension__ extern long long int llabs (long long int __x)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;






extern div_t div (int __numer, int __denom)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;
extern ldiv_t ldiv (long int __numer, long int __denom)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;


__extension__ extern lldiv_t lldiv (long long int __numer,
        long long int __denom)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__)) ;
# 1012 "/usr/include/stdlib.h" 3 4
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
# 1099 "/usr/include/stdlib.h" 3 4
extern int getsubopt (char **__restrict __optionp,
        char *const *__restrict __tokens,
        char **__restrict __valuep)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2, 3))) ;
# 1145 "/usr/include/stdlib.h" 3 4
extern int getloadavg (double __loadavg[], int __nelem)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 1155 "/usr/include/stdlib.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/stdlib-float.h" 1 3 4
# 24 "/usr/include/x86_64-linux-gnu/bits/stdlib-float.h" 3 4
extern __inline __attribute__ ((__gnu_inline__)) double
__attribute__ ((__nothrow__ , __leaf__)) atof (const char *__nptr)
{
  return strtod (__nptr, (char **) ((void *)0));
}
# 1156 "/usr/include/stdlib.h" 2 3 4
# 1167 "/usr/include/stdlib.h" 3 4

# 28 "/usr/lib/gcc/x86_64-linux-gnu/14/include/mm_malloc.h" 2 3 4




extern int posix_memalign (void **, size_t, size_t);




static __inline void *
_mm_malloc (size_t __size, size_t __alignment)
{
  void *__ptr;
  if (__alignment == 1)
    return malloc (__size);
  if (__alignment == 2 || (sizeof (void *) == 8 && __alignment == 4))
    __alignment = sizeof (void *);
  if (posix_memalign (&__ptr, __alignment, __size) == 0)
    return __ptr;
  else
    return ((void *)0);
}

static __inline void
_mm_free (void *__ptr)
{
  free (__ptr);
}
# 35 "/usr/lib/gcc/x86_64-linux-gnu/14/include/xmmintrin.h" 2 3 4


enum _mm_hint
{
  _MM_HINT_IT0 = 19,
  _MM_HINT_IT1 = 18,

  _MM_HINT_ET0 = 7,
  _MM_HINT_ET1 = 6,
  _MM_HINT_T0 = 3,
  _MM_HINT_T1 = 2,
  _MM_HINT_T2 = 1,
  _MM_HINT_NTA = 0
};




extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_prefetch (const void *__P, enum _mm_hint __I)
{
  __builtin_ia32_prefetch (__P, (__I & 0x4) >> 2,
      __I & 0x3, (__I & 0x10) >> 4);
}
# 72 "/usr/lib/gcc/x86_64-linux-gnu/14/include/xmmintrin.h" 3 4
typedef float __m128 __attribute__ ((__vector_size__ (16), __may_alias__));


typedef float __m128_u __attribute__ ((__vector_size__ (16), __may_alias__, __aligned__ (1)));


typedef float __v4sf __attribute__ ((__vector_size__ (16)));
# 112 "/usr/lib/gcc/x86_64-linux-gnu/14/include/xmmintrin.h" 3 4
extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_undefined_ps (void)
{
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Winit-self"
  __m128 __Y = __Y;
#pragma GCC diagnostic pop
  return __Y;
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_setzero_ps (void)
{
  return __extension__ (__m128){ 0.0f, 0.0f, 0.0f, 0.0f };
}





extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_add_ss (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_addss ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sub_ss (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_subss ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_mul_ss (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_mulss ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_div_ss (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_divss ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sqrt_ss (__m128 __A)
{
  return (__m128) __builtin_ia32_sqrtss ((__v4sf)__A);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_rcp_ss (__m128 __A)
{
  return (__m128) __builtin_ia32_rcpss ((__v4sf)__A);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_rsqrt_ss (__m128 __A)
{
  return (__m128) __builtin_ia32_rsqrtss ((__v4sf)__A);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_min_ss (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_minss ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_max_ss (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_maxss ((__v4sf)__A, (__v4sf)__B);
}



extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_add_ps (__m128 __A, __m128 __B)
{
  return (__m128) ((__v4sf)__A + (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sub_ps (__m128 __A, __m128 __B)
{
  return (__m128) ((__v4sf)__A - (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_mul_ps (__m128 __A, __m128 __B)
{
  return (__m128) ((__v4sf)__A * (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_div_ps (__m128 __A, __m128 __B)
{
  return (__m128) ((__v4sf)__A / (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sqrt_ps (__m128 __A)
{
  return (__m128) __builtin_ia32_sqrtps ((__v4sf)__A);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_rcp_ps (__m128 __A)
{
  return (__m128) __builtin_ia32_rcpps ((__v4sf)__A);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_rsqrt_ps (__m128 __A)
{
  return (__m128) __builtin_ia32_rsqrtps ((__v4sf)__A);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_min_ps (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_minps ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_max_ps (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_maxps ((__v4sf)__A, (__v4sf)__B);
}



extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_and_ps (__m128 __A, __m128 __B)
{
  return __builtin_ia32_andps (__A, __B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_andnot_ps (__m128 __A, __m128 __B)
{
  return __builtin_ia32_andnps (__A, __B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_or_ps (__m128 __A, __m128 __B)
{
  return __builtin_ia32_orps (__A, __B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_xor_ps (__m128 __A, __m128 __B)
{
  return __builtin_ia32_xorps (__A, __B);
}





extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpeq_ss (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_cmpeqss ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmplt_ss (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_cmpltss ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmple_ss (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_cmpless ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpgt_ss (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_movss ((__v4sf) __A,
     (__v4sf)
     __builtin_ia32_cmpltss ((__v4sf) __B,
        (__v4sf)
        __A));
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpge_ss (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_movss ((__v4sf) __A,
     (__v4sf)
     __builtin_ia32_cmpless ((__v4sf) __B,
        (__v4sf)
        __A));
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpneq_ss (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_cmpneqss ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpnlt_ss (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_cmpnltss ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpnle_ss (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_cmpnless ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpngt_ss (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_movss ((__v4sf) __A,
     (__v4sf)
     __builtin_ia32_cmpnltss ((__v4sf) __B,
         (__v4sf)
         __A));
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpnge_ss (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_movss ((__v4sf) __A,
     (__v4sf)
     __builtin_ia32_cmpnless ((__v4sf) __B,
         (__v4sf)
         __A));
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpord_ss (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_cmpordss ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpunord_ss (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_cmpunordss ((__v4sf)__A, (__v4sf)__B);
}





extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpeq_ps (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_cmpeqps ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmplt_ps (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_cmpltps ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmple_ps (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_cmpleps ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpgt_ps (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_cmpgtps ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpge_ps (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_cmpgeps ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpneq_ps (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_cmpneqps ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpnlt_ps (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_cmpnltps ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpnle_ps (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_cmpnleps ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpngt_ps (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_cmpngtps ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpnge_ps (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_cmpngeps ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpord_ps (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_cmpordps ((__v4sf)__A, (__v4sf)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpunord_ps (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_cmpunordps ((__v4sf)__A, (__v4sf)__B);
}




extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_comieq_ss (__m128 __A, __m128 __B)
{
  return __builtin_ia32_comieq ((__v4sf)__A, (__v4sf)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_comilt_ss (__m128 __A, __m128 __B)
{
  return __builtin_ia32_comilt ((__v4sf)__A, (__v4sf)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_comile_ss (__m128 __A, __m128 __B)
{
  return __builtin_ia32_comile ((__v4sf)__A, (__v4sf)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_comigt_ss (__m128 __A, __m128 __B)
{
  return __builtin_ia32_comigt ((__v4sf)__A, (__v4sf)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_comige_ss (__m128 __A, __m128 __B)
{
  return __builtin_ia32_comige ((__v4sf)__A, (__v4sf)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_comineq_ss (__m128 __A, __m128 __B)
{
  return __builtin_ia32_comineq ((__v4sf)__A, (__v4sf)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_ucomieq_ss (__m128 __A, __m128 __B)
{
  return __builtin_ia32_ucomieq ((__v4sf)__A, (__v4sf)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_ucomilt_ss (__m128 __A, __m128 __B)
{
  return __builtin_ia32_ucomilt ((__v4sf)__A, (__v4sf)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_ucomile_ss (__m128 __A, __m128 __B)
{
  return __builtin_ia32_ucomile ((__v4sf)__A, (__v4sf)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_ucomigt_ss (__m128 __A, __m128 __B)
{
  return __builtin_ia32_ucomigt ((__v4sf)__A, (__v4sf)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_ucomige_ss (__m128 __A, __m128 __B)
{
  return __builtin_ia32_ucomige ((__v4sf)__A, (__v4sf)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_ucomineq_ss (__m128 __A, __m128 __B)
{
  return __builtin_ia32_ucomineq ((__v4sf)__A, (__v4sf)__B);
}



extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtss_si32 (__m128 __A)
{
  return __builtin_ia32_cvtss2si ((__v4sf) __A);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvt_ss2si (__m128 __A)
{
  return _mm_cvtss_si32 (__A);
}






extern __inline long long __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtss_si64 (__m128 __A)
{
  return __builtin_ia32_cvtss2si64 ((__v4sf) __A);
}


extern __inline long long __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtss_si64x (__m128 __A)
{
  return __builtin_ia32_cvtss2si64 ((__v4sf) __A);
}




extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtps_pi32 (__m128 __A)
{
  return (__m64) __builtin_ia32_cvtps2pi ((__v4sf) __A);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvt_ps2pi (__m128 __A)
{
  return _mm_cvtps_pi32 (__A);
}


extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvttss_si32 (__m128 __A)
{
  return __builtin_ia32_cvttss2si ((__v4sf) __A);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtt_ss2si (__m128 __A)
{
  return _mm_cvttss_si32 (__A);
}





extern __inline long long __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvttss_si64 (__m128 __A)
{
  return __builtin_ia32_cvttss2si64 ((__v4sf) __A);
}


extern __inline long long __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvttss_si64x (__m128 __A)
{
  return __builtin_ia32_cvttss2si64 ((__v4sf) __A);
}




extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvttps_pi32 (__m128 __A)
{
  return (__m64) __builtin_ia32_cvttps2pi ((__v4sf) __A);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtt_ps2pi (__m128 __A)
{
  return _mm_cvttps_pi32 (__A);
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsi32_ss (__m128 __A, int __B)
{
  return (__m128) __builtin_ia32_cvtsi2ss ((__v4sf) __A, __B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvt_si2ss (__m128 __A, int __B)
{
  return _mm_cvtsi32_ss (__A, __B);
}





extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsi64_ss (__m128 __A, long long __B)
{
  return (__m128) __builtin_ia32_cvtsi642ss ((__v4sf) __A, __B);
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsi64x_ss (__m128 __A, long long __B)
{
  return (__m128) __builtin_ia32_cvtsi642ss ((__v4sf) __A, __B);
}




extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtpi32_ps (__m128 __A, __m64 __B)
{
  return (__m128) __builtin_ia32_cvtpi2ps ((__v4sf) __A, (__v2si)__B);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvt_pi2ps (__m128 __A, __m64 __B)
{
  return _mm_cvtpi32_ps (__A, __B);
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtpi16_ps (__m64 __A)
{
  __v4hi __sign;
  __v2si __hisi, __losi;
  __v4sf __zero, __ra, __rb;




  __sign = __builtin_ia32_pcmpgtw ((__v4hi)0LL, (__v4hi)__A);


  __losi = (__v2si) __builtin_ia32_punpcklwd ((__v4hi)__A, __sign);
  __hisi = (__v2si) __builtin_ia32_punpckhwd ((__v4hi)__A, __sign);


  __zero = (__v4sf) _mm_setzero_ps ();
  __ra = __builtin_ia32_cvtpi2ps (__zero, __losi);
  __rb = __builtin_ia32_cvtpi2ps (__ra, __hisi);

  return (__m128) __builtin_ia32_movlhps (__ra, __rb);
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtpu16_ps (__m64 __A)
{
  __v2si __hisi, __losi;
  __v4sf __zero, __ra, __rb;


  __losi = (__v2si) __builtin_ia32_punpcklwd ((__v4hi)__A, (__v4hi)0LL);
  __hisi = (__v2si) __builtin_ia32_punpckhwd ((__v4hi)__A, (__v4hi)0LL);


  __zero = (__v4sf) _mm_setzero_ps ();
  __ra = __builtin_ia32_cvtpi2ps (__zero, __losi);
  __rb = __builtin_ia32_cvtpi2ps (__ra, __hisi);

  return (__m128) __builtin_ia32_movlhps (__ra, __rb);
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtpi8_ps (__m64 __A)
{
  __v8qi __sign;




  __sign = __builtin_ia32_pcmpgtb ((__v8qi)0LL, (__v8qi)__A);


  __A = (__m64) __builtin_ia32_punpcklbw ((__v8qi)__A, __sign);

  return _mm_cvtpi16_ps(__A);
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtpu8_ps(__m64 __A)
{
  __A = (__m64) __builtin_ia32_punpcklbw ((__v8qi)__A, (__v8qi)0LL);
  return _mm_cvtpu16_ps(__A);
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtpi32x2_ps(__m64 __A, __m64 __B)
{
  __v4sf __zero = (__v4sf) _mm_setzero_ps ();
  __v4sf __sfa = __builtin_ia32_cvtpi2ps (__zero, (__v2si)__A);
  __v4sf __sfb = __builtin_ia32_cvtpi2ps (__sfa, (__v2si)__B);
  return (__m128) __builtin_ia32_movlhps (__sfa, __sfb);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtps_pi16(__m128 __A)
{
  __v4sf __hisf = (__v4sf)__A;
  __v4sf __losf = __builtin_ia32_movhlps (__hisf, __hisf);
  __v2si __hisi = __builtin_ia32_cvtps2pi (__hisf);
  __v2si __losi = __builtin_ia32_cvtps2pi (__losf);
  return (__m64) __builtin_ia32_packssdw (__hisi, __losi);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtps_pi8(__m128 __A)
{
  __v4hi __tmp = (__v4hi) _mm_cvtps_pi16 (__A);
  return (__m64) __builtin_ia32_packsswb (__tmp, (__v4hi)0LL);
}



extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_shuffle_ps (__m128 __A, __m128 __B, int const __mask)
{
  return (__m128) __builtin_ia32_shufps ((__v4sf)__A, (__v4sf)__B, __mask);
}







extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_unpackhi_ps (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_unpckhps ((__v4sf)__A, (__v4sf)__B);
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_unpacklo_ps (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_unpcklps ((__v4sf)__A, (__v4sf)__B);
}



extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_loadh_pi (__m128 __A, __m64 const *__P)
{
  return (__m128) __builtin_ia32_loadhps ((__v4sf)__A, (const __v2sf *)__P);
}


extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_storeh_pi (__m64 *__P, __m128 __A)
{
  __builtin_ia32_storehps ((__v2sf *)__P, (__v4sf)__A);
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_movehl_ps (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_movhlps ((__v4sf)__A, (__v4sf)__B);
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_movelh_ps (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_ia32_movlhps ((__v4sf)__A, (__v4sf)__B);
}



extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_loadl_pi (__m128 __A, __m64 const *__P)
{
  return (__m128) __builtin_ia32_loadlps ((__v4sf)__A, (const __v2sf *)__P);
}


extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_storel_pi (__m64 *__P, __m128 __A)
{
  __builtin_ia32_storelps ((__v2sf *)__P, (__v4sf)__A);
}


extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_movemask_ps (__m128 __A)
{
  return __builtin_ia32_movmskps ((__v4sf)__A);
}


extern __inline unsigned int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_getcsr (void)
{
  return __builtin_ia32_stmxcsr ();
}


extern __inline unsigned int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_MM_GET_EXCEPTION_STATE (void)
{
  return _mm_getcsr() & 0x003f;
}

extern __inline unsigned int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_MM_GET_EXCEPTION_MASK (void)
{
  return _mm_getcsr() & 0x1f80;
}

extern __inline unsigned int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_MM_GET_ROUNDING_MODE (void)
{
  return _mm_getcsr() & 0x6000;
}

extern __inline unsigned int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_MM_GET_FLUSH_ZERO_MODE (void)
{
  return _mm_getcsr() & 0x8000;
}


extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_setcsr (unsigned int __I)
{
  __builtin_ia32_ldmxcsr (__I);
}


extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_MM_SET_EXCEPTION_STATE(unsigned int __mask)
{
  _mm_setcsr((_mm_getcsr() & ~0x003f) | __mask);
}

extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_MM_SET_EXCEPTION_MASK (unsigned int __mask)
{
  _mm_setcsr((_mm_getcsr() & ~0x1f80) | __mask);
}

extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_MM_SET_ROUNDING_MODE (unsigned int __mode)
{
  _mm_setcsr((_mm_getcsr() & ~0x6000) | __mode);
}

extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_MM_SET_FLUSH_ZERO_MODE (unsigned int __mode)
{
  _mm_setcsr((_mm_getcsr() & ~0x8000) | __mode);
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set_ss (float __F)
{
  return __extension__ (__m128)(__v4sf){ __F, 0.0f, 0.0f, 0.0f };
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set1_ps (float __F)
{
  return __extension__ (__m128)(__v4sf){ __F, __F, __F, __F };
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set_ps1 (float __F)
{
  return _mm_set1_ps (__F);
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_load_ss (float const *__P)
{
  return _mm_set_ss (*__P);
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_load1_ps (float const *__P)
{
  return _mm_set1_ps (*__P);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_load_ps1 (float const *__P)
{
  return _mm_load1_ps (__P);
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_load_ps (float const *__P)
{
  return *(__m128 *)__P;
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_loadu_ps (float const *__P)
{
  return *(__m128_u *)__P;
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_loadr_ps (float const *__P)
{
  __v4sf __tmp = *(__v4sf *)__P;
  return (__m128) __builtin_ia32_shufps (__tmp, __tmp, (((0) << 6) | ((1) << 4) | ((2) << 2) | (3)));
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set_ps (const float __Z, const float __Y, const float __X, const float __W)
{
  return __extension__ (__m128)(__v4sf){ __W, __X, __Y, __Z };
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_setr_ps (float __Z, float __Y, float __X, float __W)
{
  return __extension__ (__m128)(__v4sf){ __Z, __Y, __X, __W };
}


extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_store_ss (float *__P, __m128 __A)
{
  *__P = ((__v4sf)__A)[0];
}

extern __inline float __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtss_f32 (__m128 __A)
{
  return ((__v4sf)__A)[0];
}


extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_store_ps (float *__P, __m128 __A)
{
  *(__m128 *)__P = __A;
}


extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_storeu_ps (float *__P, __m128 __A)
{
  *(__m128_u *)__P = __A;
}


extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_store1_ps (float *__P, __m128 __A)
{
  __v4sf __va = (__v4sf)__A;
  __v4sf __tmp = __builtin_ia32_shufps (__va, __va, (((0) << 6) | ((0) << 4) | ((0) << 2) | (0)));
  _mm_storeu_ps (__P, __tmp);
}

extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_store_ps1 (float *__P, __m128 __A)
{
  _mm_store1_ps (__P, __A);
}


extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_storer_ps (float *__P, __m128 __A)
{
  __v4sf __va = (__v4sf)__A;
  __v4sf __tmp = __builtin_ia32_shufps (__va, __va, (((0) << 6) | ((1) << 4) | ((2) << 2) | (3)));
  _mm_store_ps (__P, __tmp);
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_move_ss (__m128 __A, __m128 __B)
{
  return (__m128) __builtin_shuffle ((__v4sf)__A, (__v4sf)__B,
                                     __extension__
                                     (__attribute__((__vector_size__ (16))) int)
                                     {4,1,2,3});
}



extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_extract_pi16 (__m64 const __A, int const __N)
{
  return (unsigned short) __builtin_ia32_vec_ext_v4hi ((__v4hi)__A, __N);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pextrw (__m64 const __A, int const __N)
{
  return _mm_extract_pi16 (__A, __N);
}
# 1049 "/usr/lib/gcc/x86_64-linux-gnu/14/include/xmmintrin.h" 3 4
extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_insert_pi16 (__m64 const __A, int const __D, int const __N)
{
  return (__m64) __builtin_ia32_vec_set_v4hi ((__v4hi)__A, __D, __N);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pinsrw (__m64 const __A, int const __D, int const __N)
{
  return _mm_insert_pi16 (__A, __D, __N);
}
# 1069 "/usr/lib/gcc/x86_64-linux-gnu/14/include/xmmintrin.h" 3 4
extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_max_pi16 (__m64 __A, __m64 __B)
{
  return (__m64) __builtin_ia32_pmaxsw ((__v4hi)__A, (__v4hi)__B);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pmaxsw (__m64 __A, __m64 __B)
{
  return _mm_max_pi16 (__A, __B);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_max_pu8 (__m64 __A, __m64 __B)
{
  return (__m64) __builtin_ia32_pmaxub ((__v8qi)__A, (__v8qi)__B);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pmaxub (__m64 __A, __m64 __B)
{
  return _mm_max_pu8 (__A, __B);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_min_pi16 (__m64 __A, __m64 __B)
{
  return (__m64) __builtin_ia32_pminsw ((__v4hi)__A, (__v4hi)__B);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pminsw (__m64 __A, __m64 __B)
{
  return _mm_min_pi16 (__A, __B);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_min_pu8 (__m64 __A, __m64 __B)
{
  return (__m64) __builtin_ia32_pminub ((__v8qi)__A, (__v8qi)__B);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pminub (__m64 __A, __m64 __B)
{
  return _mm_min_pu8 (__A, __B);
}


extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_movemask_pi8 (__m64 __A)
{
  return __builtin_ia32_pmovmskb ((__v8qi)__A);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pmovmskb (__m64 __A)
{
  return _mm_movemask_pi8 (__A);
}



extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_mulhi_pu16 (__m64 __A, __m64 __B)
{
  return (__m64) __builtin_ia32_pmulhuw ((__v4hi)__A, (__v4hi)__B);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pmulhuw (__m64 __A, __m64 __B)
{
  return _mm_mulhi_pu16 (__A, __B);
}




extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_shuffle_pi16 (__m64 __A, int const __N)
{
  return (__m64) __builtin_ia32_pshufw ((__v4hi)__A, __N);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pshufw (__m64 __A, int const __N)
{
  return _mm_shuffle_pi16 (__A, __N);
}
# 1171 "/usr/lib/gcc/x86_64-linux-gnu/14/include/xmmintrin.h" 3 4
extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_maskmove_si64 (__m64 __A, __m64 __N, char *__P)
{



  typedef long long __v2di __attribute__ ((__vector_size__ (16)));
  typedef char __v16qi __attribute__ ((__vector_size__ (16)));

  __v2di __A128 = __extension__ (__v2di) { ((__v1di) __A)[0], 0 };
  __v2di __N128 = __extension__ (__v2di) { ((__v1di) __N)[0], 0 };


  long unsigned int offset = ((long unsigned int) __P) & 0xf;
  if (offset)
    {


      if (offset > 8)
 offset = 8;
      __P = (char *) (((long unsigned int) __P) - offset);


      switch (offset)
 {
 case 1:
   __A128 = __builtin_ia32_pslldqi128 (__A128, 8);
   __N128 = __builtin_ia32_pslldqi128 (__N128, 8);
   break;
 case 2:
   __A128 = __builtin_ia32_pslldqi128 (__A128, 2 * 8);
   __N128 = __builtin_ia32_pslldqi128 (__N128, 2 * 8);
   break;
 case 3:
   __A128 = __builtin_ia32_pslldqi128 (__A128, 3 * 8);
   __N128 = __builtin_ia32_pslldqi128 (__N128, 3 * 8);
   break;
 case 4:
   __A128 = __builtin_ia32_pslldqi128 (__A128, 4 * 8);
   __N128 = __builtin_ia32_pslldqi128 (__N128, 4 * 8);
   break;
 case 5:
   __A128 = __builtin_ia32_pslldqi128 (__A128, 5 * 8);
   __N128 = __builtin_ia32_pslldqi128 (__N128, 5 * 8);
   break;
 case 6:
   __A128 = __builtin_ia32_pslldqi128 (__A128, 6 * 8);
   __N128 = __builtin_ia32_pslldqi128 (__N128, 6 * 8);
   break;
 case 7:
   __A128 = __builtin_ia32_pslldqi128 (__A128, 7 * 8);
   __N128 = __builtin_ia32_pslldqi128 (__N128, 7 * 8);
   break;
 case 8:
   __A128 = __builtin_ia32_pslldqi128 (__A128, 8 * 8);
   __N128 = __builtin_ia32_pslldqi128 (__N128, 8 * 8);
   break;
 default:
   break;
 }
    }
  __builtin_ia32_maskmovdqu ((__v16qi)__A128, (__v16qi)__N128, __P);



}

extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_maskmovq (__m64 __A, __m64 __N, char *__P)
{
  _mm_maskmove_si64 (__A, __N, __P);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_avg_pu8 (__m64 __A, __m64 __B)
{
  return (__m64) __builtin_ia32_pavgb ((__v8qi)__A, (__v8qi)__B);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pavgb (__m64 __A, __m64 __B)
{
  return _mm_avg_pu8 (__A, __B);
}


extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_avg_pu16 (__m64 __A, __m64 __B)
{
  return (__m64) __builtin_ia32_pavgw ((__v4hi)__A, (__v4hi)__B);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_pavgw (__m64 __A, __m64 __B)
{
  return _mm_avg_pu16 (__A, __B);
}




extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sad_pu8 (__m64 __A, __m64 __B)
{
  return (__m64) __builtin_ia32_psadbw ((__v8qi)__A, (__v8qi)__B);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_m_psadbw (__m64 __A, __m64 __B)
{
  return _mm_sad_pu8 (__A, __B);
}


extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_stream_pi (__m64 *__P, __m64 __A)
{
  __builtin_ia32_movntq ((unsigned long long *)__P, (unsigned long long)__A);
}


extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_stream_ps (float *__P, __m128 __A)
{
  __builtin_ia32_movntps (__P, (__v4sf)__A);
}



extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sfence (void)
{
  __builtin_ia32_sfence ();
}
# 1322 "/usr/lib/gcc/x86_64-linux-gnu/14/include/xmmintrin.h" 3 4
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/emmintrin.h" 1 3 4
# 1323 "/usr/lib/gcc/x86_64-linux-gnu/14/include/xmmintrin.h" 2 3 4
# 1334 "/usr/lib/gcc/x86_64-linux-gnu/14/include/xmmintrin.h" 3 4
extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_pause (void)
{
  __builtin_ia32_pause ();
}
# 32 "/usr/lib/gcc/x86_64-linux-gnu/14/include/emmintrin.h" 2 3 4
# 40 "/usr/lib/gcc/x86_64-linux-gnu/14/include/emmintrin.h" 3 4
typedef double __v2df __attribute__ ((__vector_size__ (16)));
typedef long long __v2di __attribute__ ((__vector_size__ (16)));
typedef unsigned long long __v2du __attribute__ ((__vector_size__ (16)));
typedef int __v4si __attribute__ ((__vector_size__ (16)));
typedef unsigned int __v4su __attribute__ ((__vector_size__ (16)));
typedef short __v8hi __attribute__ ((__vector_size__ (16)));
typedef unsigned short __v8hu __attribute__ ((__vector_size__ (16)));
typedef char __v16qi __attribute__ ((__vector_size__ (16)));
typedef signed char __v16qs __attribute__ ((__vector_size__ (16)));
typedef unsigned char __v16qu __attribute__ ((__vector_size__ (16)));



typedef long long __m128i __attribute__ ((__vector_size__ (16), __may_alias__));
typedef double __m128d __attribute__ ((__vector_size__ (16), __may_alias__));


typedef long long __m128i_u __attribute__ ((__vector_size__ (16), __may_alias__, __aligned__ (1)));
typedef double __m128d_u __attribute__ ((__vector_size__ (16), __may_alias__, __aligned__ (1)));






extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set_sd (double __F)
{
  return __extension__ (__m128d){ __F, 0.0 };
}


extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set1_pd (double __F)
{
  return __extension__ (__m128d){ __F, __F };
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set_pd1 (double __F)
{
  return _mm_set1_pd (__F);
}


extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set_pd (double __W, double __X)
{
  return __extension__ (__m128d){ __X, __W };
}


extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_setr_pd (double __W, double __X)
{
  return __extension__ (__m128d){ __W, __X };
}


extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_undefined_pd (void)
{
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Winit-self"
  __m128d __Y = __Y;
#pragma GCC diagnostic pop
  return __Y;
}


extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_setzero_pd (void)
{
  return __extension__ (__m128d){ 0.0, 0.0 };
}


extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_move_sd (__m128d __A, __m128d __B)
{
  return __extension__ (__m128d) __builtin_shuffle ((__v2df)__A, (__v2df)__B, (__v2di){2, 1});
}


extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_load_pd (double const *__P)
{
  return *(__m128d *)__P;
}


extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_loadu_pd (double const *__P)
{
  return *(__m128d_u *)__P;
}


extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_load1_pd (double const *__P)
{
  return _mm_set1_pd (*__P);
}


extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_load_sd (double const *__P)
{
  return _mm_set_sd (*__P);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_load_pd1 (double const *__P)
{
  return _mm_load1_pd (__P);
}


extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_loadr_pd (double const *__P)
{
  __m128d __tmp = _mm_load_pd (__P);
  return __builtin_ia32_shufpd (__tmp, __tmp, (((0) << 1) | (1)));
}


extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_store_pd (double *__P, __m128d __A)
{
  *(__m128d *)__P = __A;
}


extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_storeu_pd (double *__P, __m128d __A)
{
  *(__m128d_u *)__P = __A;
}


extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_store_sd (double *__P, __m128d __A)
{
  *__P = ((__v2df)__A)[0];
}

extern __inline double __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsd_f64 (__m128d __A)
{
  return ((__v2df)__A)[0];
}

extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_storel_pd (double *__P, __m128d __A)
{
  _mm_store_sd (__P, __A);
}


extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_storeh_pd (double *__P, __m128d __A)
{
  *__P = ((__v2df)__A)[1];
}



extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_store1_pd (double *__P, __m128d __A)
{
  _mm_store_pd (__P, __builtin_ia32_shufpd (__A, __A, (((0) << 1) | (0))));
}

extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_store_pd1 (double *__P, __m128d __A)
{
  _mm_store1_pd (__P, __A);
}


extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_storer_pd (double *__P, __m128d __A)
{
  _mm_store_pd (__P, __builtin_ia32_shufpd (__A, __A, (((0) << 1) | (1))));
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsi128_si32 (__m128i __A)
{
  return __builtin_ia32_vec_ext_v4si ((__v4si)__A, 0);
}



extern __inline long long __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsi128_si64 (__m128i __A)
{
  return ((__v2di)__A)[0];
}


extern __inline long long __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsi128_si64x (__m128i __A)
{
  return ((__v2di)__A)[0];
}


extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_add_pd (__m128d __A, __m128d __B)
{
  return (__m128d) ((__v2df)__A + (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_add_sd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_addsd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sub_pd (__m128d __A, __m128d __B)
{
  return (__m128d) ((__v2df)__A - (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sub_sd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_subsd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_mul_pd (__m128d __A, __m128d __B)
{
  return (__m128d) ((__v2df)__A * (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_mul_sd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_mulsd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_div_pd (__m128d __A, __m128d __B)
{
  return (__m128d) ((__v2df)__A / (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_div_sd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_divsd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sqrt_pd (__m128d __A)
{
  return (__m128d)__builtin_ia32_sqrtpd ((__v2df)__A);
}


extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sqrt_sd (__m128d __A, __m128d __B)
{
  __v2df __tmp = __builtin_ia32_movsd ((__v2df)__A, (__v2df)__B);
  return (__m128d)__builtin_ia32_sqrtsd ((__v2df)__tmp);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_min_pd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_minpd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_min_sd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_minsd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_max_pd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_maxpd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_max_sd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_maxsd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_and_pd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_andpd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_andnot_pd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_andnpd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_or_pd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_orpd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_xor_pd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_xorpd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpeq_pd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_cmpeqpd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmplt_pd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_cmpltpd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmple_pd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_cmplepd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpgt_pd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_cmpgtpd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpge_pd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_cmpgepd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpneq_pd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_cmpneqpd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpnlt_pd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_cmpnltpd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpnle_pd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_cmpnlepd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpngt_pd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_cmpngtpd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpnge_pd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_cmpngepd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpord_pd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_cmpordpd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpunord_pd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_cmpunordpd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpeq_sd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_cmpeqsd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmplt_sd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_cmpltsd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmple_sd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_cmplesd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpgt_sd (__m128d __A, __m128d __B)
{
  return (__m128d) __builtin_ia32_movsd ((__v2df) __A,
      (__v2df)
      __builtin_ia32_cmpltsd ((__v2df) __B,
         (__v2df)
         __A));
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpge_sd (__m128d __A, __m128d __B)
{
  return (__m128d) __builtin_ia32_movsd ((__v2df) __A,
      (__v2df)
      __builtin_ia32_cmplesd ((__v2df) __B,
         (__v2df)
         __A));
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpneq_sd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_cmpneqsd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpnlt_sd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_cmpnltsd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpnle_sd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_cmpnlesd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpngt_sd (__m128d __A, __m128d __B)
{
  return (__m128d) __builtin_ia32_movsd ((__v2df) __A,
      (__v2df)
      __builtin_ia32_cmpnltsd ((__v2df) __B,
          (__v2df)
          __A));
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpnge_sd (__m128d __A, __m128d __B)
{
  return (__m128d) __builtin_ia32_movsd ((__v2df) __A,
      (__v2df)
      __builtin_ia32_cmpnlesd ((__v2df) __B,
          (__v2df)
          __A));
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpord_sd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_cmpordsd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpunord_sd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_cmpunordsd ((__v2df)__A, (__v2df)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_comieq_sd (__m128d __A, __m128d __B)
{
  return __builtin_ia32_comisdeq ((__v2df)__A, (__v2df)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_comilt_sd (__m128d __A, __m128d __B)
{
  return __builtin_ia32_comisdlt ((__v2df)__A, (__v2df)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_comile_sd (__m128d __A, __m128d __B)
{
  return __builtin_ia32_comisdle ((__v2df)__A, (__v2df)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_comigt_sd (__m128d __A, __m128d __B)
{
  return __builtin_ia32_comisdgt ((__v2df)__A, (__v2df)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_comige_sd (__m128d __A, __m128d __B)
{
  return __builtin_ia32_comisdge ((__v2df)__A, (__v2df)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_comineq_sd (__m128d __A, __m128d __B)
{
  return __builtin_ia32_comisdneq ((__v2df)__A, (__v2df)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_ucomieq_sd (__m128d __A, __m128d __B)
{
  return __builtin_ia32_ucomisdeq ((__v2df)__A, (__v2df)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_ucomilt_sd (__m128d __A, __m128d __B)
{
  return __builtin_ia32_ucomisdlt ((__v2df)__A, (__v2df)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_ucomile_sd (__m128d __A, __m128d __B)
{
  return __builtin_ia32_ucomisdle ((__v2df)__A, (__v2df)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_ucomigt_sd (__m128d __A, __m128d __B)
{
  return __builtin_ia32_ucomisdgt ((__v2df)__A, (__v2df)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_ucomige_sd (__m128d __A, __m128d __B)
{
  return __builtin_ia32_ucomisdge ((__v2df)__A, (__v2df)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_ucomineq_sd (__m128d __A, __m128d __B)
{
  return __builtin_ia32_ucomisdneq ((__v2df)__A, (__v2df)__B);
}



extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set_epi64x (long long __q1, long long __q0)
{
  return __extension__ (__m128i)(__v2di){ __q0, __q1 };
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set_epi64 (__m64 __q1, __m64 __q0)
{
  return _mm_set_epi64x ((long long)__q1, (long long)__q0);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set_epi32 (int __q3, int __q2, int __q1, int __q0)
{
  return __extension__ (__m128i)(__v4si){ __q0, __q1, __q2, __q3 };
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set_epi16 (short __q7, short __q6, short __q5, short __q4,
        short __q3, short __q2, short __q1, short __q0)
{
  return __extension__ (__m128i)(__v8hi){
    __q0, __q1, __q2, __q3, __q4, __q5, __q6, __q7 };
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set_epi8 (char __q15, char __q14, char __q13, char __q12,
       char __q11, char __q10, char __q09, char __q08,
       char __q07, char __q06, char __q05, char __q04,
       char __q03, char __q02, char __q01, char __q00)
{
  return __extension__ (__m128i)(__v16qi){
    __q00, __q01, __q02, __q03, __q04, __q05, __q06, __q07,
    __q08, __q09, __q10, __q11, __q12, __q13, __q14, __q15
  };
}



extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set1_epi64x (long long __A)
{
  return _mm_set_epi64x (__A, __A);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set1_epi64 (__m64 __A)
{
  return _mm_set_epi64 (__A, __A);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set1_epi32 (int __A)
{
  return _mm_set_epi32 (__A, __A, __A, __A);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set1_epi16 (short __A)
{
  return _mm_set_epi16 (__A, __A, __A, __A, __A, __A, __A, __A);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_set1_epi8 (char __A)
{
  return _mm_set_epi8 (__A, __A, __A, __A, __A, __A, __A, __A,
         __A, __A, __A, __A, __A, __A, __A, __A);
}




extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_setr_epi64 (__m64 __q0, __m64 __q1)
{
  return _mm_set_epi64 (__q1, __q0);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_setr_epi32 (int __q0, int __q1, int __q2, int __q3)
{
  return _mm_set_epi32 (__q3, __q2, __q1, __q0);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_setr_epi16 (short __q0, short __q1, short __q2, short __q3,
         short __q4, short __q5, short __q6, short __q7)
{
  return _mm_set_epi16 (__q7, __q6, __q5, __q4, __q3, __q2, __q1, __q0);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_setr_epi8 (char __q00, char __q01, char __q02, char __q03,
        char __q04, char __q05, char __q06, char __q07,
        char __q08, char __q09, char __q10, char __q11,
        char __q12, char __q13, char __q14, char __q15)
{
  return _mm_set_epi8 (__q15, __q14, __q13, __q12, __q11, __q10, __q09, __q08,
         __q07, __q06, __q05, __q04, __q03, __q02, __q01, __q00);
}



extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_load_si128 (__m128i const *__P)
{
  return *__P;
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_loadu_si128 (__m128i_u const *__P)
{
  return *__P;
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_loadl_epi64 (__m128i_u const *__P)
{
  return _mm_set_epi64 ((__m64)0LL, *(__m64_u *)__P);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_loadu_si64 (void const *__P)
{
  return _mm_loadl_epi64 ((__m128i_u *)__P);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_loadu_si32 (void const *__P)
{
  return _mm_set_epi32 (0, 0, 0, (*(__m32_u *)__P)[0]);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_loadu_si16 (void const *__P)
{
  return _mm_set_epi16 (0, 0, 0, 0, 0, 0, 0, (*(__m16_u *)__P)[0]);
}

extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_store_si128 (__m128i *__P, __m128i __B)
{
  *__P = __B;
}

extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_storeu_si128 (__m128i_u *__P, __m128i __B)
{
  *__P = __B;
}

extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_storel_epi64 (__m128i_u *__P, __m128i __B)
{
  *(__m64_u *)__P = (__m64) ((__v2di)__B)[0];
}

extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_storeu_si64 (void *__P, __m128i __B)
{
  _mm_storel_epi64 ((__m128i_u *)__P, __B);
}

extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_storeu_si32 (void *__P, __m128i __B)
{
  *(__m32_u *)__P = (__m32) ((__v4si)__B)[0];
}

extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_storeu_si16 (void *__P, __m128i __B)
{
  *(__m16_u *)__P = (__m16) ((__v8hi)__B)[0];
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_movepi64_pi64 (__m128i __B)
{
  return (__m64) ((__v2di)__B)[0];
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_movpi64_epi64 (__m64 __A)
{
  return _mm_set_epi64 ((__m64)0LL, __A);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_move_epi64 (__m128i __A)
{
  return (__m128i)__builtin_ia32_movq128 ((__v2di) __A);
}


extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_undefined_si128 (void)
{
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Winit-self"
  __m128i __Y = __Y;
#pragma GCC diagnostic pop
  return __Y;
}


extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_setzero_si128 (void)
{
  return __extension__ (__m128i)(__v4si){ 0, 0, 0, 0 };
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtepi32_pd (__m128i __A)
{
  return (__m128d)__builtin_ia32_cvtdq2pd ((__v4si) __A);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtepi32_ps (__m128i __A)
{
  return (__m128)__builtin_ia32_cvtdq2ps ((__v4si) __A);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtpd_epi32 (__m128d __A)
{
  return (__m128i)__builtin_ia32_cvtpd2dq ((__v2df) __A);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtpd_pi32 (__m128d __A)
{
  return (__m64)__builtin_ia32_cvtpd2pi ((__v2df) __A);
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtpd_ps (__m128d __A)
{
  return (__m128)__builtin_ia32_cvtpd2ps ((__v2df) __A);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvttpd_epi32 (__m128d __A)
{
  return (__m128i)__builtin_ia32_cvttpd2dq ((__v2df) __A);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvttpd_pi32 (__m128d __A)
{
  return (__m64)__builtin_ia32_cvttpd2pi ((__v2df) __A);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtpi32_pd (__m64 __A)
{
  return (__m128d)__builtin_ia32_cvtpi2pd ((__v2si) __A);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtps_epi32 (__m128 __A)
{
  return (__m128i)__builtin_ia32_cvtps2dq ((__v4sf) __A);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvttps_epi32 (__m128 __A)
{
  return (__m128i)__builtin_ia32_cvttps2dq ((__v4sf) __A);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtps_pd (__m128 __A)
{
  return (__m128d)__builtin_ia32_cvtps2pd ((__v4sf) __A);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsd_si32 (__m128d __A)
{
  return __builtin_ia32_cvtsd2si ((__v2df) __A);
}



extern __inline long long __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsd_si64 (__m128d __A)
{
  return __builtin_ia32_cvtsd2si64 ((__v2df) __A);
}


extern __inline long long __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsd_si64x (__m128d __A)
{
  return __builtin_ia32_cvtsd2si64 ((__v2df) __A);
}


extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvttsd_si32 (__m128d __A)
{
  return __builtin_ia32_cvttsd2si ((__v2df) __A);
}



extern __inline long long __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvttsd_si64 (__m128d __A)
{
  return __builtin_ia32_cvttsd2si64 ((__v2df) __A);
}


extern __inline long long __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvttsd_si64x (__m128d __A)
{
  return __builtin_ia32_cvttsd2si64 ((__v2df) __A);
}


extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsd_ss (__m128 __A, __m128d __B)
{
  return (__m128)__builtin_ia32_cvtsd2ss ((__v4sf) __A, (__v2df) __B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsi32_sd (__m128d __A, int __B)
{
  return (__m128d)__builtin_ia32_cvtsi2sd ((__v2df) __A, __B);
}



extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsi64_sd (__m128d __A, long long __B)
{
  return (__m128d)__builtin_ia32_cvtsi642sd ((__v2df) __A, __B);
}


extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsi64x_sd (__m128d __A, long long __B)
{
  return (__m128d)__builtin_ia32_cvtsi642sd ((__v2df) __A, __B);
}


extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtss_sd (__m128d __A, __m128 __B)
{
  return (__m128d)__builtin_ia32_cvtss2sd ((__v2df) __A, (__v4sf)__B);
}


extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_shuffle_pd(__m128d __A, __m128d __B, const int __mask)
{
  return (__m128d)__builtin_ia32_shufpd ((__v2df)__A, (__v2df)__B, __mask);
}






extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_unpackhi_pd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_unpckhpd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_unpacklo_pd (__m128d __A, __m128d __B)
{
  return (__m128d)__builtin_ia32_unpcklpd ((__v2df)__A, (__v2df)__B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_loadh_pd (__m128d __A, double const *__B)
{
  return (__m128d)__builtin_ia32_loadhpd ((__v2df)__A, __B);
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_loadl_pd (__m128d __A, double const *__B)
{
  return (__m128d)__builtin_ia32_loadlpd ((__v2df)__A, __B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_movemask_pd (__m128d __A)
{
  return __builtin_ia32_movmskpd ((__v2df)__A);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_packs_epi16 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_packsswb128 ((__v8hi)__A, (__v8hi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_packs_epi32 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_packssdw128 ((__v4si)__A, (__v4si)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_packus_epi16 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_packuswb128 ((__v8hi)__A, (__v8hi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_unpackhi_epi8 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_punpckhbw128 ((__v16qi)__A, (__v16qi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_unpackhi_epi16 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_punpckhwd128 ((__v8hi)__A, (__v8hi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_unpackhi_epi32 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_punpckhdq128 ((__v4si)__A, (__v4si)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_unpackhi_epi64 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_punpckhqdq128 ((__v2di)__A, (__v2di)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_unpacklo_epi8 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_punpcklbw128 ((__v16qi)__A, (__v16qi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_unpacklo_epi16 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_punpcklwd128 ((__v8hi)__A, (__v8hi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_unpacklo_epi32 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_punpckldq128 ((__v4si)__A, (__v4si)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_unpacklo_epi64 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_punpcklqdq128 ((__v2di)__A, (__v2di)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_add_epi8 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v16qu)__A + (__v16qu)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_add_epi16 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v8hu)__A + (__v8hu)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_add_epi32 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v4su)__A + (__v4su)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_add_epi64 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v2du)__A + (__v2du)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_adds_epi8 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_paddsb128 ((__v16qi)__A, (__v16qi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_adds_epi16 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_paddsw128 ((__v8hi)__A, (__v8hi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_adds_epu8 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_paddusb128 ((__v16qi)__A, (__v16qi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_adds_epu16 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_paddusw128 ((__v8hi)__A, (__v8hi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sub_epi8 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v16qu)__A - (__v16qu)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sub_epi16 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v8hu)__A - (__v8hu)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sub_epi32 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v4su)__A - (__v4su)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sub_epi64 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v2du)__A - (__v2du)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_subs_epi8 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_psubsb128 ((__v16qi)__A, (__v16qi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_subs_epi16 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_psubsw128 ((__v8hi)__A, (__v8hi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_subs_epu8 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_psubusb128 ((__v16qi)__A, (__v16qi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_subs_epu16 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_psubusw128 ((__v8hi)__A, (__v8hi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_madd_epi16 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_pmaddwd128 ((__v8hi)__A, (__v8hi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_mulhi_epi16 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_pmulhw128 ((__v8hi)__A, (__v8hi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_mullo_epi16 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v8hu)__A * (__v8hu)__B);
}

extern __inline __m64 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_mul_su32 (__m64 __A, __m64 __B)
{
  return (__m64)__builtin_ia32_pmuludq ((__v2si)__A, (__v2si)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_mul_epu32 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_pmuludq128 ((__v4si)__A, (__v4si)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_slli_epi16 (__m128i __A, int __B)
{
  return (__m128i)__builtin_ia32_psllwi128 ((__v8hi)__A, __B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_slli_epi32 (__m128i __A, int __B)
{
  return (__m128i)__builtin_ia32_pslldi128 ((__v4si)__A, __B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_slli_epi64 (__m128i __A, int __B)
{
  return (__m128i)__builtin_ia32_psllqi128 ((__v2di)__A, __B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_srai_epi16 (__m128i __A, int __B)
{
  return (__m128i)__builtin_ia32_psrawi128 ((__v8hi)__A, __B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_srai_epi32 (__m128i __A, int __B)
{
  return (__m128i)__builtin_ia32_psradi128 ((__v4si)__A, __B);
}


extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_bsrli_si128 (__m128i __A, const int __N)
{
  return (__m128i)__builtin_ia32_psrldqi128 (__A, __N * 8);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_bslli_si128 (__m128i __A, const int __N)
{
  return (__m128i)__builtin_ia32_pslldqi128 (__A, __N * 8);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_srli_si128 (__m128i __A, const int __N)
{
  return (__m128i)__builtin_ia32_psrldqi128 (__A, __N * 8);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_slli_si128 (__m128i __A, const int __N)
{
  return (__m128i)__builtin_ia32_pslldqi128 (__A, __N * 8);
}
# 1248 "/usr/lib/gcc/x86_64-linux-gnu/14/include/emmintrin.h" 3 4
extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_srli_epi16 (__m128i __A, int __B)
{
  return (__m128i)__builtin_ia32_psrlwi128 ((__v8hi)__A, __B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_srli_epi32 (__m128i __A, int __B)
{
  return (__m128i)__builtin_ia32_psrldi128 ((__v4si)__A, __B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_srli_epi64 (__m128i __A, int __B)
{
  return (__m128i)__builtin_ia32_psrlqi128 ((__v2di)__A, __B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sll_epi16 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_psllw128((__v8hi)__A, (__v8hi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sll_epi32 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_pslld128((__v4si)__A, (__v4si)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sll_epi64 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_psllq128((__v2di)__A, (__v2di)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sra_epi16 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_psraw128 ((__v8hi)__A, (__v8hi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sra_epi32 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_psrad128 ((__v4si)__A, (__v4si)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_srl_epi16 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_psrlw128 ((__v8hi)__A, (__v8hi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_srl_epi32 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_psrld128 ((__v4si)__A, (__v4si)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_srl_epi64 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_psrlq128 ((__v2di)__A, (__v2di)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_and_si128 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v2du)__A & (__v2du)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_andnot_si128 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_pandn128 ((__v2di)__A, (__v2di)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_or_si128 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v2du)__A | (__v2du)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_xor_si128 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v2du)__A ^ (__v2du)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpeq_epi8 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v16qi)__A == (__v16qi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpeq_epi16 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v8hi)__A == (__v8hi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpeq_epi32 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v4si)__A == (__v4si)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmplt_epi8 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v16qs)__A < (__v16qs)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmplt_epi16 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v8hi)__A < (__v8hi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmplt_epi32 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v4si)__A < (__v4si)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpgt_epi8 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v16qs)__A > (__v16qs)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpgt_epi16 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v8hi)__A > (__v8hi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cmpgt_epi32 (__m128i __A, __m128i __B)
{
  return (__m128i) ((__v4si)__A > (__v4si)__B);
}


extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_extract_epi16 (__m128i const __A, int const __N)
{
  return (unsigned short) __builtin_ia32_vec_ext_v8hi ((__v8hi)__A, __N);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_insert_epi16 (__m128i const __A, int const __D, int const __N)
{
  return (__m128i) __builtin_ia32_vec_set_v8hi ((__v8hi)__A, __D, __N);
}
# 1412 "/usr/lib/gcc/x86_64-linux-gnu/14/include/emmintrin.h" 3 4
extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_max_epi16 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_pmaxsw128 ((__v8hi)__A, (__v8hi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_max_epu8 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_pmaxub128 ((__v16qi)__A, (__v16qi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_min_epi16 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_pminsw128 ((__v8hi)__A, (__v8hi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_min_epu8 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_pminub128 ((__v16qi)__A, (__v16qi)__B);
}

extern __inline int __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_movemask_epi8 (__m128i __A)
{
  return __builtin_ia32_pmovmskb128 ((__v16qi)__A);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_mulhi_epu16 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_pmulhuw128 ((__v8hi)__A, (__v8hi)__B);
}


extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_shufflehi_epi16 (__m128i __A, const int __mask)
{
  return (__m128i)__builtin_ia32_pshufhw ((__v8hi)__A, __mask);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_shufflelo_epi16 (__m128i __A, const int __mask)
{
  return (__m128i)__builtin_ia32_pshuflw ((__v8hi)__A, __mask);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_shuffle_epi32 (__m128i __A, const int __mask)
{
  return (__m128i)__builtin_ia32_pshufd ((__v4si)__A, __mask);
}
# 1475 "/usr/lib/gcc/x86_64-linux-gnu/14/include/emmintrin.h" 3 4
extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_maskmoveu_si128 (__m128i __A, __m128i __B, char *__C)
{
  __builtin_ia32_maskmovdqu ((__v16qi)__A, (__v16qi)__B, __C);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_avg_epu8 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_pavgb128 ((__v16qi)__A, (__v16qi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_avg_epu16 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_pavgw128 ((__v8hi)__A, (__v8hi)__B);
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_sad_epu8 (__m128i __A, __m128i __B)
{
  return (__m128i)__builtin_ia32_psadbw128 ((__v16qi)__A, (__v16qi)__B);
}

extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_stream_si32 (int *__A, int __B)
{
  __builtin_ia32_movnti (__A, __B);
}


extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_stream_si64 (long long int *__A, long long int __B)
{
  __builtin_ia32_movnti64 (__A, __B);
}


extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_stream_si128 (__m128i *__A, __m128i __B)
{
  __builtin_ia32_movntdq ((__v2di *)__A, (__v2di)__B);
}

extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_stream_pd (double *__A, __m128d __B)
{
  __builtin_ia32_movntpd (__A, (__v2df)__B);
}

extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_clflush (void const *__A)
{
  __builtin_ia32_clflush (__A);
}

extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_lfence (void)
{
  __builtin_ia32_lfence ();
}

extern __inline void __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_mfence (void)
{
  __builtin_ia32_mfence ();
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsi32_si128 (int __A)
{
  return _mm_set_epi32 (0, 0, 0, __A);
}



extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsi64_si128 (long long __A)
{
  return _mm_set_epi64x (0, __A);
}


extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_cvtsi64x_si128 (long long __A)
{
  return _mm_set_epi64x (0, __A);
}




extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_castpd_ps(__m128d __A)
{
  return (__m128) __A;
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_castpd_si128(__m128d __A)
{
  return (__m128i) __A;
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_castps_pd(__m128 __A)
{
  return (__m128d) __A;
}

extern __inline __m128i __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_castps_si128(__m128 __A)
{
  return (__m128i) __A;
}

extern __inline __m128 __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_castsi128_ps(__m128i __A)
{
  return (__m128) __A;
}

extern __inline __m128d __attribute__((__gnu_inline__, __always_inline__, __artificial__))
_mm_castsi128_pd(__m128i __A)
{
  return (__m128d) __A;
}
# 355 "include/mimalloc/atomic.h" 2

# 355 "include/mimalloc/atomic.h"
static inline void mi_atomic_yield(void) {
  _mm_pause();
}
# 463 "include/mimalloc/atomic.h"
void _mi_error_message(int err, const char* fmt, ...);



static inline 
# 467 "include/mimalloc/atomic.h" 3 4
             _Bool 
# 467 "include/mimalloc/atomic.h"
                  mi_lock_try_acquire(pthread_mutex_t* lock) {
  return (pthread_mutex_trylock(lock) == 0);
}
static inline void mi_lock_acquire(pthread_mutex_t* lock) {
  const int err = pthread_mutex_lock(lock);
  if (err != 0) {
    _mi_error_message(err, "internal error: lock cannot be acquired\n");
  }
}
static inline void mi_lock_release(pthread_mutex_t* lock) {
  pthread_mutex_unlock(lock);
}
static inline void mi_lock_init(pthread_mutex_t* lock) {
  pthread_mutex_init(lock, 
# 480 "include/mimalloc/atomic.h" 3 4
                          ((void *)0)
# 480 "include/mimalloc/atomic.h"
                              );
}
static inline void mi_lock_done(pthread_mutex_t* lock) {
  pthread_mutex_destroy(lock);
}
# 28 "include/mimalloc/types.h" 2
# 138 "include/mimalloc/types.h"
typedef int64_t mi_ssize_t;
# 237 "include/mimalloc/types.h"
typedef uintptr_t mi_encoded_t;


typedef size_t mi_threadid_t;


typedef struct mi_block_s {
  mi_encoded_t next;
} mi_block_t;
# 256 "include/mimalloc/types.h"
typedef enum mi_delayed_e {
  MI_USE_DELAYED_FREE = 0,
  MI_DELAYED_FREEING = 1,
  MI_NO_DELAYED_FREE = 2,
  MI_NEVER_DELAYED_FREE = 3
} mi_delayed_t;





typedef union mi_page_flags_s {
  uint8_t full_aligned;
  struct {
    uint8_t in_full : 1;
    uint8_t has_aligned : 1;
  } x;
} mi_page_flags_t;
# 287 "include/mimalloc/types.h"
typedef uintptr_t mi_thread_free_t;
# 317 "include/mimalloc/types.h"
typedef struct mi_page_s {

  uint32_t slice_count;
  uint32_t slice_offset;
  uint8_t is_committed:1;
  uint8_t is_zero_init:1;
  uint8_t is_huge:1;


  uint16_t capacity;
  uint16_t reserved;
  mi_page_flags_t flags;
  uint8_t free_is_zero:1;
  uint8_t retire_expire:7;

  mi_block_t* free;
  mi_block_t* local_free;
  uint16_t used;
  uint8_t block_size_shift;
  uint8_t heap_tag;

  size_t block_size;
  uint8_t* page_start;





  _Atomic(mi_thread_free_t) xthread_free;
  _Atomic(uintptr_t) xheap;

  struct mi_page_s* next;
  struct mi_page_s* prev;


  void* padding[1];
} mi_page_t;







typedef enum mi_page_kind_e {
  MI_PAGE_SMALL,
  MI_PAGE_MEDIUM,
  MI_PAGE_LARGE,
  MI_PAGE_HUGE

} mi_page_kind_t;

typedef enum mi_segment_kind_e {
  MI_SEGMENT_NORMAL,
  MI_SEGMENT_HUGE,
} mi_segment_kind_t;
# 396 "include/mimalloc/types.h"
typedef struct mi_commit_mask_s {
  size_t mask[(((1ULL<<( 9 + (13 + (3)))) / ((1ULL<< (13 + (3))))) / ((1<<(3))*8))];
} mi_commit_mask_t;

typedef mi_page_t mi_slice_t;
typedef int64_t mi_msecs_t;







typedef enum mi_memkind_e {
  MI_MEM_NONE,
  MI_MEM_EXTERNAL,
  MI_MEM_STATIC,
  MI_MEM_OS,
  MI_MEM_OS_HUGE,
  MI_MEM_OS_REMAP,
  MI_MEM_ARENA
} mi_memkind_t;

static inline 
# 419 "include/mimalloc/types.h" 3 4
             _Bool 
# 419 "include/mimalloc/types.h"
                  mi_memkind_is_os(mi_memkind_t memkind) {
  return (memkind >= MI_MEM_OS && memkind <= MI_MEM_OS_REMAP);
}

typedef struct mi_memid_os_info {
  void* base;
  size_t size;
} mi_memid_os_info_t;

typedef struct mi_memid_arena_info {
  size_t block_index;
  mi_arena_id_t id;
  
# 431 "include/mimalloc/types.h" 3 4
 _Bool 
# 431 "include/mimalloc/types.h"
               is_exclusive;
} mi_memid_arena_info_t;

typedef struct mi_memid_s {
  union {
    mi_memid_os_info_t os;
    mi_memid_arena_info_t arena;
  } mem;
  
# 439 "include/mimalloc/types.h" 3 4
 _Bool 
# 439 "include/mimalloc/types.h"
               is_pinned;
  
# 440 "include/mimalloc/types.h" 3 4
 _Bool 
# 440 "include/mimalloc/types.h"
               initially_committed;
  
# 441 "include/mimalloc/types.h" 3 4
 _Bool 
# 441 "include/mimalloc/types.h"
               initially_zero;
  mi_memkind_t memkind;
} mi_memid_t;
# 460 "include/mimalloc/types.h"
typedef struct mi_subproc_s mi_subproc_t;

typedef struct mi_segment_s {

  mi_memid_t memid;
  
# 465 "include/mimalloc/types.h" 3 4
 _Bool 
# 465 "include/mimalloc/types.h"
                   allow_decommit;
  
# 466 "include/mimalloc/types.h" 3 4
 _Bool 
# 466 "include/mimalloc/types.h"
                   allow_purge;
  size_t segment_size;
  mi_subproc_t* subproc;


  mi_msecs_t purge_expire;
  mi_commit_mask_t purge_mask;
  mi_commit_mask_t commit_mask;


  struct mi_segment_s* next;
  
# 477 "include/mimalloc/types.h" 3 4
 _Bool 
# 477 "include/mimalloc/types.h"
                   was_reclaimed;
  
# 478 "include/mimalloc/types.h" 3 4
 _Bool 
# 478 "include/mimalloc/types.h"
                   dont_free;

  size_t abandoned;
  size_t abandoned_visits;
  size_t used;
  uintptr_t cookie;

  struct mi_segment_s* abandoned_os_next;
  struct mi_segment_s* abandoned_os_prev;

  size_t segment_slices;
  size_t segment_info_slices;


  mi_segment_kind_t kind;
  size_t slice_entries;
  _Atomic(mi_threadid_t) thread_id;

  mi_slice_t slices[((1ULL<<( 9 + (13 + (3)))) / (1ULL<< (13 + (3))))+1];
} mi_segment_t;
# 514 "include/mimalloc/types.h"
typedef struct mi_tld_s mi_tld_t;


typedef struct mi_page_queue_s {
  mi_page_t* first;
  mi_page_t* last;
  size_t block_size;
} mi_page_queue_t;




typedef struct mi_random_cxt_s {
  uint32_t input[16];
  uint32_t output[16];
  int output_available;
  
# 530 "include/mimalloc/types.h" 3 4
 _Bool 
# 530 "include/mimalloc/types.h"
          weak;
} mi_random_ctx_t;
# 551 "include/mimalloc/types.h"
struct mi_heap_s {
  mi_tld_t* tld;
  _Atomic(mi_block_t*) thread_delayed_free;
  mi_threadid_t thread_id;
  mi_arena_id_t arena_id;
  uintptr_t cookie;
  uintptr_t keys[2];
  mi_random_ctx_t random;
  size_t page_count;
  size_t page_retired_min;
  size_t page_retired_max;
  mi_heap_t* next;
  
# 563 "include/mimalloc/types.h" 3 4
 _Bool 
# 563 "include/mimalloc/types.h"
                       no_reclaim;
  uint8_t tag;







  mi_page_t* pages_free_direct[((128) + 0 + 1)];
  mi_page_queue_t pages[((73U)+1) + 1];
};
# 624 "include/mimalloc/types.h"
typedef struct mi_stat_count_s {
  int64_t allocated;
  int64_t freed;
  int64_t peak;
  int64_t current;
} mi_stat_count_t;

typedef struct mi_stat_counter_s {
  int64_t total;
  int64_t count;
} mi_stat_counter_t;

typedef struct mi_stats_s {
  mi_stat_count_t segments;
  mi_stat_count_t pages;
  mi_stat_count_t reserved;
  mi_stat_count_t committed;
  mi_stat_count_t reset;
  mi_stat_count_t purged;
  mi_stat_count_t page_committed;
  mi_stat_count_t segments_abandoned;
  mi_stat_count_t pages_abandoned;
  mi_stat_count_t threads;
  mi_stat_count_t normal;
  mi_stat_count_t huge;
  mi_stat_count_t large;
  mi_stat_count_t malloc;
  mi_stat_count_t segments_cache;
  mi_stat_counter_t pages_extended;
  mi_stat_counter_t mmap_calls;
  mi_stat_counter_t commit_calls;
  mi_stat_counter_t reset_calls;
  mi_stat_counter_t purge_calls;
  mi_stat_counter_t page_no_retire;
  mi_stat_counter_t searches;
  mi_stat_counter_t normal_count;
  mi_stat_counter_t huge_count;
  mi_stat_counter_t large_count;
  mi_stat_counter_t arena_count;
  mi_stat_counter_t arena_crossover_count;
  mi_stat_counter_t arena_rollback_count;
  mi_stat_counter_t guarded_alloc_count;



} mi_stats_t;



void _mi_stat_increase(mi_stat_count_t* stat, size_t amount);
void _mi_stat_decrease(mi_stat_count_t* stat, size_t amount);

void _mi_stat_adjust_increase(mi_stat_count_t* stat, size_t amount);
void _mi_stat_adjust_decrease(mi_stat_count_t* stat, size_t amount);

void _mi_stat_counter_increase(mi_stat_counter_t* stat, size_t amount);
# 705 "include/mimalloc/types.h"
struct mi_subproc_s {
  _Atomic(size_t) abandoned_count;
  _Atomic(size_t) abandoned_os_list_count;
  pthread_mutex_t abandoned_os_lock;
  pthread_mutex_t abandoned_os_visit_lock;
  mi_segment_t* abandoned_os_list;
  mi_segment_t* abandoned_os_list_tail;
  mi_memid_t memid;
};







typedef struct mi_span_queue_s {
  mi_slice_t* first;
  mi_slice_t* last;
  size_t slice_count;
} mi_span_queue_t;




typedef struct mi_segments_tld_s {
  mi_span_queue_t spans[(35)+1];
  size_t count;
  size_t peak_count;
  size_t current_size;
  size_t peak_size;
  size_t reclaim_count;
  mi_subproc_t* subproc;
  mi_stats_t* stats;
} mi_segments_tld_t;


struct mi_tld_s {
  unsigned long long heartbeat;
  
# 744 "include/mimalloc/types.h" 3 4
 _Bool 
# 744 "include/mimalloc/types.h"
                     recurse;
  mi_heap_t* heap_backing;
  mi_heap_t* heaps;
  mi_segments_tld_t segments;
  mi_stats_t stats;
};
# 18 "include/mimalloc/internal.h" 2
# 1 "include/mimalloc/track.h" 1






       
# 19 "include/mimalloc/internal.h" 2
# 66 "include/mimalloc/internal.h"
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stdarg.h" 1 3 4
# 40 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stdarg.h" 3 4

# 40 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stdarg.h" 3 4
typedef __builtin_va_list __gnuc_va_list;
# 103 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stdarg.h" 3 4
typedef __gnuc_va_list va_list;
# 67 "include/mimalloc/internal.h" 2

# 67 "include/mimalloc/internal.h"
void _mi_vsnprintf(char* buf, size_t bufsize, const char* fmt, va_list args);
void _mi_snprintf(char* buf, size_t buflen, const char* fmt, ...);
char _mi_toupper(char c);
int _mi_strnicmp(const char* s, const char* t, size_t n);
void _mi_strlcpy(char* dest, const char* src, size_t dest_size);
void _mi_strlcat(char* dest, const char* src, size_t dest_size);
size_t _mi_strlen(const char* s);
size_t _mi_strnlen(const char* s, size_t max_len);

# 75 "include/mimalloc/internal.h" 3 4
_Bool 
# 75 "include/mimalloc/internal.h"
           _mi_getenv(const char* name, char* result, size_t result_size);


void _mi_fputs(mi_output_fun* out, void* arg, const char* prefix, const char* message);
void _mi_fprintf(mi_output_fun* out, void* arg, const char* fmt, ...);
void _mi_warning_message(const char* fmt, ...);
void _mi_verbose_message(const char* fmt, ...);
void _mi_trace_message(const char* fmt, ...);
void _mi_options_init(void);
long _mi_option_get_fast(mi_option_t option);
void _mi_error_message(int err, const char* fmt, ...);


void _mi_random_init(mi_random_ctx_t* ctx);
void _mi_random_init_weak(mi_random_ctx_t* ctx);
void _mi_random_reinit_if_weak(mi_random_ctx_t * ctx);
void _mi_random_split(mi_random_ctx_t* ctx, mi_random_ctx_t* new_ctx);
uintptr_t _mi_random_next(mi_random_ctx_t* ctx);
uintptr_t _mi_heap_random_next(mi_heap_t* heap);
uintptr_t _mi_os_random_weak(uintptr_t extra_seed);
static inline uintptr_t _mi_random_shuffle(uintptr_t x);


extern __attribute__((aligned(64))) mi_stats_t _mi_stats_main;
extern __attribute__((visibility("hidden"))) __attribute__((aligned(64))) const mi_page_t _mi_page_empty;
void _mi_process_load(void);
void _mi_process_done(void);

# 102 "include/mimalloc/internal.h" 3 4
_Bool 
# 102 "include/mimalloc/internal.h"
           _mi_is_redirected(void);

# 103 "include/mimalloc/internal.h" 3 4
_Bool 
# 103 "include/mimalloc/internal.h"
           _mi_allocator_init(const char** message);
void _mi_allocator_done(void);

# 105 "include/mimalloc/internal.h" 3 4
_Bool 
# 105 "include/mimalloc/internal.h"
           _mi_is_main_thread(void);
size_t _mi_current_thread_count(void);

# 107 "include/mimalloc/internal.h" 3 4
_Bool 
# 107 "include/mimalloc/internal.h"
           _mi_preloading(void);
void _mi_thread_done(mi_heap_t* heap);
void _mi_thread_data_collect(void);
void _mi_tld_init(mi_tld_t* tld, mi_heap_t* bheap);
mi_threadid_t _mi_thread_id(void) ;
mi_heap_t* _mi_heap_main_get(void);
mi_subproc_t* _mi_subproc_from_id(mi_subproc_id_t subproc_id);
void _mi_heap_guarded_init(mi_heap_t* heap);


void _mi_os_init(void);
void* _mi_os_alloc(size_t size, mi_memid_t* memid);
void _mi_os_free(void* p, size_t size, mi_memid_t memid);
void _mi_os_free_ex(void* p, size_t size, 
# 120 "include/mimalloc/internal.h" 3 4
                                                _Bool 
# 120 "include/mimalloc/internal.h"
                                                     still_committed, mi_memid_t memid);

size_t _mi_os_page_size(void);
size_t _mi_os_good_alloc_size(size_t size);

# 124 "include/mimalloc/internal.h" 3 4
_Bool 
# 124 "include/mimalloc/internal.h"
           _mi_os_has_overcommit(void);

# 125 "include/mimalloc/internal.h" 3 4
_Bool 
# 125 "include/mimalloc/internal.h"
           _mi_os_has_virtual_reserve(void);


# 127 "include/mimalloc/internal.h" 3 4
_Bool 
# 127 "include/mimalloc/internal.h"
           _mi_os_reset(void* addr, size_t size);

# 128 "include/mimalloc/internal.h" 3 4
_Bool 
# 128 "include/mimalloc/internal.h"
           _mi_os_commit(void* p, size_t size, 
# 128 "include/mimalloc/internal.h" 3 4
                                               _Bool
# 128 "include/mimalloc/internal.h"
                                                   * is_zero);

# 129 "include/mimalloc/internal.h" 3 4
_Bool 
# 129 "include/mimalloc/internal.h"
           _mi_os_decommit(void* addr, size_t size);

# 130 "include/mimalloc/internal.h" 3 4
_Bool 
# 130 "include/mimalloc/internal.h"
           _mi_os_protect(void* addr, size_t size);

# 131 "include/mimalloc/internal.h" 3 4
_Bool 
# 131 "include/mimalloc/internal.h"
           _mi_os_unprotect(void* addr, size_t size);

# 132 "include/mimalloc/internal.h" 3 4
_Bool 
# 132 "include/mimalloc/internal.h"
           _mi_os_purge(void* p, size_t size);

# 133 "include/mimalloc/internal.h" 3 4
_Bool 
# 133 "include/mimalloc/internal.h"
           _mi_os_purge_ex(void* p, size_t size, 
# 133 "include/mimalloc/internal.h" 3 4
                                                 _Bool 
# 133 "include/mimalloc/internal.h"
                                                      allow_reset, size_t stat_size);

void* _mi_os_alloc_aligned(size_t size, size_t alignment, 
# 135 "include/mimalloc/internal.h" 3 4
                                                               _Bool 
# 135 "include/mimalloc/internal.h"
                                                                    commit, 
# 135 "include/mimalloc/internal.h" 3 4
                                                                            _Bool 
# 135 "include/mimalloc/internal.h"
                                                                                 allow_large, mi_memid_t* memid);
void* _mi_os_alloc_aligned_at_offset(size_t size, size_t alignment, size_t align_offset, 
# 136 "include/mimalloc/internal.h" 3 4
                                                                                              _Bool 
# 136 "include/mimalloc/internal.h"
                                                                                                   commit, 
# 136 "include/mimalloc/internal.h" 3 4
                                                                                                           _Bool 
# 136 "include/mimalloc/internal.h"
                                                                                                                allow_large, mi_memid_t* memid);

void* _mi_os_get_aligned_hint(size_t try_alignment, size_t size);

# 139 "include/mimalloc/internal.h" 3 4
_Bool 
# 139 "include/mimalloc/internal.h"
           _mi_os_use_large_page(size_t size, size_t alignment);
size_t _mi_os_large_page_size(void);

void* _mi_os_alloc_huge_os_pages(size_t pages, int numa_node, mi_msecs_t max_secs, size_t* pages_reserved, size_t* psize, mi_memid_t* memid);


mi_arena_id_t _mi_arena_id_none(void);
void _mi_arena_free(void* p, size_t size, size_t still_committed_size, mi_memid_t memid);
void* _mi_arena_alloc(size_t size, 
# 147 "include/mimalloc/internal.h" 3 4
                                        _Bool 
# 147 "include/mimalloc/internal.h"
                                             commit, 
# 147 "include/mimalloc/internal.h" 3 4
                                                     _Bool 
# 147 "include/mimalloc/internal.h"
                                                          allow_large, mi_arena_id_t req_arena_id, mi_memid_t* memid);
void* _mi_arena_alloc_aligned(size_t size, size_t alignment, size_t align_offset, 
# 148 "include/mimalloc/internal.h" 3 4
                                                                                       _Bool 
# 148 "include/mimalloc/internal.h"
                                                                                            commit, 
# 148 "include/mimalloc/internal.h" 3 4
                                                                                                    _Bool 
# 148 "include/mimalloc/internal.h"
                                                                                                         allow_large, mi_arena_id_t req_arena_id, mi_memid_t* memid);

# 149 "include/mimalloc/internal.h" 3 4
_Bool 
# 149 "include/mimalloc/internal.h"
           _mi_arena_memid_is_suitable(mi_memid_t memid, mi_arena_id_t request_arena_id);

# 150 "include/mimalloc/internal.h" 3 4
_Bool 
# 150 "include/mimalloc/internal.h"
           _mi_arena_contains(const void* p);
void _mi_arenas_collect(
# 151 "include/mimalloc/internal.h" 3 4
                              _Bool 
# 151 "include/mimalloc/internal.h"
                                   force_purge);
void _mi_arena_unsafe_destroy_all(void);


# 154 "include/mimalloc/internal.h" 3 4
_Bool 
# 154 "include/mimalloc/internal.h"
           _mi_arena_segment_clear_abandoned(mi_segment_t* segment);
void _mi_arena_segment_mark_abandoned(mi_segment_t* segment);

void* _mi_arena_meta_zalloc(size_t size, mi_memid_t* memid);
void _mi_arena_meta_free(void* p, mi_memid_t memid, size_t size);

typedef struct mi_arena_field_cursor_s {
  size_t os_list_count;
  size_t start;
  size_t end;
  size_t bitmap_idx;
  mi_subproc_t* subproc;
  
# 166 "include/mimalloc/internal.h" 3 4
 _Bool 
# 166 "include/mimalloc/internal.h"
                visit_all;
  
# 167 "include/mimalloc/internal.h" 3 4
 _Bool 
# 167 "include/mimalloc/internal.h"
                hold_visit_lock;
} mi_arena_field_cursor_t;
void _mi_arena_field_cursor_init(mi_heap_t* heap, mi_subproc_t* subproc, 
# 169 "include/mimalloc/internal.h" 3 4
                                                                                 _Bool 
# 169 "include/mimalloc/internal.h"
                                                                                      visit_all, mi_arena_field_cursor_t* current);
mi_segment_t* _mi_arena_segment_clear_abandoned_next(mi_arena_field_cursor_t* previous);
void _mi_arena_field_cursor_done(mi_arena_field_cursor_t* current);


void _mi_segment_map_allocated_at(const mi_segment_t* segment);
void _mi_segment_map_freed_at(const mi_segment_t* segment);
void _mi_segment_map_unsafe_destroy(void);


mi_page_t* _mi_segment_page_alloc(mi_heap_t* heap, size_t block_size, size_t page_alignment, mi_segments_tld_t* tld);
void _mi_segment_page_free(mi_page_t* page, 
# 180 "include/mimalloc/internal.h" 3 4
                                                 _Bool 
# 180 "include/mimalloc/internal.h"
                                                      force, mi_segments_tld_t* tld);
void _mi_segment_page_abandon(mi_page_t* page, mi_segments_tld_t* tld);

# 182 "include/mimalloc/internal.h" 3 4
_Bool 
# 182 "include/mimalloc/internal.h"
          _mi_segment_try_reclaim_abandoned( mi_heap_t* heap, 
# 182 "include/mimalloc/internal.h" 3 4
                                                              _Bool 
# 182 "include/mimalloc/internal.h"
                                                                   try_all, mi_segments_tld_t* tld);
void _mi_segment_collect(mi_segment_t* segment, 
# 183 "include/mimalloc/internal.h" 3 4
                                                     _Bool 
# 183 "include/mimalloc/internal.h"
                                                          force);




void _mi_segment_huge_page_reset(mi_segment_t* segment, mi_page_t* page, mi_block_t* block);


uint8_t* _mi_segment_page_start(const mi_segment_t* segment, const mi_page_t* page, size_t* page_size);
void _mi_abandoned_reclaim_all(mi_heap_t* heap, mi_segments_tld_t* tld);
void _mi_abandoned_collect(mi_heap_t* heap, 
# 193 "include/mimalloc/internal.h" 3 4
                                                 _Bool 
# 193 "include/mimalloc/internal.h"
                                                      force, mi_segments_tld_t* tld);

# 194 "include/mimalloc/internal.h" 3 4
_Bool 
# 194 "include/mimalloc/internal.h"
          _mi_segment_attempt_reclaim(mi_heap_t* heap, mi_segment_t* segment);

# 195 "include/mimalloc/internal.h" 3 4
_Bool 
# 195 "include/mimalloc/internal.h"
          _mi_segment_visit_blocks(mi_segment_t* segment, int heap_tag, 
# 195 "include/mimalloc/internal.h" 3 4
                                                                        _Bool 
# 195 "include/mimalloc/internal.h"
                                                                             visit_blocks, mi_block_visit_fun* visitor, void* arg);


void* _mi_malloc_generic(mi_heap_t* heap, size_t size, 
# 198 "include/mimalloc/internal.h" 3 4
                                                            _Bool 
# 198 "include/mimalloc/internal.h"
                                                                 zero, size_t huge_alignment) __attribute__((malloc));

void _mi_page_retire(mi_page_t* page) ;
void _mi_page_unfull(mi_page_t* page);
void _mi_page_free(mi_page_t* page, mi_page_queue_t* pq, 
# 202 "include/mimalloc/internal.h" 3 4
                                                               _Bool 
# 202 "include/mimalloc/internal.h"
                                                                    force);
void _mi_page_abandon(mi_page_t* page, mi_page_queue_t* pq);
void _mi_page_force_abandon(mi_page_t* page);

void _mi_heap_delayed_free_all(mi_heap_t* heap);

# 207 "include/mimalloc/internal.h" 3 4
_Bool 
# 207 "include/mimalloc/internal.h"
           _mi_heap_delayed_free_partial(mi_heap_t* heap);
void _mi_heap_collect_retired(mi_heap_t* heap, 
# 208 "include/mimalloc/internal.h" 3 4
                                                     _Bool 
# 208 "include/mimalloc/internal.h"
                                                          force);

void _mi_page_use_delayed_free(mi_page_t* page, mi_delayed_t delay, 
# 210 "include/mimalloc/internal.h" 3 4
                                                                          _Bool 
# 210 "include/mimalloc/internal.h"
                                                                               override_never);

# 211 "include/mimalloc/internal.h" 3 4
_Bool 
# 211 "include/mimalloc/internal.h"
           _mi_page_try_use_delayed_free(mi_page_t* page, mi_delayed_t delay, 
# 211 "include/mimalloc/internal.h" 3 4
                                                                              _Bool 
# 211 "include/mimalloc/internal.h"
                                                                                   override_never);
size_t _mi_page_queue_append(mi_heap_t* heap, mi_page_queue_t* pq, mi_page_queue_t* append);
void _mi_deferred_free(mi_heap_t* heap, 
# 213 "include/mimalloc/internal.h" 3 4
                                              _Bool 
# 213 "include/mimalloc/internal.h"
                                                   force);

void _mi_page_free_collect(mi_page_t* page,
# 215 "include/mimalloc/internal.h" 3 4
                                                 _Bool 
# 215 "include/mimalloc/internal.h"
                                                      force);
void _mi_page_reclaim(mi_heap_t* heap, mi_page_t* page);

size_t _mi_bin_size(uint8_t bin);
uint8_t _mi_bin(size_t size);


void _mi_heap_init(mi_heap_t* heap, mi_tld_t* tld, mi_arena_id_t arena_id, 
# 222 "include/mimalloc/internal.h" 3 4
                                                                                 _Bool 
# 222 "include/mimalloc/internal.h"
                                                                                      noreclaim, uint8_t tag);
void _mi_heap_destroy_pages(mi_heap_t* heap);
void _mi_heap_collect_abandon(mi_heap_t* heap);
void _mi_heap_set_default_direct(mi_heap_t* heap);

# 226 "include/mimalloc/internal.h" 3 4
_Bool 
# 226 "include/mimalloc/internal.h"
           _mi_heap_memid_is_suitable(mi_heap_t* heap, mi_memid_t memid);
void _mi_heap_unsafe_destroy_all(mi_heap_t* heap);
mi_heap_t* _mi_heap_by_tag(mi_heap_t* heap, uint8_t tag);
void _mi_heap_area_init(mi_heap_area_t* area, mi_page_t* page);

# 230 "include/mimalloc/internal.h" 3 4
_Bool 
# 230 "include/mimalloc/internal.h"
           _mi_heap_area_visit_blocks(const mi_heap_area_t* area, mi_page_t* page, mi_block_visit_fun* visitor, void* arg);


void _mi_stats_done(mi_stats_t* stats);
mi_msecs_t _mi_clock_now(void);
mi_msecs_t _mi_clock_end(mi_msecs_t start);
mi_msecs_t _mi_clock_start(void);


void* _mi_page_malloc_zero(mi_heap_t* heap, mi_page_t* page, size_t size, 
# 239 "include/mimalloc/internal.h" 3 4
                                                                               _Bool 
# 239 "include/mimalloc/internal.h"
                                                                                    zero) ;
void* _mi_page_malloc(mi_heap_t* heap, mi_page_t* page, size_t size) ;
void* _mi_page_malloc_zeroed(mi_heap_t* heap, mi_page_t* page, size_t size) ;
void* _mi_heap_malloc_zero(mi_heap_t* heap, size_t size, 
# 242 "include/mimalloc/internal.h" 3 4
                                                              _Bool 
# 242 "include/mimalloc/internal.h"
                                                                   zero) ;
void* _mi_heap_malloc_zero_ex(mi_heap_t* heap, size_t size, 
# 243 "include/mimalloc/internal.h" 3 4
                                                                 _Bool 
# 243 "include/mimalloc/internal.h"
                                                                      zero, size_t huge_alignment) ;
void* _mi_heap_realloc_zero(mi_heap_t* heap, void* p, size_t newsize, 
# 244 "include/mimalloc/internal.h" 3 4
                                                                           _Bool 
# 244 "include/mimalloc/internal.h"
                                                                                zero) ;
mi_block_t* _mi_page_ptr_unalign(const mi_page_t* page, const void* p);

# 246 "include/mimalloc/internal.h" 3 4
_Bool 
# 246 "include/mimalloc/internal.h"
           _mi_free_delayed_block(mi_block_t* block);
void _mi_free_generic(mi_segment_t* segment, mi_page_t* page, 
# 247 "include/mimalloc/internal.h" 3 4
                                                                    _Bool 
# 247 "include/mimalloc/internal.h"
                                                                         is_local, void* p) ;
void _mi_padding_shrink(const mi_page_t* page, const mi_block_t* block, const size_t min_size);
# 281 "include/mimalloc/internal.h"
# 1 "/usr/include/errno.h" 1 3 4
# 28 "/usr/include/errno.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/errno.h" 1 3 4
# 26 "/usr/include/x86_64-linux-gnu/bits/errno.h" 3 4
# 1 "/usr/include/linux/errno.h" 1 3 4
# 1 "/usr/lib/linux/uapi/x86/asm/errno.h" 1 3 4
# 1 "/usr/include/asm-generic/errno.h" 1 3 4




# 1 "/usr/include/asm-generic/errno-base.h" 1 3 4
# 6 "/usr/include/asm-generic/errno.h" 2 3 4
# 2 "/usr/lib/linux/uapi/x86/asm/errno.h" 2 3 4
# 2 "/usr/include/linux/errno.h" 2 3 4
# 27 "/usr/include/x86_64-linux-gnu/bits/errno.h" 2 3 4
# 29 "/usr/include/errno.h" 2 3 4









# 37 "/usr/include/errno.h" 3 4
extern int *__errno_location (void) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__const__));
# 52 "/usr/include/errno.h" 3 4

# 282 "include/mimalloc/internal.h" 2
# 318 "include/mimalloc/internal.h"
# 1 "/usr/include/string.h" 1 3 4
# 26 "/usr/include/string.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/libc-header-start.h" 1 3 4
# 27 "/usr/include/string.h" 2 3 4






# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 1 3 4
# 34 "/usr/include/string.h" 2 3 4
# 43 "/usr/include/string.h" 3 4
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






extern int strcoll_l (const char *__s1, const char *__s2, locale_t __l)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2, 3)));


extern size_t strxfrm_l (char *__dest, const char *__src, size_t __n,
    locale_t __l) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 4)))
     __attribute__ ((__access__ (__write_only__, 1, 3)));





extern char *strdup (const char *__s)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) __attribute__ ((__nonnull__ (1)));






extern char *strndup (const char *__string, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) __attribute__ ((__nonnull__ (1)));
# 246 "/usr/include/string.h" 3 4
extern char *strchr (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
# 273 "/usr/include/string.h" 3 4
extern char *strrchr (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
# 286 "/usr/include/string.h" 3 4
extern char *strchrnul (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));





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

extern char *strtok_r (char *__restrict __s, const char *__restrict __delim,
         char **__restrict __save_ptr)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (2, 3)));
# 380 "/usr/include/string.h" 3 4
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
# 432 "/usr/include/string.h" 3 4
extern int strerror_r (int __errnum, char *__buf, size_t __buflen) __asm__ ("" "__xpg_strerror_r") __attribute__ ((__nothrow__ , __leaf__))

                        __attribute__ ((__nonnull__ (2)))
    __attribute__ ((__access__ (__write_only__, 2, 3)));
# 458 "/usr/include/string.h" 3 4
extern char *strerror_l (int __errnum, locale_t __l) __attribute__ ((__nothrow__ , __leaf__));



# 1 "/usr/include/strings.h" 1 3 4
# 23 "/usr/include/strings.h" 3 4
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 1 3 4
# 24 "/usr/include/strings.h" 2 3 4










extern int bcmp (const void *__s1, const void *__s2, size_t __n)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1, 2)));


extern void bcopy (const void *__src, void *__dest, size_t __n)
  __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));


extern void bzero (void *__s, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 68 "/usr/include/strings.h" 3 4
extern char *index (const char *__s, int __c)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__pure__)) __attribute__ ((__nonnull__ (1)));
# 96 "/usr/include/strings.h" 3 4
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



# 463 "/usr/include/string.h" 2 3 4



extern void explicit_bzero (void *__s, size_t __n) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)))
    __attribute__ ((__access__ (__write_only__, 1, 2)));



extern char *strsep (char **__restrict __stringp,
       const char *__restrict __delim)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1, 2)));




extern char *strsignal (int __sig) __attribute__ ((__nothrow__ , __leaf__));
# 489 "/usr/include/string.h" 3 4
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
# 552 "/usr/include/string.h" 3 4

# 319 "include/mimalloc/internal.h" 2





# 323 "include/mimalloc/internal.h"
static inline 
# 323 "include/mimalloc/internal.h" 3 4
             _Bool 
# 323 "include/mimalloc/internal.h"
                  _mi_is_power_of_two(uintptr_t x) {
  return ((x & (x - 1)) == 0);
}


static inline 
# 328 "include/mimalloc/internal.h" 3 4
             _Bool 
# 328 "include/mimalloc/internal.h"
                  _mi_is_aligned(void* p, size_t alignment) {
  ;
  return (((uintptr_t)p % alignment) == 0);
}


static inline uintptr_t _mi_align_up(uintptr_t sz, size_t alignment) {
  ;
  uintptr_t mask = alignment - 1;
  if ((alignment & mask) == 0) {
    return ((sz + mask) & ~mask);
  }
  else {
    return (((sz + mask)/alignment)*alignment);
  }
}


static inline uintptr_t _mi_align_down(uintptr_t sz, size_t alignment) {
  ;
  uintptr_t mask = alignment - 1;
  if ((alignment & mask) == 0) {
    return (sz & ~mask);
  }
  else {
    return ((sz / alignment) * alignment);
  }
}


static inline void* mi_align_up_ptr(void* p, size_t alignment) {
  return (void*)_mi_align_up((uintptr_t)p, alignment);
}


static inline void* mi_align_down_ptr(void* p, size_t alignment) {
  return (void*)_mi_align_down((uintptr_t)p, alignment);
}



static inline uintptr_t _mi_divide_up(uintptr_t size, size_t divider) {
  ;
  return (divider == 0 ? size : ((size + divider - 1) / divider));
}



static inline size_t _mi_clamp(size_t sz, size_t min, size_t max) {
  if (sz < min) return min;
  else if (sz > max) return max;
  else return sz;
}


static inline 
# 383 "include/mimalloc/internal.h" 3 4
             _Bool 
# 383 "include/mimalloc/internal.h"
                  mi_mem_is_zero(const void* p, size_t size) {
  for (size_t i = 0; i < size; i++) {
    if (((uint8_t*)p)[i] != 0) return 
# 385 "include/mimalloc/internal.h" 3 4
                                     0
# 385 "include/mimalloc/internal.h"
                                          ;
  }
  return 
# 387 "include/mimalloc/internal.h" 3 4
        1
# 387 "include/mimalloc/internal.h"
            ;
}




static inline size_t _mi_wsize_from_size(size_t size) {
  ;
  return (size + sizeof(uintptr_t) - 1) / sizeof(uintptr_t);
}



# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/limits.h" 1 3 4
# 34 "/usr/lib/gcc/x86_64-linux-gnu/14/include/limits.h" 3 4
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/syslimits.h" 1 3 4






# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/limits.h" 1 3 4
# 210 "/usr/lib/gcc/x86_64-linux-gnu/14/include/limits.h" 3 4
# 1 "/usr/include/limits.h" 1 3 4
# 26 "/usr/include/limits.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/libc-header-start.h" 1 3 4
# 27 "/usr/include/limits.h" 2 3 4
# 195 "/usr/include/limits.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/posix1_lim.h" 1 3 4
# 27 "/usr/include/x86_64-linux-gnu/bits/posix1_lim.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/wordsize.h" 1 3 4
# 28 "/usr/include/x86_64-linux-gnu/bits/posix1_lim.h" 2 3 4
# 161 "/usr/include/x86_64-linux-gnu/bits/posix1_lim.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/local_lim.h" 1 3 4
# 38 "/usr/include/x86_64-linux-gnu/bits/local_lim.h" 3 4
# 1 "/usr/include/linux/limits.h" 1 3 4
# 39 "/usr/include/x86_64-linux-gnu/bits/local_lim.h" 2 3 4
# 162 "/usr/include/x86_64-linux-gnu/bits/posix1_lim.h" 2 3 4
# 196 "/usr/include/limits.h" 2 3 4



# 1 "/usr/include/x86_64-linux-gnu/bits/posix2_lim.h" 1 3 4
# 200 "/usr/include/limits.h" 2 3 4
# 211 "/usr/lib/gcc/x86_64-linux-gnu/14/include/limits.h" 2 3 4
# 8 "/usr/lib/gcc/x86_64-linux-gnu/14/include/syslimits.h" 2 3 4
# 35 "/usr/lib/gcc/x86_64-linux-gnu/14/include/limits.h" 2 3 4
# 401 "include/mimalloc/internal.h" 2



static inline 
# 404 "include/mimalloc/internal.h" 3 4
             _Bool 
# 404 "include/mimalloc/internal.h"
                  mi_mul_overflow(size_t count, size_t size, size_t* total) {

    return __builtin_umull_overflow(count, size, (unsigned long *)total);





}
# 423 "include/mimalloc/internal.h"
static inline 
# 423 "include/mimalloc/internal.h" 3 4
             _Bool 
# 423 "include/mimalloc/internal.h"
                  mi_count_size_overflow(size_t count, size_t size, size_t* total) {
  if (count==1) {
    *total = size;
    return 
# 426 "include/mimalloc/internal.h" 3 4
          0
# 426 "include/mimalloc/internal.h"
               ;
  }
  else if (__builtin_expect(!!(mi_mul_overflow(count, size, total)),
# 428 "include/mimalloc/internal.h" 3 4
         0
# 428 "include/mimalloc/internal.h"
         )) {



    *total = 
# 432 "include/mimalloc/internal.h" 3 4
            (18446744073709551615UL)
# 432 "include/mimalloc/internal.h"
                    ;
    return 
# 433 "include/mimalloc/internal.h" 3 4
          1
# 433 "include/mimalloc/internal.h"
              ;
  }
  else return 
# 435 "include/mimalloc/internal.h" 3 4
             0
# 435 "include/mimalloc/internal.h"
                  ;
}






extern __attribute__((visibility("hidden"))) const mi_heap_t _mi_heap_empty;

static inline 
# 445 "include/mimalloc/internal.h" 3 4
             _Bool 
# 445 "include/mimalloc/internal.h"
                  mi_heap_is_backing(const mi_heap_t* heap) {
  return (heap->tld->heap_backing == heap);
}

static inline 
# 449 "include/mimalloc/internal.h" 3 4
             _Bool 
# 449 "include/mimalloc/internal.h"
                  mi_heap_is_initialized(mi_heap_t* heap) {
  ;
  return (heap != 
# 451 "include/mimalloc/internal.h" 3 4
                 ((void *)0) 
# 451 "include/mimalloc/internal.h"
                      && heap != &_mi_heap_empty);
}

static inline uintptr_t _mi_ptr_cookie(const void* p) {
  extern __attribute__((visibility("hidden"))) mi_heap_t _mi_heap_main;
  ;
  return ((uintptr_t)p ^ _mi_heap_main.cookie);
}





static inline mi_page_t* _mi_heap_get_free_small_page(mi_heap_t* heap, size_t size) {
  ;
  const size_t idx = _mi_wsize_from_size(size);
  ;
  return heap->pages_free_direct[idx];
}






static inline mi_segment_t* _mi_ptr_segment(const void* p) {
  mi_segment_t* const segment = (mi_segment_t*)(((uintptr_t)p - 1) & ~((uintptr_t)((1ULL<<( 9 + (13 + (3)))) - 1)));



  return ((intptr_t)segment <= 0 ? 
# 481 "include/mimalloc/internal.h" 3 4
                                  ((void *)0) 
# 481 "include/mimalloc/internal.h"
                                       : segment);

}

static inline mi_page_t* mi_slice_to_page(mi_slice_t* s) {
  ;
  return (mi_page_t*)(s);
}

static inline mi_slice_t* mi_page_to_slice(mi_page_t* p) {
  ;
  return (mi_slice_t*)(p);
}


static inline mi_segment_t* _mi_page_segment(const mi_page_t* page) {
  ;
  mi_segment_t* segment = _mi_ptr_segment(page);
  ;
  return segment;
}

static inline mi_slice_t* mi_slice_first(const mi_slice_t* slice) {
  mi_slice_t* start = (mi_slice_t*)((uint8_t*)slice - slice->slice_offset);
  ;
  ;
  ;
  return start;
}


static inline mi_page_t* _mi_segment_page_of(const mi_segment_t* segment, const void* p) {
  ;
  ptrdiff_t diff = (uint8_t*)p - (uint8_t*)segment;
  ;
  size_t idx = (size_t)diff >> (13 + (3));
  ;
  mi_slice_t* slice0 = (mi_slice_t*)&segment->slices[idx];
  mi_slice_t* slice = mi_slice_first(slice0);
  ;
  ;
  return mi_slice_to_page(slice);
}


static inline uint8_t* mi_page_start(const mi_page_t* page) {
  ;
  ;
  return page->page_start;
}


static inline mi_page_t* _mi_ptr_page(void* p) {
  ;
  return _mi_segment_page_of(_mi_ptr_segment(p), p);
}


static inline size_t mi_page_block_size(const mi_page_t* page) {
  ;
  return page->block_size;
}

static inline 
# 544 "include/mimalloc/internal.h" 3 4
             _Bool 
# 544 "include/mimalloc/internal.h"
                  mi_page_is_huge(const mi_page_t* page) {
 
                                                                                         ;
  return page->is_huge;
}



static inline size_t mi_page_usable_block_size(const mi_page_t* page) {
  return mi_page_block_size(page) - 0;
}


static inline size_t mi_segment_size(mi_segment_t* segment) {
  return segment->segment_slices * (1ULL<< (13 + (3)));
}

static inline uint8_t* mi_segment_end(mi_segment_t* segment) {
  return (uint8_t*)segment + mi_segment_size(segment);
}


static inline mi_block_t* mi_page_thread_free(const mi_page_t* page) {
  return (mi_block_t*)(
# 567 "include/mimalloc/internal.h" 3 4
                      __extension__ ({ __auto_type __atomic_load_ptr = (
# 567 "include/mimalloc/internal.h"
                      &((mi_page_t*)page)->xthread_free
# 567 "include/mimalloc/internal.h" 3 4
                      ); __typeof__ ((void)0, *__atomic_load_ptr) __atomic_load_tmp; __atomic_load (__atomic_load_ptr, &__atomic_load_tmp, (
# 567 "include/mimalloc/internal.h"
                      memory_order_relaxed
# 567 "include/mimalloc/internal.h" 3 4
                      )); __atomic_load_tmp; }) 
# 567 "include/mimalloc/internal.h"
                                                                                & ~3);
}

static inline mi_delayed_t mi_page_thread_free_flag(const mi_page_t* page) {
  return (mi_delayed_t)(
# 571 "include/mimalloc/internal.h" 3 4
                       __extension__ ({ __auto_type __atomic_load_ptr = (
# 571 "include/mimalloc/internal.h"
                       &((mi_page_t*)page)->xthread_free
# 571 "include/mimalloc/internal.h" 3 4
                       ); __typeof__ ((void)0, *__atomic_load_ptr) __atomic_load_tmp; __atomic_load (__atomic_load_ptr, &__atomic_load_tmp, (
# 571 "include/mimalloc/internal.h"
                       memory_order_relaxed
# 571 "include/mimalloc/internal.h" 3 4
                       )); __atomic_load_tmp; }) 
# 571 "include/mimalloc/internal.h"
                                                                                 & 3);
}


static inline mi_heap_t* mi_page_heap(const mi_page_t* page) {
  return (mi_heap_t*)(
# 576 "include/mimalloc/internal.h" 3 4
                     __extension__ ({ __auto_type __atomic_load_ptr = (
# 576 "include/mimalloc/internal.h"
                     &((mi_page_t*)page)->xheap
# 576 "include/mimalloc/internal.h" 3 4
                     ); __typeof__ ((void)0, *__atomic_load_ptr) __atomic_load_tmp; __atomic_load (__atomic_load_ptr, &__atomic_load_tmp, (
# 576 "include/mimalloc/internal.h"
                     memory_order_relaxed
# 576 "include/mimalloc/internal.h" 3 4
                     )); __atomic_load_tmp; })
# 576 "include/mimalloc/internal.h"
                                                                       );
}

static inline void mi_page_set_heap(mi_page_t* page, mi_heap_t* heap) {
  ;
  
# 581 "include/mimalloc/internal.h" 3 4
 __extension__ ({ __auto_type __atomic_store_ptr = (
# 581 "include/mimalloc/internal.h"
 &page->xheap
# 581 "include/mimalloc/internal.h" 3 4
 ); __typeof__ ((void)0, *__atomic_store_ptr) __atomic_store_tmp = (
# 581 "include/mimalloc/internal.h"
 (uintptr_t)heap
# 581 "include/mimalloc/internal.h" 3 4
 ); __atomic_store (__atomic_store_ptr, &__atomic_store_tmp, (
# 581 "include/mimalloc/internal.h"
 memory_order_release
# 581 "include/mimalloc/internal.h" 3 4
 )); })
# 581 "include/mimalloc/internal.h"
                                                      ;
  if (heap != 
# 582 "include/mimalloc/internal.h" 3 4
             ((void *)0)
# 582 "include/mimalloc/internal.h"
                 ) { page->heap_tag = heap->tag; }
}


static inline mi_block_t* mi_tf_block(mi_thread_free_t tf) {
  return (mi_block_t*)(tf & ~0x03);
}
static inline mi_delayed_t mi_tf_delayed(mi_thread_free_t tf) {
  return (mi_delayed_t)(tf & 0x03);
}
static inline mi_thread_free_t mi_tf_make(mi_block_t* block, mi_delayed_t delayed) {
  return (mi_thread_free_t)((uintptr_t)block | (uintptr_t)delayed);
}
static inline mi_thread_free_t mi_tf_set_delayed(mi_thread_free_t tf, mi_delayed_t delayed) {
  return mi_tf_make(mi_tf_block(tf),delayed);
}
static inline mi_thread_free_t mi_tf_set_block(mi_thread_free_t tf, mi_block_t* block) {
  return mi_tf_make(block, mi_tf_delayed(tf));
}



static inline 
# 604 "include/mimalloc/internal.h" 3 4
             _Bool 
# 604 "include/mimalloc/internal.h"
                  mi_page_all_free(const mi_page_t* page) {
  ;
  return (page->used == 0);
}


static inline 
# 610 "include/mimalloc/internal.h" 3 4
             _Bool 
# 610 "include/mimalloc/internal.h"
                  mi_page_has_any_available(const mi_page_t* page) {
  ;
  return (page->used < page->reserved || (mi_page_thread_free(page) != 
# 612 "include/mimalloc/internal.h" 3 4
                                                                      ((void *)0)
# 612 "include/mimalloc/internal.h"
                                                                          ));
}


static inline 
# 616 "include/mimalloc/internal.h" 3 4
             _Bool 
# 616 "include/mimalloc/internal.h"
                  mi_page_immediate_available(const mi_page_t* page) {
  ;
  return (page->free != 
# 618 "include/mimalloc/internal.h" 3 4
                       ((void *)0)
# 618 "include/mimalloc/internal.h"
                           );
}


static inline 
# 622 "include/mimalloc/internal.h" 3 4
             _Bool 
# 622 "include/mimalloc/internal.h"
                  mi_page_is_mostly_used(const mi_page_t* page) {
  if (page==
# 623 "include/mimalloc/internal.h" 3 4
           ((void *)0)
# 623 "include/mimalloc/internal.h"
               ) return 
# 623 "include/mimalloc/internal.h" 3 4
                        1
# 623 "include/mimalloc/internal.h"
                            ;
  uint16_t frac = page->reserved / 8U;
  return (page->reserved - page->used <= frac);
}

static inline mi_page_queue_t* mi_page_queue(const mi_heap_t* heap, size_t size) {
  return &((mi_heap_t*)heap)->pages[_mi_bin(size)];
}






static inline 
# 637 "include/mimalloc/internal.h" 3 4
             _Bool 
# 637 "include/mimalloc/internal.h"
                  mi_page_is_in_full(const mi_page_t* page) {
  return page->flags.x.in_full;
}

static inline void mi_page_set_in_full(mi_page_t* page, 
# 641 "include/mimalloc/internal.h" 3 4
                                                       _Bool 
# 641 "include/mimalloc/internal.h"
                                                            in_full) {
  page->flags.x.in_full = in_full;
}

static inline 
# 645 "include/mimalloc/internal.h" 3 4
             _Bool 
# 645 "include/mimalloc/internal.h"
                  mi_page_has_aligned(const mi_page_t* page) {
  return page->flags.x.has_aligned;
}

static inline void mi_page_set_has_aligned(mi_page_t* page, 
# 649 "include/mimalloc/internal.h" 3 4
                                                           _Bool 
# 649 "include/mimalloc/internal.h"
                                                                has_aligned) {
  page->flags.x.has_aligned = has_aligned;
}
# 712 "include/mimalloc/internal.h"
static inline 
# 712 "include/mimalloc/internal.h" 3 4
             _Bool 
# 712 "include/mimalloc/internal.h"
                  mi_is_in_same_segment(const void* p, const void* q) {
  return (_mi_ptr_segment(p) == _mi_ptr_segment(q));
}

static inline 
# 716 "include/mimalloc/internal.h" 3 4
             _Bool 
# 716 "include/mimalloc/internal.h"
                  mi_is_in_same_page(const void* p, const void* q) {
  mi_segment_t* segment = _mi_ptr_segment(p);
  if (_mi_ptr_segment(q) != segment) return 
# 718 "include/mimalloc/internal.h" 3 4
                                           0
# 718 "include/mimalloc/internal.h"
                                                ;

  mi_page_t* page = _mi_segment_page_of(segment, p);
  size_t psize;
  uint8_t* start = _mi_segment_page_start(segment, page, &psize);
  return (start <= (uint8_t*)q && (uint8_t*)q < start + psize);
}

static inline uintptr_t mi_rotl(uintptr_t x, uintptr_t shift) {
  shift %= ((1<<(3))*8);
  return (shift==0 ? x : ((x << shift) | (x >> (((1<<(3))*8) - shift))));
}
static inline uintptr_t mi_rotr(uintptr_t x, uintptr_t shift) {
  shift %= ((1<<(3))*8);
  return (shift==0 ? x : ((x >> shift) | (x << (((1<<(3))*8) - shift))));
}

static inline void* mi_ptr_decode(const void* null, const mi_encoded_t x, const uintptr_t* keys) {
  void* p = (void*)(mi_rotr(x - keys[0], keys[0]) ^ keys[1]);
  return (p==null ? 
# 737 "include/mimalloc/internal.h" 3 4
                   ((void *)0) 
# 737 "include/mimalloc/internal.h"
                        : p);
}

static inline mi_encoded_t mi_ptr_encode(const void* null, const void* p, const uintptr_t* keys) {
  uintptr_t x = (uintptr_t)(p==
# 741 "include/mimalloc/internal.h" 3 4
                              ((void *)0) 
# 741 "include/mimalloc/internal.h"
                                   ? null : p);
  return mi_rotl(x ^ keys[1], keys[0]) + keys[0];
}

static inline uint32_t mi_ptr_encode_canary(const void* null, const void* p, const uintptr_t* keys) {
  const uint32_t x = (uint32_t)(mi_ptr_encode(null,p,keys));




  return (x & 0xFFFFFF00);

}

static inline mi_block_t* mi_block_nextx( const void* null, const mi_block_t* block, const uintptr_t* keys ) {
  ;
  mi_block_t* next;



  (void)(keys); (void)(null);
  next = (mi_block_t*)block->next;

  ;
  return next;
}

static inline void mi_block_set_nextx(const void* null, mi_block_t* block, const mi_block_t* next, const uintptr_t* keys) {
  ;



  (void)(keys); (void)(null);
  block->next = (mi_encoded_t)next;

  ;
}

static inline mi_block_t* mi_block_next(const mi_page_t* page, const mi_block_t* block) {
# 790 "include/mimalloc/internal.h"
  (void)(page);
  return mi_block_nextx(page,block,
# 791 "include/mimalloc/internal.h" 3 4
                                  ((void *)0)
# 791 "include/mimalloc/internal.h"
                                      );

}

static inline void mi_block_set_next(const mi_page_t* page, mi_block_t* block, const mi_block_t* next) {



  (void)(page);
  mi_block_set_nextx(page,block,next,
# 800 "include/mimalloc/internal.h" 3 4
                                    ((void *)0)
# 800 "include/mimalloc/internal.h"
                                        );

}






static inline void mi_commit_mask_create_empty(mi_commit_mask_t* cm) {
  for (size_t i = 0; i < (((1ULL<<( 9 + (13 + (3)))) / ((1ULL<< (13 + (3))))) / ((1<<(3))*8)); i++) {
    cm->mask[i] = 0;
  }
}

static inline void mi_commit_mask_create_full(mi_commit_mask_t* cm) {
  for (size_t i = 0; i < (((1ULL<<( 9 + (13 + (3)))) / ((1ULL<< (13 + (3))))) / ((1<<(3))*8)); i++) {
    cm->mask[i] = ~((size_t)0);
  }
}

static inline 
# 821 "include/mimalloc/internal.h" 3 4
             _Bool 
# 821 "include/mimalloc/internal.h"
                  mi_commit_mask_is_empty(const mi_commit_mask_t* cm) {
  for (size_t i = 0; i < (((1ULL<<( 9 + (13 + (3)))) / ((1ULL<< (13 + (3))))) / ((1<<(3))*8)); i++) {
    if (cm->mask[i] != 0) return 
# 823 "include/mimalloc/internal.h" 3 4
                                0
# 823 "include/mimalloc/internal.h"
                                     ;
  }
  return 
# 825 "include/mimalloc/internal.h" 3 4
        1
# 825 "include/mimalloc/internal.h"
            ;
}

static inline 
# 828 "include/mimalloc/internal.h" 3 4
             _Bool 
# 828 "include/mimalloc/internal.h"
                  mi_commit_mask_is_full(const mi_commit_mask_t* cm) {
  for (size_t i = 0; i < (((1ULL<<( 9 + (13 + (3)))) / ((1ULL<< (13 + (3))))) / ((1<<(3))*8)); i++) {
    if (cm->mask[i] != ~((size_t)0)) return 
# 830 "include/mimalloc/internal.h" 3 4
                                           0
# 830 "include/mimalloc/internal.h"
                                                ;
  }
  return 
# 832 "include/mimalloc/internal.h" 3 4
        1
# 832 "include/mimalloc/internal.h"
            ;
}


size_t _mi_commit_mask_committed_size(const mi_commit_mask_t* cm, size_t total);
size_t _mi_commit_mask_next_run(const mi_commit_mask_t* cm, size_t* idx);
# 853 "include/mimalloc/internal.h"
static inline mi_memid_t _mi_memid_create(mi_memkind_t memkind) {
  mi_memid_t memid;
  memset(&memid,0,sizeof(memid));
  memid.memkind = memkind;
  return memid;
}

static inline mi_memid_t _mi_memid_none(void) {
  return _mi_memid_create(MI_MEM_NONE);
}

static inline mi_memid_t _mi_memid_create_os(
# 864 "include/mimalloc/internal.h" 3 4
                                            _Bool 
# 864 "include/mimalloc/internal.h"
                                                 committed, 
# 864 "include/mimalloc/internal.h" 3 4
                                                            _Bool 
# 864 "include/mimalloc/internal.h"
                                                                 is_zero, 
# 864 "include/mimalloc/internal.h" 3 4
                                                                          _Bool 
# 864 "include/mimalloc/internal.h"
                                                                               is_large) {
  mi_memid_t memid = _mi_memid_create(MI_MEM_OS);
  memid.initially_committed = committed;
  memid.initially_zero = is_zero;
  memid.is_pinned = is_large;
  return memid;
}






static inline uintptr_t _mi_random_shuffle(uintptr_t x) {
  if (x==0) { x = 17; }


  x ^= x >> 30;
  x *= 0xbf58476d1ce4e5b9UL;
  x ^= x >> 27;
  x *= 0x94d049bb133111ebUL;
  x ^= x >> 31;
# 894 "include/mimalloc/internal.h"
  return x;
}





int _mi_os_numa_node_get(void);
size_t _mi_os_numa_node_count_get(void);

extern __attribute__((visibility("hidden"))) _Atomic(size_t) _mi_numa_node_count;
static inline int _mi_os_numa_node(void) {
  if (__builtin_expect(!!(
# 906 "include/mimalloc/internal.h" 3 4
    __extension__ ({ __auto_type __atomic_load_ptr = (
# 906 "include/mimalloc/internal.h"
    &_mi_numa_node_count
# 906 "include/mimalloc/internal.h" 3 4
    ); __typeof__ ((void)0, *__atomic_load_ptr) __atomic_load_tmp; __atomic_load (__atomic_load_ptr, &__atomic_load_tmp, (
# 906 "include/mimalloc/internal.h"
    memory_order_relaxed
# 906 "include/mimalloc/internal.h" 3 4
    )); __atomic_load_tmp; }) 
# 906 "include/mimalloc/internal.h"
    == 1),
# 906 "include/mimalloc/internal.h" 3 4
    1
# 906 "include/mimalloc/internal.h"
    )) { return 0; }
  else return _mi_os_numa_node_get();
}
static inline size_t _mi_os_numa_node_count(void) {
  const size_t count = 
# 910 "include/mimalloc/internal.h" 3 4
                      __extension__ ({ __auto_type __atomic_load_ptr = (
# 910 "include/mimalloc/internal.h"
                      &_mi_numa_node_count
# 910 "include/mimalloc/internal.h" 3 4
                      ); __typeof__ ((void)0, *__atomic_load_ptr) __atomic_load_tmp; __atomic_load (__atomic_load_ptr, &__atomic_load_tmp, (
# 910 "include/mimalloc/internal.h"
                      memory_order_relaxed
# 910 "include/mimalloc/internal.h" 3 4
                      )); __atomic_load_tmp; })
# 910 "include/mimalloc/internal.h"
                                                                  ;
  if (__builtin_expect(!!(count > 0),
# 911 "include/mimalloc/internal.h" 3 4
    1
# 911 "include/mimalloc/internal.h"
    )) { return count; }
  else return _mi_os_numa_node_count_get();
}
# 923 "include/mimalloc/internal.h"
# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/limits.h" 1 3 4
# 924 "include/mimalloc/internal.h" 2

static inline size_t mi_clz(uintptr_t x) {
  if (x==0) return ((1<<(3))*8);

  return __builtin_clzl(x);



}
static inline size_t mi_ctz(uintptr_t x) {
  if (x==0) return ((1<<(3))*8);

  return __builtin_ctzl(x);



}
# 1028 "include/mimalloc/internal.h"
static inline size_t mi_bsr(uintptr_t x) {
  return (x==0 ? ((1<<(3))*8) : ((1<<(3))*8) - 1 - mi_clz(x));
}
# 1062 "include/mimalloc/internal.h"
static inline void _mi_memcpy(void* dst, const void* src, size_t n) {
  memcpy(dst, src, n);
}
static inline void _mi_memzero(void* dst, size_t n) {
  memset(dst, 0, n);
}
# 1077 "include/mimalloc/internal.h"
static inline void _mi_memcpy_aligned(void* dst, const void* src, size_t n) {
  ;
  void* adst = __builtin_assume_aligned(dst, (1<<(3)));
  const void* asrc = __builtin_assume_aligned(src, (1<<(3)));
  _mi_memcpy(adst, asrc, n);
}

static inline void _mi_memzero_aligned(void* dst, size_t n) {
  ;
  void* adst = __builtin_assume_aligned(dst, (1<<(3)));
  _mi_memzero(adst, n);
}
# 9 "src/options.c" 2

# 1 "include/mimalloc/prim.h" 1






       
# 24 "include/mimalloc/prim.h"
typedef struct mi_os_mem_config_s {
  size_t page_size;
  size_t large_page_size;
  size_t alloc_granularity;
  size_t physical_memory;
  size_t virtual_address_bits;
  
# 30 "include/mimalloc/prim.h" 3 4
 _Bool 
# 30 "include/mimalloc/prim.h"
         has_overcommit;
  
# 31 "include/mimalloc/prim.h" 3 4
 _Bool 
# 31 "include/mimalloc/prim.h"
         has_partial_free;
  
# 32 "include/mimalloc/prim.h" 3 4
 _Bool 
# 32 "include/mimalloc/prim.h"
         has_virtual_reserve;
} mi_os_mem_config_t;


void _mi_prim_mem_init( mi_os_mem_config_t* config );


int _mi_prim_free(void* addr, size_t size );
# 49 "include/mimalloc/prim.h"
int _mi_prim_alloc(void* hint_addr, size_t size, size_t try_alignment, 
# 49 "include/mimalloc/prim.h" 3 4
                                                                      _Bool 
# 49 "include/mimalloc/prim.h"
                                                                           commit, 
# 49 "include/mimalloc/prim.h" 3 4
                                                                                   _Bool 
# 49 "include/mimalloc/prim.h"
                                                                                        allow_large, 
# 49 "include/mimalloc/prim.h" 3 4
                                                                                                     _Bool
# 49 "include/mimalloc/prim.h"
                                                                                                         * is_large, 
# 49 "include/mimalloc/prim.h" 3 4
                                                                                                                     _Bool
# 49 "include/mimalloc/prim.h"
                                                                                                                         * is_zero, void** addr);




int _mi_prim_commit(void* addr, size_t size, 
# 54 "include/mimalloc/prim.h" 3 4
                                            _Bool
# 54 "include/mimalloc/prim.h"
                                                * is_zero);





int _mi_prim_decommit(void* addr, size_t size, 
# 60 "include/mimalloc/prim.h" 3 4
                                              _Bool
# 60 "include/mimalloc/prim.h"
                                                  * needs_recommit);



int _mi_prim_reset(void* addr, size_t size);


int _mi_prim_protect(void* addr, size_t size, 
# 67 "include/mimalloc/prim.h" 3 4
                                             _Bool 
# 67 "include/mimalloc/prim.h"
                                                  protect);





int _mi_prim_alloc_huge_os_pages(void* hint_addr, size_t size, int numa_node, 
# 73 "include/mimalloc/prim.h" 3 4
                                                                             _Bool
# 73 "include/mimalloc/prim.h"
                                                                                 * is_zero, void** addr);


size_t _mi_prim_numa_node(void);


size_t _mi_prim_numa_node_count(void);


mi_msecs_t _mi_prim_clock_now(void);


typedef struct mi_process_info_s {
  mi_msecs_t elapsed;
  mi_msecs_t utime;
  mi_msecs_t stime;
  size_t current_rss;
  size_t peak_rss;
  size_t current_commit;
  size_t peak_commit;
  size_t page_faults;
} mi_process_info_t;

void _mi_prim_process_info(mi_process_info_t* pinfo);



void _mi_prim_out_stderr( const char* msg );




# 104 "include/mimalloc/prim.h" 3 4
_Bool 
# 104 "include/mimalloc/prim.h"
    _mi_prim_getenv(const char* name, char* result, size_t result_size);





# 109 "include/mimalloc/prim.h" 3 4
_Bool 
# 109 "include/mimalloc/prim.h"
    _mi_prim_random_buf(void* buf, size_t buf_len);


void _mi_prim_thread_init_auto_done(void);


void _mi_prim_thread_done_auto_done(void);


void _mi_prim_thread_associate_default_heap(mi_heap_t* heap);
# 149 "include/mimalloc/prim.h"
static inline void* mi_prim_tls_slot(size_t slot) {
  void* res;
  const size_t ofs = (slot*sizeof(void*));







    __asm__("movq %%fs:%1, %0" : "=r" (res) : "m" (*((void**)ofs)) : );
# 176 "include/mimalloc/prim.h"
  return res;
}


static inline void mi_prim_tls_slot_set(size_t slot, void* value) {
  const size_t ofs = (slot*sizeof(void*));







    __asm__("movq %1,%%fs:%0" : "=m" (*((void**)ofs)) : "rn" (value) : );
# 206 "include/mimalloc/prim.h"
}
# 272 "include/mimalloc/prim.h"
extern __thread mi_heap_t* _mi_heap_default;
extern 
# 273 "include/mimalloc/prim.h" 3 4
      _Bool 
# 273 "include/mimalloc/prim.h"
           _mi_process_is_initialized;

static inline mi_threadid_t _mi_prim_thread_id(void) ;
# 293 "include/mimalloc/prim.h"
static inline mi_threadid_t _mi_prim_thread_id(void) {

  return (uintptr_t)__builtin_thread_pointer();
}
# 342 "include/mimalloc/prim.h"
static inline mi_heap_t* mi_prim_get_default_heap(void);
# 409 "include/mimalloc/prim.h"
static inline mi_heap_t* mi_prim_get_default_heap(void) {



  return _mi_heap_default;
}
# 11 "src/options.c" 2

# 1 "/usr/include/stdio.h" 1 3 4
# 28 "/usr/include/stdio.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/libc-header-start.h" 1 3 4
# 29 "/usr/include/stdio.h" 2 3 4





# 1 "/usr/lib/gcc/x86_64-linux-gnu/14/include/stddef.h" 1 3 4
# 35 "/usr/include/stdio.h" 2 3 4





# 1 "/usr/include/x86_64-linux-gnu/bits/types/__fpos_t.h" 1 3 4




# 1 "/usr/include/x86_64-linux-gnu/bits/types/__mbstate_t.h" 1 3 4
# 13 "/usr/include/x86_64-linux-gnu/bits/types/__mbstate_t.h" 3 4

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


# 1 "/usr/include/x86_64-linux-gnu/bits/types/cookie_io_functions_t.h" 1 3 4
# 27 "/usr/include/x86_64-linux-gnu/bits/types/cookie_io_functions_t.h" 3 4
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
# 48 "/usr/include/stdio.h" 2 3 4
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



extern int renameat (int __oldfd, const char *__old, int __newfd,
       const char *__new) __attribute__ ((__nothrow__ , __leaf__));
# 184 "/usr/include/stdio.h" 3 4
extern int fclose (FILE *__stream) __attribute__ ((__nonnull__ (1)));
# 194 "/usr/include/stdio.h" 3 4
extern FILE *tmpfile (void)
  __attribute__ ((__malloc__)) __attribute__ ((__malloc__ (fclose, 1))) ;
# 211 "/usr/include/stdio.h" 3 4
extern char *tmpnam (char[20]) __attribute__ ((__nothrow__ , __leaf__)) ;




extern char *tmpnam_r (char __s[20]) __attribute__ ((__nothrow__ , __leaf__)) ;
# 228 "/usr/include/stdio.h" 3 4
extern char *tempnam (const char *__dir, const char *__pfx)
   __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__malloc__)) __attribute__ ((__malloc__ (__builtin_free, 1)));






extern int fflush (FILE *__stream);
# 245 "/usr/include/stdio.h" 3 4
extern int fflush_unlocked (FILE *__stream);
# 264 "/usr/include/stdio.h" 3 4
extern FILE *fopen (const char *__restrict __filename,
      const char *__restrict __modes)
  __attribute__ ((__malloc__)) __attribute__ ((__malloc__ (fclose, 1))) ;




extern FILE *freopen (const char *__restrict __filename,
        const char *__restrict __modes,
        FILE *__restrict __stream) __attribute__ ((__nonnull__ (3)));
# 299 "/usr/include/stdio.h" 3 4
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
# 334 "/usr/include/stdio.h" 3 4
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
# 463 "/usr/include/stdio.h" 3 4
extern int fscanf (FILE *__restrict __stream, const char *__restrict __format, ...) __asm__ ("" "__isoc99_fscanf")

                                __attribute__ ((__nonnull__ (1)));
extern int scanf (const char *__restrict __format, ...) __asm__ ("" "__isoc99_scanf")
                              ;
extern int sscanf (const char *__restrict __s, const char *__restrict __format, ...) __asm__ ("" "__isoc99_sscanf") __attribute__ ((__nothrow__ , __leaf__))

                      ;
# 490 "/usr/include/stdio.h" 3 4
extern int vfscanf (FILE *__restrict __s, const char *__restrict __format,
      __gnuc_va_list __arg)
     __attribute__ ((__format__ (__scanf__, 2, 0))) __attribute__ ((__nonnull__ (1)));





extern int vscanf (const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__format__ (__scanf__, 1, 0))) ;


extern int vsscanf (const char *__restrict __s,
      const char *__restrict __format, __gnuc_va_list __arg)
     __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__format__ (__scanf__, 2, 0)));
# 540 "/usr/include/stdio.h" 3 4
extern int vfscanf (FILE *__restrict __s, const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc99_vfscanf")



     __attribute__ ((__format__ (__scanf__, 2, 0))) __attribute__ ((__nonnull__ (1)));
extern int vscanf (const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc99_vscanf")

     __attribute__ ((__format__ (__scanf__, 1, 0))) ;
extern int vsscanf (const char *__restrict __s, const char *__restrict __format, __gnuc_va_list __arg) __asm__ ("" "__isoc99_vsscanf") __attribute__ ((__nothrow__ , __leaf__))



     __attribute__ ((__format__ (__scanf__, 2, 0)));
# 575 "/usr/include/stdio.h" 3 4
extern int fgetc (FILE *__stream) __attribute__ ((__nonnull__ (1)));
extern int getc (FILE *__stream) __attribute__ ((__nonnull__ (1)));





extern int getchar (void);






extern int getc_unlocked (FILE *__stream) __attribute__ ((__nonnull__ (1)));
extern int getchar_unlocked (void);
# 600 "/usr/include/stdio.h" 3 4
extern int fgetc_unlocked (FILE *__stream) __attribute__ ((__nonnull__ (1)));
# 611 "/usr/include/stdio.h" 3 4
extern int fputc (int __c, FILE *__stream) __attribute__ ((__nonnull__ (2)));
extern int putc (int __c, FILE *__stream) __attribute__ ((__nonnull__ (2)));





extern int putchar (int __c);
# 627 "/usr/include/stdio.h" 3 4
extern int fputc_unlocked (int __c, FILE *__stream) __attribute__ ((__nonnull__ (2)));







extern int putc_unlocked (int __c, FILE *__stream) __attribute__ ((__nonnull__ (2)));
extern int putchar_unlocked (int __c);






extern int getw (FILE *__stream) __attribute__ ((__nonnull__ (1)));


extern int putw (int __w, FILE *__stream) __attribute__ ((__nonnull__ (2)));







extern char *fgets (char *__restrict __s, int __n, FILE *__restrict __stream)
     __attribute__ ((__access__ (__write_only__, 1, 2))) __attribute__ ((__nonnull__ (3)));
# 689 "/usr/include/stdio.h" 3 4
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
# 756 "/usr/include/stdio.h" 3 4
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
# 793 "/usr/include/stdio.h" 3 4
extern int fseeko (FILE *__stream, __off_t __off, int __whence)
  __attribute__ ((__nonnull__ (1)));




extern __off_t ftello (FILE *__stream) __attribute__ ((__nonnull__ (1)));
# 819 "/usr/include/stdio.h" 3 4
extern int fgetpos (FILE *__restrict __stream, fpos_t *__restrict __pos)
  __attribute__ ((__nonnull__ (1)));




extern int fsetpos (FILE *__stream, const fpos_t *__pos) __attribute__ ((__nonnull__ (1)));
# 850 "/usr/include/stdio.h" 3 4
extern void clearerr (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));

extern int feof (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));

extern int ferror (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));



extern void clearerr_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int feof_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
extern int ferror_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));







extern void perror (const char *__s) __attribute__ ((__cold__));




extern int fileno (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));




extern int fileno_unlocked (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 887 "/usr/include/stdio.h" 3 4
extern int pclose (FILE *__stream) __attribute__ ((__nonnull__ (1)));





extern FILE *popen (const char *__command, const char *__modes)
  __attribute__ ((__malloc__)) __attribute__ ((__malloc__ (pclose, 1))) ;






extern char *ctermid (char *__s) __attribute__ ((__nothrow__ , __leaf__))
  __attribute__ ((__access__ (__write_only__, 1)));
# 931 "/usr/include/stdio.h" 3 4
extern void flockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));



extern int ftrylockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));


extern void funlockfile (FILE *__stream) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__nonnull__ (1)));
# 949 "/usr/include/stdio.h" 3 4
extern int __uflow (FILE *);
extern int __overflow (FILE *, int);
# 966 "/usr/include/stdio.h" 3 4
# 1 "/usr/include/x86_64-linux-gnu/bits/stdio.h" 1 3 4
# 38 "/usr/include/x86_64-linux-gnu/bits/stdio.h" 3 4
extern __inline __attribute__ ((__gnu_inline__)) int
vprintf (const char *__restrict __fmt, __gnuc_va_list __arg)
{
  return vfprintf (stdout, __fmt, __arg);
}



extern __inline __attribute__ ((__gnu_inline__)) int
getchar (void)
{
  return getc (stdin);
}




extern __inline __attribute__ ((__gnu_inline__)) int
fgetc_unlocked (FILE *__fp)
{
  return (__builtin_expect (((__fp)->_IO_read_ptr >= (__fp)->_IO_read_end), 0) ? __uflow (__fp) : *(unsigned char *) (__fp)->_IO_read_ptr++);
}





extern __inline __attribute__ ((__gnu_inline__)) int
getc_unlocked (FILE *__fp)
{
  return (__builtin_expect (((__fp)->_IO_read_ptr >= (__fp)->_IO_read_end), 0) ? __uflow (__fp) : *(unsigned char *) (__fp)->_IO_read_ptr++);
}


extern __inline __attribute__ ((__gnu_inline__)) int
getchar_unlocked (void)
{
  return (__builtin_expect (((stdin)->_IO_read_ptr >= (stdin)->_IO_read_end), 0) ? __uflow (stdin) : *(unsigned char *) (stdin)->_IO_read_ptr++);
}




extern __inline __attribute__ ((__gnu_inline__)) int
putchar (int __c)
{
  return putc (__c, stdout);
}




extern __inline __attribute__ ((__gnu_inline__)) int
fputc_unlocked (int __c, FILE *__stream)
{
  return (__builtin_expect (((__stream)->_IO_write_ptr >= (__stream)->_IO_write_end), 0) ? __overflow (__stream, (unsigned char) (__c)) : (unsigned char) (*(__stream)->_IO_write_ptr++ = (__c)));
}





extern __inline __attribute__ ((__gnu_inline__)) int
putc_unlocked (int __c, FILE *__stream)
{
  return (__builtin_expect (((__stream)->_IO_write_ptr >= (__stream)->_IO_write_end), 0) ? __overflow (__stream, (unsigned char) (__c)) : (unsigned char) (*(__stream)->_IO_write_ptr++ = (__c)));
}


extern __inline __attribute__ ((__gnu_inline__)) int
putchar_unlocked (int __c)
{
  return (__builtin_expect (((stdout)->_IO_write_ptr >= (stdout)->_IO_write_end), 0) ? __overflow (stdout, (unsigned char) (__c)) : (unsigned char) (*(stdout)->_IO_write_ptr++ = (__c)));
}
# 127 "/usr/include/x86_64-linux-gnu/bits/stdio.h" 3 4
extern __inline __attribute__ ((__gnu_inline__)) int
__attribute__ ((__nothrow__ , __leaf__)) feof_unlocked (FILE *__stream)
{
  return (((__stream)->_flags & 0x0010) != 0);
}


extern __inline __attribute__ ((__gnu_inline__)) int
__attribute__ ((__nothrow__ , __leaf__)) ferror_unlocked (FILE *__stream)
{
  return (((__stream)->_flags & 0x0020) != 0);
}
# 967 "/usr/include/stdio.h" 2 3 4







# 13 "src/options.c" 2





# 17 "src/options.c"
static long mi_max_error_count = 16;
static long mi_max_warning_count = 16;

static void mi_add_stderr_output(void);

int mi_version(void) {
  return 219;
}
# 33 "src/options.c"
typedef enum mi_init_e {
  UNINIT,
  DEFAULTED,
  INITIALIZED
} mi_init_t;

typedef struct mi_option_desc_s {
  long value;
  mi_init_t init;
  mi_option_t option;
  const char* name;
  const char* legacy_name;
} mi_option_desc_t;
# 106 "src/options.c"
static mi_option_desc_t options[_mi_option_last] =
{




  { 0, UNINIT, mi_option_show_errors, "show_errors", 
# 112 "src/options.c" 3 4
              ((void *)0) 
# 112 "src/options.c"
                                     },

  { 0, UNINIT, mi_option_show_stats, "show_stats", 
# 114 "src/options.c" 3 4
              ((void *)0) 
# 114 "src/options.c"
                                    },
  { 0, UNINIT, mi_option_verbose, "verbose", 
# 115 "src/options.c" 3 4
                               ((void *)0) 
# 115 "src/options.c"
                                                  },


  { 1,
       UNINIT, mi_option_eager_commit, "eager_commit", 
# 119 "src/options.c" 3 4
              ((void *)0) 
# 119 "src/options.c"
                                      },
  { 2,
       UNINIT, mi_option_arena_eager_commit, "arena_eager_commit", "eager_region_commit" },
  { 1, UNINIT, mi_option_purge_decommits, "purge_decommits", "reset_decommits" },
  { 2,
       UNINIT, mi_option_allow_large_os_pages, "allow_large_os_pages", "large_os_pages" },
  { 0,
       UNINIT, mi_option_reserve_huge_os_pages, "reserve_huge_os_pages", 
# 126 "src/options.c" 3 4
              ((void *)0) 
# 126 "src/options.c"
                                               },
  {-1, UNINIT, mi_option_reserve_huge_os_pages_at, "reserve_huge_os_pages_at", 
# 127 "src/options.c" 3 4
              ((void *)0) 
# 127 "src/options.c"
                                                  },
  { 0,
       UNINIT, mi_option_reserve_os_memory, "reserve_os_memory", 
# 129 "src/options.c" 3 4
              ((void *)0) 
# 129 "src/options.c"
                                               },
  { 0, UNINIT, mi_option_deprecated_segment_cache, "deprecated_segment_cache", 
# 130 "src/options.c" 3 4
              ((void *)0) 
# 130 "src/options.c"
                                                  },
  { 0, UNINIT, mi_option_deprecated_page_reset, "deprecated_page_reset", 
# 131 "src/options.c" 3 4
              ((void *)0) 
# 131 "src/options.c"
                                               },
  { 0, UNINIT, mi_option_abandoned_page_purge, "abandoned_page_purge", "abandoned_page_reset" },
  { 0, UNINIT, mi_option_deprecated_segment_reset, "deprecated_segment_reset", 
# 133 "src/options.c" 3 4
              ((void *)0) 
# 133 "src/options.c"
                                                  },



  { 1, UNINIT, mi_option_eager_commit_delay, "eager_commit_delay", 
# 137 "src/options.c" 3 4
              ((void *)0) 
# 137 "src/options.c"
                                            },

  { 10, UNINIT, mi_option_purge_delay, "purge_delay", "reset_delay" },
  { 0, UNINIT, mi_option_use_numa_nodes, "use_numa_nodes", 
# 140 "src/options.c" 3 4
                ((void *)0) 
# 140 "src/options.c"
                                          },
  { 0, UNINIT, mi_option_disallow_os_alloc, "disallow_os_alloc", "limit_os_alloc" },
  { 100, UNINIT, mi_option_os_tag, "os_tag", 
# 142 "src/options.c" 3 4
                ((void *)0) 
# 142 "src/options.c"
                                  },
  { 32, UNINIT, mi_option_max_errors, "max_errors", 
# 143 "src/options.c" 3 4
                ((void *)0) 
# 143 "src/options.c"
                                      },
  { 32, UNINIT, mi_option_max_warnings, "max_warnings", 
# 144 "src/options.c" 3 4
                ((void *)0) 
# 144 "src/options.c"
                                        },
  { 10, UNINIT, mi_option_max_segment_reclaim, "max_segment_reclaim", 
# 145 "src/options.c" 3 4
                ((void *)0)
# 145 "src/options.c"
                                              },
  { 0, UNINIT, mi_option_destroy_on_exit, "destroy_on_exit", 
# 146 "src/options.c" 3 4
                ((void *)0)
# 146 "src/options.c"
                                          },
  { 1024L*1024L, UNINIT, mi_option_arena_reserve, "arena_reserve", 
# 147 "src/options.c" 3 4
                                     ((void *)0) 
# 147 "src/options.c"
                                                              },
  { 10, UNINIT, mi_option_arena_purge_mult, "arena_purge_mult", 
# 148 "src/options.c" 3 4
                ((void *)0) 
# 148 "src/options.c"
                                            },
  { 1, UNINIT, mi_option_purge_extend_delay, "purge_extend_delay", "decommit_extend_delay" },
  { 0, UNINIT, mi_option_abandoned_reclaim_on_free, "abandoned_reclaim_on_free", 
# 150 "src/options.c" 3 4
                ((void *)0) 
# 150 "src/options.c"
                                                     },
  { 0, UNINIT, mi_option_disallow_arena_alloc, "disallow_arena_alloc", 
# 151 "src/options.c" 3 4
                                              ((void *)0) 
# 151 "src/options.c"
                                                                              },
  { 400, UNINIT, mi_option_retry_on_oom, "retry_on_oom", 
# 152 "src/options.c" 3 4
                ((void *)0) 
# 152 "src/options.c"
                                        },



  { 0, UNINIT, mi_option_visit_abandoned, "visit_abandoned", 
# 156 "src/options.c" 3 4
                ((void *)0) 
# 156 "src/options.c"
                                           },

  { 0, UNINIT, mi_option_guarded_min, "guarded_min", 
# 158 "src/options.c" 3 4
                ((void *)0) 
# 158 "src/options.c"
                                       },
  { (((1024ULL)*(1024ULL))*(1024ULL)), UNINIT, mi_option_guarded_max, "guarded_max", 
# 159 "src/options.c" 3 4
                   ((void *)0) 
# 159 "src/options.c"
                                          },
  { 0, UNINIT, mi_option_guarded_precise, "guarded_precise", 
# 160 "src/options.c" 3 4
                ((void *)0) 
# 160 "src/options.c"
                                           },
  { 0,
         UNINIT, mi_option_guarded_sample_rate, "guarded_sample_rate", 
# 162 "src/options.c" 3 4
                ((void *)0)
# 162 "src/options.c"
                                              },
  { 0, UNINIT, mi_option_guarded_sample_seed, "guarded_sample_seed", 
# 163 "src/options.c" 3 4
                ((void *)0)
# 163 "src/options.c"
                                              },
  { 0, UNINIT, mi_option_target_segments_per_thread, "target_segments_per_thread", 
# 164 "src/options.c" 3 4
                ((void *)0) 
# 164 "src/options.c"
                                                      },
};

static void mi_option_init(mi_option_desc_t* desc);

static 
# 169 "src/options.c" 3 4
      _Bool 
# 169 "src/options.c"
           mi_option_has_size_in_kib(mi_option_t option) {
  return (option == mi_option_reserve_os_memory || option == mi_option_arena_reserve);
}

void _mi_options_init(void) {

  mi_add_stderr_output();
  for(int i = 0; i < _mi_option_last; i++ ) {
    mi_option_t option = (mi_option_t)i;
    long l = mi_option_get(option); (void)(l);

    {
      mi_option_desc_t* desc = &options[option];
      _mi_verbose_message("option '%s': %ld %s\n", desc->name, desc->value, (mi_option_has_size_in_kib(option) ? "KiB" : ""));
    }
  }
  mi_max_error_count = mi_option_get(mi_option_max_errors);
  mi_max_warning_count = mi_option_get(mi_option_max_warnings);
# 196 "src/options.c"
}

long _mi_option_get_fast(mi_option_t option) {
  ;
  mi_option_desc_t* desc = &options[option];
  ;

  return desc->value;
}


__attribute__((warn_unused_result)) long mi_option_get(mi_option_t option) {
  ;
  if (option < 0 || option >= _mi_option_last) return 0;
  mi_option_desc_t* desc = &options[option];
  ;
  if (__builtin_expect(!!(desc->init == UNINIT),
# 212 "src/options.c" 3 4
    0
# 212 "src/options.c"
    )) {
    mi_option_init(desc);
  }
  return desc->value;
}

__attribute__((warn_unused_result)) long mi_option_get_clamp(mi_option_t option, long min, long max) {
  long x = mi_option_get(option);
  return (x < min ? min : (x > max ? max : x));
}

__attribute__((warn_unused_result)) size_t mi_option_get_size(mi_option_t option) {
  const long x = mi_option_get(option);
  size_t size = (x < 0 ? 0 : (size_t)x);
  if (mi_option_has_size_in_kib(option)) {
    size *= (1024ULL);
  }
  return size;
}

void mi_option_set(mi_option_t option, long value) {
  ;
  if (option < 0 || option >= _mi_option_last) return;
  mi_option_desc_t* desc = &options[option];
  ;
  desc->value = value;
  desc->init = INITIALIZED;

  if (desc->option == mi_option_guarded_min && _mi_option_get_fast(mi_option_guarded_max) < value) {
    mi_option_set(mi_option_guarded_max, value);
  }
  else if (desc->option == mi_option_guarded_max && _mi_option_get_fast(mi_option_guarded_min) > value) {
    mi_option_set(mi_option_guarded_min, value);
  }
}

void mi_option_set_default(mi_option_t option, long value) {
  ;
  if (option < 0 || option >= _mi_option_last) return;
  mi_option_desc_t* desc = &options[option];
  if (desc->init != INITIALIZED) {
    desc->value = value;
  }
}

__attribute__((warn_unused_result)) 
# 257 "src/options.c" 3 4
                 _Bool 
# 257 "src/options.c"
                      mi_option_is_enabled(mi_option_t option) {
  return (mi_option_get(option) != 0);
}

void mi_option_set_enabled(mi_option_t option, 
# 261 "src/options.c" 3 4
                                              _Bool 
# 261 "src/options.c"
                                                   enable) {
  mi_option_set(option, (enable ? 1 : 0));
}

void mi_option_set_enabled_default(mi_option_t option, 
# 265 "src/options.c" 3 4
                                                      _Bool 
# 265 "src/options.c"
                                                           enable) {
  mi_option_set_default(option, (enable ? 1 : 0));
}

void mi_option_enable(mi_option_t option) {
  mi_option_set_enabled(option,
# 270 "src/options.c" 3 4
                              1
# 270 "src/options.c"
                                  );
}

void mi_option_disable(mi_option_t option) {
  mi_option_set_enabled(option,
# 274 "src/options.c" 3 4
                              0
# 274 "src/options.c"
                                   );
}

static void mi_out_stderr(const char* msg, void* arg) {
  (void)(arg);
  if (msg != 
# 279 "src/options.c" 3 4
            ((void *)0) 
# 279 "src/options.c"
                 && msg[0] != 0) {
    _mi_prim_out_stderr(msg);
  }
}
# 291 "src/options.c"
static char out_buf[((size_t)(16*1024))+1];
static _Atomic(size_t) out_len;

static void mi_out_buf(const char* msg, void* arg) {
  (void)(arg);
  if (msg==
# 296 "src/options.c" 3 4
          ((void *)0)
# 296 "src/options.c"
              ) return;
  if (
# 297 "src/options.c" 3 4
     __extension__ ({ __auto_type __atomic_load_ptr = (
# 297 "src/options.c"
     &out_len
# 297 "src/options.c" 3 4
     ); __typeof__ ((void)0, *__atomic_load_ptr) __atomic_load_tmp; __atomic_load (__atomic_load_ptr, &__atomic_load_tmp, (
# 297 "src/options.c"
     memory_order_relaxed
# 297 "src/options.c" 3 4
     )); __atomic_load_tmp; })
# 297 "src/options.c"
                                     >=((size_t)(16*1024))) return;
  size_t n = _mi_strlen(msg);
  if (n==0) return;

  size_t start = 
# 301 "src/options.c" 3 4
                __atomic_fetch_add ((
# 301 "src/options.c"
                &out_len
# 301 "src/options.c" 3 4
                ), (
# 301 "src/options.c"
                n
# 301 "src/options.c" 3 4
                ), (
# 301 "src/options.c"
                memory_order_acq_rel
# 301 "src/options.c" 3 4
                ))
# 301 "src/options.c"
                                                  ;
  if (start >= ((size_t)(16*1024))) return;

  if (start+n >= ((size_t)(16*1024))) {
    n = ((size_t)(16*1024))-start-1;
  }
  _mi_memcpy(&out_buf[start], msg, n);
}

static void mi_out_buf_flush(mi_output_fun* out, 
# 310 "src/options.c" 3 4
                                                _Bool 
# 310 "src/options.c"
                                                     no_more_buf, void* arg) {
  if (out==
# 311 "src/options.c" 3 4
          ((void *)0)
# 311 "src/options.c"
              ) return;

  size_t count = 
# 313 "src/options.c" 3 4
                __atomic_fetch_add ((
# 313 "src/options.c"
                &out_len
# 313 "src/options.c" 3 4
                ), (
# 313 "src/options.c"
                (no_more_buf ? ((size_t)(16*1024)) : 1)
# 313 "src/options.c" 3 4
                ), (
# 313 "src/options.c"
                memory_order_acq_rel
# 313 "src/options.c" 3 4
                ))
# 313 "src/options.c"
                                                                                        ;

  if (count>((size_t)(16*1024))) count = ((size_t)(16*1024));
  out_buf[count] = 0;
  out(out_buf,arg);
  if (!no_more_buf) {
    out_buf[count] = '\n';
  }
}




static void mi_out_buf_stderr(const char* msg, void* arg) {
  mi_out_stderr(msg,arg);
  mi_out_buf(msg,arg);
}
# 339 "src/options.c"
static mi_output_fun* volatile mi_out_default;
static _Atomic(void*) mi_out_arg;

static mi_output_fun* mi_out_get_default(void** parg) {
  if (parg != 
# 343 "src/options.c" 3 4
             ((void *)0)
# 343 "src/options.c"
                 ) { *parg = 
# 343 "src/options.c" 3 4
                             __extension__ ({ __auto_type __atomic_load_ptr = (
# 343 "src/options.c"
                             &mi_out_arg
# 343 "src/options.c" 3 4
                             ); __typeof__ ((void)0, *__atomic_load_ptr) __atomic_load_tmp; __atomic_load (__atomic_load_ptr, &__atomic_load_tmp, (
# 343 "src/options.c"
                             memory_order_acquire
# 343 "src/options.c" 3 4
                             )); __atomic_load_tmp; })
# 343 "src/options.c"
                                                                         ; }
  mi_output_fun* out = mi_out_default;
  return (out == 
# 345 "src/options.c" 3 4
                ((void *)0) 
# 345 "src/options.c"
                     ? &mi_out_buf : out);
}

void mi_register_output(mi_output_fun* out, void* arg) {
  mi_out_default = (out == 
# 349 "src/options.c" 3 4
                          ((void *)0) 
# 349 "src/options.c"
                               ? &mi_out_stderr : out);
  
# 350 "src/options.c" 3 4
 __extension__ ({ __auto_type __atomic_store_ptr = (
# 350 "src/options.c"
 &mi_out_arg
# 350 "src/options.c" 3 4
 ); __typeof__ ((void)0, *__atomic_store_ptr) __atomic_store_tmp = (
# 350 "src/options.c"
 arg
# 350 "src/options.c" 3 4
 ); __atomic_store (__atomic_store_ptr, &__atomic_store_tmp, (
# 350 "src/options.c"
 memory_order_release
# 350 "src/options.c" 3 4
 )); })
# 350 "src/options.c"
                                                   ;
  if (out!=
# 351 "src/options.c" 3 4
          ((void *)0)
# 351 "src/options.c"
              ) mi_out_buf_flush(out,
# 351 "src/options.c" 3 4
                                     1
# 351 "src/options.c"
                                         ,arg);
}


static void mi_add_stderr_output(void) {
  ;
  mi_out_buf_flush(&mi_out_stderr, 
# 357 "src/options.c" 3 4
                                  0
# 357 "src/options.c"
                                       , 
# 357 "src/options.c" 3 4
                                         ((void *)0)
# 357 "src/options.c"
                                             );
  mi_out_default = &mi_out_buf_stderr;
}




static _Atomic(size_t) error_count;
static _Atomic(size_t) warning_count;
# 376 "src/options.c"
static __thread 
# 376 "src/options.c" 3 4
                     _Bool 
# 376 "src/options.c"
                          recurse = 
# 376 "src/options.c" 3 4
                                    0
# 376 "src/options.c"
                                         ;

static __attribute__((noinline)) 
# 378 "src/options.c" 3 4
                       _Bool 
# 378 "src/options.c"
                            mi_recurse_enter_prim(void) {
  if (recurse) return 
# 379 "src/options.c" 3 4
                     0
# 379 "src/options.c"
                          ;
  recurse = 
# 380 "src/options.c" 3 4
           1
# 380 "src/options.c"
               ;
  return 
# 381 "src/options.c" 3 4
        1
# 381 "src/options.c"
            ;
}

static __attribute__((noinline)) void mi_recurse_exit_prim(void) {
  recurse = 
# 385 "src/options.c" 3 4
           0
# 385 "src/options.c"
                ;
}

static 
# 388 "src/options.c" 3 4
      _Bool 
# 388 "src/options.c"
           mi_recurse_enter(void) {



  return mi_recurse_enter_prim();
}

static void mi_recurse_exit(void) {



  mi_recurse_exit_prim();
}

void _mi_fputs(mi_output_fun* out, void* arg, const char* prefix, const char* message) {
  if (out==
# 403 "src/options.c" 3 4
          ((void *)0) 
# 403 "src/options.c"
               || (void*)out==(void*)
# 403 "src/options.c" 3 4
                                     stdout 
# 403 "src/options.c"
                                            || (void*)out==(void*)
# 403 "src/options.c" 3 4
                                                                  stderr
# 403 "src/options.c"
                                                                        ) {
    if (!mi_recurse_enter()) return;
    out = mi_out_get_default(&arg);
    if (prefix != 
# 406 "src/options.c" 3 4
                 ((void *)0)
# 406 "src/options.c"
                     ) out(prefix, arg);
    out(message, arg);
    mi_recurse_exit();
  }
  else {
    if (prefix != 
# 411 "src/options.c" 3 4
                 ((void *)0)
# 411 "src/options.c"
                     ) out(prefix, arg);
    out(message, arg);
  }
}



static void mi_vfprintf( mi_output_fun* out, void* arg, const char* prefix, const char* fmt, va_list args ) {
  char buf[512];
  if (fmt==
# 420 "src/options.c" 3 4
          ((void *)0)
# 420 "src/options.c"
              ) return;
  if (!mi_recurse_enter()) return;
  _mi_vsnprintf(buf, sizeof(buf)-1, fmt, args);
  mi_recurse_exit();
  _mi_fputs(out,arg,prefix,buf);
}

void _mi_fprintf( mi_output_fun* out, void* arg, const char* fmt, ... ) {
  va_list args;
  
# 429 "src/options.c" 3 4
 __builtin_va_start(
# 429 "src/options.c"
 args
# 429 "src/options.c" 3 4
 ,
# 429 "src/options.c"
 fmt
# 429 "src/options.c" 3 4
 )
# 429 "src/options.c"
                   ;
  mi_vfprintf(out,arg,
# 430 "src/options.c" 3 4
                     ((void *)0)
# 430 "src/options.c"
                         ,fmt,args);
  
# 431 "src/options.c" 3 4
 __builtin_va_end(
# 431 "src/options.c"
 args
# 431 "src/options.c" 3 4
 )
# 431 "src/options.c"
             ;
}

static void mi_vfprintf_thread(mi_output_fun* out, void* arg, const char* prefix, const char* fmt, va_list args) {
  if (prefix != 
# 435 "src/options.c" 3 4
               ((void *)0) 
# 435 "src/options.c"
                    && _mi_strnlen(prefix,33) <= 32 && !_mi_is_main_thread()) {
    char tprefix[64];
    _mi_snprintf(tprefix, sizeof(tprefix), "%sthread 0x%tx: ", prefix, (uintptr_t)_mi_thread_id());
    mi_vfprintf(out, arg, tprefix, fmt, args);
  }
  else {
    mi_vfprintf(out, arg, prefix, fmt, args);
  }
}

void _mi_trace_message(const char* fmt, ...) {
  if (mi_option_get(mi_option_verbose) <= 1) return;
  va_list args;
  
# 448 "src/options.c" 3 4
 __builtin_va_start(
# 448 "src/options.c"
 args
# 448 "src/options.c" 3 4
 ,
# 448 "src/options.c"
 fmt
# 448 "src/options.c" 3 4
 )
# 448 "src/options.c"
                    ;
  mi_vfprintf_thread(
# 449 "src/options.c" 3 4
                    ((void *)0)
# 449 "src/options.c"
                        , 
# 449 "src/options.c" 3 4
                          ((void *)0)
# 449 "src/options.c"
                              , "mimalloc: ", fmt, args);
  
# 450 "src/options.c" 3 4
 __builtin_va_end(
# 450 "src/options.c"
 args
# 450 "src/options.c" 3 4
 )
# 450 "src/options.c"
             ;
}

void _mi_verbose_message(const char* fmt, ...) {
  if (!mi_option_is_enabled(mi_option_verbose)) return;
  va_list args;
  
# 456 "src/options.c" 3 4
 __builtin_va_start(
# 456 "src/options.c"
 args
# 456 "src/options.c" 3 4
 ,
# 456 "src/options.c"
 fmt
# 456 "src/options.c" 3 4
 )
# 456 "src/options.c"
                   ;
  mi_vfprintf(
# 457 "src/options.c" 3 4
             ((void *)0)
# 457 "src/options.c"
                 , 
# 457 "src/options.c" 3 4
                   ((void *)0)
# 457 "src/options.c"
                       , "mimalloc: ", fmt, args);
  
# 458 "src/options.c" 3 4
 __builtin_va_end(
# 458 "src/options.c"
 args
# 458 "src/options.c" 3 4
 )
# 458 "src/options.c"
             ;
}

static void mi_show_error_message(const char* fmt, va_list args) {
  if (!mi_option_is_enabled(mi_option_verbose)) {
    if (!mi_option_is_enabled(mi_option_show_errors)) return;
    if (mi_max_error_count >= 0 && (long)
# 464 "src/options.c" 3 4
                                        __atomic_fetch_add ((
# 464 "src/options.c"
                                        &error_count
# 464 "src/options.c" 3 4
                                        ), (
# 464 "src/options.c"
                                        (uintptr_t)1
# 464 "src/options.c" 3 4
                                        ), (
# 464 "src/options.c"
                                        memory_order_acq_rel
# 464 "src/options.c" 3 4
                                        )) 
# 464 "src/options.c"
                                                                                  > mi_max_error_count) return;
  }
  mi_vfprintf_thread(
# 466 "src/options.c" 3 4
                    ((void *)0)
# 466 "src/options.c"
                        , 
# 466 "src/options.c" 3 4
                          ((void *)0)
# 466 "src/options.c"
                              , "mimalloc: error: ", fmt, args);
}

void _mi_warning_message(const char* fmt, ...) {
  if (!mi_option_is_enabled(mi_option_verbose)) {
    if (!mi_option_is_enabled(mi_option_show_errors)) return;
    if (mi_max_warning_count >= 0 && (long)
# 472 "src/options.c" 3 4
                                          __atomic_fetch_add ((
# 472 "src/options.c"
                                          &warning_count
# 472 "src/options.c" 3 4
                                          ), (
# 472 "src/options.c"
                                          (uintptr_t)1
# 472 "src/options.c" 3 4
                                          ), (
# 472 "src/options.c"
                                          memory_order_acq_rel
# 472 "src/options.c" 3 4
                                          )) 
# 472 "src/options.c"
                                                                                      > mi_max_warning_count) return;
  }
  va_list args;
  
# 475 "src/options.c" 3 4
 __builtin_va_start(
# 475 "src/options.c"
 args
# 475 "src/options.c" 3 4
 ,
# 475 "src/options.c"
 fmt
# 475 "src/options.c" 3 4
 )
# 475 "src/options.c"
                   ;
  mi_vfprintf_thread(
# 476 "src/options.c" 3 4
                    ((void *)0)
# 476 "src/options.c"
                        , 
# 476 "src/options.c" 3 4
                          ((void *)0)
# 476 "src/options.c"
                              , "mimalloc: warning: ", fmt, args);
  
# 477 "src/options.c" 3 4
 __builtin_va_end(
# 477 "src/options.c"
 args
# 477 "src/options.c" 3 4
 )
# 477 "src/options.c"
             ;
}
# 492 "src/options.c"
static mi_error_fun* volatile mi_error_handler;
static _Atomic(void*) mi_error_arg;

static void mi_error_default(int err) {
  (void)(err);
# 515 "src/options.c"
}

void mi_register_error(mi_error_fun* fun, void* arg) {
  mi_error_handler = fun;
  
# 519 "src/options.c" 3 4
 __extension__ ({ __auto_type __atomic_store_ptr = (
# 519 "src/options.c"
 &mi_error_arg
# 519 "src/options.c" 3 4
 ); __typeof__ ((void)0, *__atomic_store_ptr) __atomic_store_tmp = (
# 519 "src/options.c"
 arg
# 519 "src/options.c" 3 4
 ); __atomic_store (__atomic_store_ptr, &__atomic_store_tmp, (
# 519 "src/options.c"
 memory_order_release
# 519 "src/options.c" 3 4
 )); })
# 519 "src/options.c"
                                                     ;
}

void _mi_error_message(int err, const char* fmt, ...) {

  va_list args;
  
# 525 "src/options.c" 3 4
 __builtin_va_start(
# 525 "src/options.c"
 args
# 525 "src/options.c" 3 4
 ,
# 525 "src/options.c"
 fmt
# 525 "src/options.c" 3 4
 )
# 525 "src/options.c"
                    ;
  mi_show_error_message(fmt, args);
  
# 527 "src/options.c" 3 4
 __builtin_va_end(
# 527 "src/options.c"
 args
# 527 "src/options.c" 3 4
 )
# 527 "src/options.c"
             ;

  if (mi_error_handler != 
# 529 "src/options.c" 3 4
                         ((void *)0)
# 529 "src/options.c"
                             ) {
    mi_error_handler(err, 
# 530 "src/options.c" 3 4
                         __extension__ ({ __auto_type __atomic_load_ptr = (
# 530 "src/options.c"
                         &mi_error_arg
# 530 "src/options.c" 3 4
                         ); __typeof__ ((void)0, *__atomic_load_ptr) __atomic_load_tmp; __atomic_load (__atomic_load_ptr, &__atomic_load_tmp, (
# 530 "src/options.c"
                         memory_order_acquire
# 530 "src/options.c" 3 4
                         )); __atomic_load_tmp; })
# 530 "src/options.c"
                                                                       );
  }
  else {
    mi_error_default(err);
  }
}
# 546 "src/options.c"
static void mi_option_init(mi_option_desc_t* desc) {

  char s[64 + 1];
  char buf[64+1];
  _mi_strlcpy(buf, "mimalloc_", sizeof(buf));
  _mi_strlcat(buf, desc->name, sizeof(buf));
  
# 552 "src/options.c" 3 4
 _Bool 
# 552 "src/options.c"
      found = _mi_getenv(buf, s, sizeof(s));
  if (!found && desc->legacy_name != 
# 553 "src/options.c" 3 4
                                    ((void *)0)
# 553 "src/options.c"
                                        ) {
    _mi_strlcpy(buf, "mimalloc_", sizeof(buf));
    _mi_strlcat(buf, desc->legacy_name, sizeof(buf));
    found = _mi_getenv(buf, s, sizeof(s));
    if (found) {
      _mi_warning_message("environment option \"mimalloc_%s\" is deprecated -- use \"mimalloc_%s\" instead.\n", desc->legacy_name, desc->name);
    }
  }

  if (found) {
    size_t len = _mi_strnlen(s, sizeof(buf) - 1);
    for (size_t i = 0; i < len; i++) {
      buf[i] = _mi_toupper(s[i]);
    }
    buf[len] = 0;
    if (buf[0] == 0 || strstr("1;TRUE;YES;ON", buf) != 
# 568 "src/options.c" 3 4
                                                      ((void *)0)
# 568 "src/options.c"
                                                          ) {
      desc->value = 1;
      desc->init = INITIALIZED;
    }
    else if (strstr("0;FALSE;NO;OFF", buf) != 
# 572 "src/options.c" 3 4
                                             ((void *)0)
# 572 "src/options.c"
                                                 ) {
      desc->value = 0;
      desc->init = INITIALIZED;
    }
    else {
      char* end = buf;
      long value = strtol(buf, &end, 10);
      if (mi_option_has_size_in_kib(desc->option)) {


        size_t size = (value < 0 ? 0 : (size_t)value);
        
# 583 "src/options.c" 3 4
       _Bool 
# 583 "src/options.c"
            overflow = 
# 583 "src/options.c" 3 4
                       0
# 583 "src/options.c"
                            ;
        if (*end == 'K') { end++; }
        else if (*end == 'M') { overflow = mi_mul_overflow(size,(1024ULL),&size); end++; }
        else if (*end == 'G') { overflow = mi_mul_overflow(size,((1024ULL)*(1024ULL)),&size); end++; }
        else if (*end == 'T') { overflow = mi_mul_overflow(size,(((1024ULL)*(1024ULL))*(1024ULL)),&size); end++; }
        else { size = (size + (1024ULL) - 1) / (1024ULL); }
        if (end[0] == 'I' && end[1] == 'B') { end += 2; }
        else if (*end == 'B') { end++; }
        if (overflow || size > ((1ULL<< (13 + (3))) * (
# 591 "src/options.c" 3 4
                              (4294967295U)
# 591 "src/options.c"
                              -1))) { size = (((1ULL<< (13 + (3))) * (
# 591 "src/options.c" 3 4
                                                           (4294967295U)
# 591 "src/options.c"
                                                           -1)) / (1024ULL)); }
        value = (size > 0x7fffffffffffffffL 
# 592 "src/options.c"
                                ? 0x7fffffffffffffffL 
# 592 "src/options.c"
                                           : (long)size);
      }
      if (*end == 0) {
        mi_option_set(desc->option, value);
      }
      else {

        desc->init = DEFAULTED;
        if (desc->option == mi_option_verbose && desc->value == 0) {


          desc->value = 1;
          _mi_warning_message("environment option mimalloc_%s has an invalid value.\n", desc->name);
          desc->value = 0;
        }
        else {
          _mi_warning_message("environment option mimalloc_%s has an invalid value.\n", desc->name);
        }
      }
    }
    ;
  }
  else if (!_mi_preloading()) {
    desc->init = DEFAULTED;
  }
}
