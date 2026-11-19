typedef long unsigned int size_t;
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
static mi_os_mem_config_t mi_os_mem_config = {
  4096,
  0,
  4096,
  32*(((1024ULL)*(1024ULL))*(1024ULL)),
  48,
  
# 41 "src/os.c" 3 4
 1
# 41 "src/os.c"
     ,
  
# 42 "src/os.c" 3 4
 0
# 42 "src/os.c"
      ,
  
# 43 "src/os.c" 3 4
 1

# 44 "src/os.c"
};
size_t _mi_os_page_size(void) {
  return mi_os_mem_config.page_size;
}
size_t _mi_os_large_page_size(void) {
  return (mi_os_mem_config.large_page_size != 0 ? mi_os_mem_config.large_page_size : _mi_os_page_size());
}
