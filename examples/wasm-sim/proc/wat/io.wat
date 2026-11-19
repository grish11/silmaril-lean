;; io: the one linear memory that every WASI-calling module (loader, sys, libc) uses, at
;; disjoint offsets (loader: [0, 0x100000) and the ELF file from 0x200000; sys: [0x100000,
;; 0x110100); libc: [0x120000, 0x130100)). WASI preview 1 reads iovecs from the caller's
;; exported "memory"; after `wasm-merge` there is only one such export, so the modules must
;; already agree on one memory when linked separately.
(module (memory (export "memory") 33))
