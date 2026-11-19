# Actual remaining original-package O2 stripping pairs

This completed tranche adds80 actual ELF rows/80 unique hashes/40 stripping pairs on x86_64 and AArch64. [summary.json](summary.json) and per-package reports map source/archive/compiler/flags/output/receipt/census/pair identities and first/repeat timings.

| Project | New ELF rows | Unstripped canonical matches |
| --- | ---: | ---: |
| darkhttpd |4|2/2|
| TCP ping-pong |8|4/4|
| mimalloc |4|2/2|
| jemalloc |4|1/2|
| Reference crypto (seven libraries) |28|14/14|
| TinyCC |4|2/2|
| GNU coreutils (seven programs) |28|14/14|

Thirty-nine of40 unstripped outputs exactly match canonical O2 bytes. Native jemalloc differs with observed generated LG_VADDR57 versus canonical48; [exact header diff](jemalloc/canonical-config.diff) and [limits](jemalloc/README.md) preserve that distinction without claiming exclusive causation. Both clean new native repeats match each other, and their independent stripping pair is preserved beside unchanged canonical bytes. No canonical byte identity is claimed for that native pair.

Exactly two independently initialized standard pinned workers verified the entire installed-package lock, after successful removal of both prior SQLite workers. Each profile resets private source/build/home/tmp/shared-memory workspaces and verifies frozen recipes/source archives. Independent clean builds and independent strips match; both repeats/forms pass package tests. All246 new measured commands exited successfully; source/output/census/map/raw-repeat hashes were independently verified. Native/QEMU distinction and cache limits remain in commands/receipts. Host CPU/kernel capabilities are recorded observations, not frozen by package locks; jemalloc's actual generated configuration difference remains visible.

Runtime records separate assertion results from HTTP/TCP/allocator transcript observations. Refcrypto executes32 KAT assertions plus RFC6234 driver70/35/105 pass counts. TinyCC compiles genuine target relocatable objects, links them with pinned target GCC, and executes hello/Fibonacci output. Coreutils tests version and true/echo/cat/wc/head/sort/sha256sum behaviors. These observations establish no source semantics, semantic equivalence, exhaustive test or Lean proof.

[container-pool-lifecycle.json](container-pool-lifecycle.json) records14 successful new profiles and successful removal of both workers. Containers are reused with clean independent workspaces, not newly initialized per profile. The next AArch64 BoringSSL pool only starts after documented successful cleanup, with exactly two separate workers and verified extended locks.

The same invocation hash-verifies and retains8 cJSON and8 SQLite O2 rows without a new execution claim; per-package retained reports preserve original lifecycle/test/receipt identities. In particular, historical cJSON receipts do not contain independent-repeat runtime fields; this report does not create or infer them. New80 plus retained16 give96 O2 rows across these nine projects. OpenSSL is a separate12-row pair tranche: [AArch64 #1065](https://github.com/hiloopai/silmaril-lean/pull/1065) and [native #1080](https://github.com/hiloopai/silmaril-lean/pull/1080), not rebuilt here. No additional unique-content count is inferred by summing canonical/variant rows.

All actual ELF bytes and included public licensed source inputs remain ordinary Git. Existing canonical/variant paths and hashes are unchanged. Public source under test remains distinct from owned recipes. Full local make check/exhaustive upstream tests were not run; CI remains required. Shared index/UI/DB/Lean ownership remains with integration.
