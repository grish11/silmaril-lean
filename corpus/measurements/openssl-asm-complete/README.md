# Complete actual OpenSSL assembly artifact matrix

OpenSSL3.5.9 ASM now has60 actual ELF rows: two targets (AArch64/x86_64), five
optimization levels (O0/Og/O1/O2/O3), three objects (libcrypto/libssl/CLI), two
stripping forms. [matrix.json](matrix.json) identifies all exact hashes, receipts,
census and30 stripping pairs. Every ELF/receipt/census/pair hash and both repeats'
recorded runtime results was rechecked. Prior tranche rows are not new work.

The final native O1/O2/O3 tranche contributes18 rows; earlier x86 O0/Og and
AArch64 tranches provide the other42. Exact sources/generators/.S, C volatile-asm
lexical inventories, flags/commands/tool versions, measurements and reused-pool
lifecycle remain with each build. These are independent clean workspace repeats
in the original two independently initialized persistent workers, not new
containers per profile. Canonical and no-asm paths/hashes are unchanged.

Static census decoder coverage/gaps and observation/formal boundaries remain
explicit. These are public upstream inputs under test. No full local make check,
exhaustive upstream testing, source semantics, Lean proof, functional equivalence
or FIPS validation is claimed. Shared index/browser and Lean modules are untouched;
CI and normal integration remain required.

[Completed pool lifecycle](container-pool-lifecycle.json) records all16 successful profiles (including no-asm followups), the same2 independently initialized workers, explicit controller reconnection and both successful removals. Both installed-package inventories match the standard complete lock. No per-profile container replacement or new-container repeat is claimed.
