# Actual delivered BoringSSL and BoringCrypto configurations

This pinned upstream checkout provides60 actual executable/shared-library ELF rows,36 unique hashes and30 stripping pairs in10 successful profiles. [artifacts.csv](artifacts.csv) maps source commit → configuration → target/compiler/flags → optimization → stripping → exact artifact/receipt/census/pair hashes. [summary.json](summary.json) links every build and records actual source-hash checks, successful measured commands and independent repeat times. Existing source/ELF bytes are not rewritten by this report.

| Configuration | Level | Native x86_64 rows | AArch64 rows (QEMU tests) |
| --- | --- | ---: | ---: |
| no-asm |O0|6|6|
| no-asm |O2|6|6|
| asm |O0|6|6|
| asm |O2|6|6|
| FIPS_SHARED |O0|6|6|

Each successful cell contains libcrypto/libssl/bssl unstripped/stripped. Identical libssl/CLI bytes across configurations are counted as separate configuration rows but once as unique bytes. All180 measured commands exited successfully. Independently initialized persistent workers, clean private workspaces and independent raw builds/strips establish measured reproducibility; both repeats/forms pass SHA/AES, Ed25519 rejection, certificate/TLS1.3 BIO transfer and CLI observations. Native and QEMU observations remain distinct. Static census decoding gaps are explicit; neither runtime nor census proves semantics or equivalence.

BoringCrypto is upstream crypto/fipsmodule, not fabricated separate upstream. FIPS_SHARED O0 preserves actual upstream bcm.o/archive and executed Go integrity injection. Non-FIPS profiles preserve repository ld-r packaging of genuine upstream fipsmodule objects, explicitly distinguished from FIPS_SHARED. Supplementary ET_REL/archive artifacts remain unstripped, outside the60 executable/library rows. FIPS_mode=1 describes a compiled research configuration, **not FIPS validation/certification**.

Public source commit ebd922adc708a48b0cccfcdf81e854a3fdc1b7b6/archive75ee588268ae3d7552f5be7e0849bdcc8e4159f22547dbfb4aae997784fdd345 and licenses are included. Public upstream sources under test remain distinct from repository-owned recipes. Upstream committed pregenerated assembly, generators, actual compiler inputs and lexical C inlineasm inventories remain separate; no local perlasm regeneration or compiler-emitted assembly-as-inlineasm claim. Both workers verify immutable extended image80149.../220-package/tool/15659-file Go-tree inventories; CPU/kernel/page-cache capabilities are not frozen by package locks.

Native FIPS_SHARED GCC14 O2 is [actually failed/unsupported](../boringssl-fips-o2-failure/README.md): upstream guard rejects referenced discarded data.rel.ro.local. It has no artifact/repeat/strip/runtime-success claim and is not retried. AArch64 FIPS_SHARED O2 was deliberately not selected; no failed AArch64 attempt is claimed. No linker/integrity guard or compiler substitution was used. This representative selection does not claim all optimization levels, all upstream tests, other upstream versions, FIPS validation, source semantics, formal equivalence or Lean proofs. Full local make check was not run. Shared indexes/UI/DB/Lean remain with integration.
