# Complete actual AArch64 OpenSSL ASM matrix

This final tranche adds six actual OpenSSL 3.5.9 AArch64 assembly-enabled O3 ELF
rows: libcrypto/libssl/CLI, unstripped and stripped. Together with the prior
O0/Og and O1/O2 tranches, all five requested optimization levels now have real
artifacts on AArch64 in both stripping forms:30 rows. The
[complete matrix](complete-aarch64-asm-matrix.json) identifies every existing
output hash and receipt; this does not count the prior24 rows as new work.

[summary.json](summary.json) records this tranche's exact hashes/census/source
inventories and actual timings. O3 first/repeat build wall seconds were
171.481/146.772.
Both independently built and independently stripped pairs match bytes. Both
repeats and both forms passed recorded crypto/signature/certificate/TLS1.3
observations under pinned QEMU. Verification checked all included source hashes,
six new ELF/receipt/census/strip-map hashes, runtime records and18 successful
measured command exits; the complete matrix's30 ELF hashes were rechecked.

The same two independently initialized persistent workers reset private clean
source/build/temp/home/shared-memory workspaces. These are not fresh-container
repeats. Exact image/package lock/environment/recipe/controller lifecycle and
perlasm/assembler/compiler command evidence remains with each profile. Generated
standalone .S and public generator inputs are preserved separately from the
hash-checked lexical C volatile-asm inventory; syntax does not establish active
preprocessing or execution. Compiler-emitted assembly is not labeled inlineasm.

For a concrete populated configuration comparison, these unstripped O2 files use
the same upstream version, target, compiler and optimization. Exact hashes are in
[configuration-comparison.json](configuration-comparison.json). Sizes do not
establish performance or equivalence.

| O2 object | no-asm bytes | asm bytes |
| --- | ---: | ---: |
| libcrypto.so.3 | 5645872 | 6510832 |
| libssl.so.3 | 1195528 | 1195528 |
| openssl | 1249792 | 1249792 |

Shared indexes/browser/Lean modules and historical bytes remain untouched. Static
census decoder gaps remain explicit. No exhaustive upstream testing, source
semantics, Lean proof, functional equivalence or FIPS validation is claimed.
Full local `make check` was not run; CI remains required. x86 profiles are still
building separately and are excluded from this completion claim.
