# Actual AArch64 OpenSSL assembly-enabled builds

Two completed OpenSSL 3.5.9 configurations add **12 actual ELF rows**: O0 and Og,
AArch64, libcrypto/libssl/CLI, each unstripped and stripped. These are public
upstream inputs under test. Existing canonical/no-asm paths and hashes are kept.
The upstream release archive is pinned in each build receipt.

[summary.json](summary.json) identifies exact ELF hashes, receipt and independent
census paths, source inventory and actual timings. Both repeats and both
independently stripped forms passed SHA-2/SHA-3/BLAKE2, AES known-answer/roundtrip,
Ed25519, certificate and TLS 1.3 handshake/verification/application-transfer
observations under the pinned QEMU. Both original and stripped repeat pairs
matched bytes. Executable section/address maps remain with each profile.

| Optimization | First build wall seconds | Independent repeat wall seconds | ELF rows |
| --- | ---: | ---: | ---: |
| O0 | 125.773 | 102.812 | 6 |
| Og | 133.545 | 111.137 | 6 |

The same two independently initialized persistent containers are reused. Each
profile resets private source/build/temp/home/shared-memory workspaces; sanitized
commands use the verified original image and complete package lock. These are
independent clean workspace repeats, not new containers per profile. Lifecycle,
recipe/controller identities, measured commands and logs accompany the artifacts.
The earlier controller reconnection is recorded honestly in lifecycle receipts.

Each profile preserves 30 standalone assembler source files separately from the
included C-family file with explicit volatile inline-asm syntax. See
[source-assembly-O0.json](source-assembly-O0.json) and
[source-assembly-Og.json](source-assembly-Og.json): sources are hash checked, and
lexical sites are not assumed to survive preprocessing. No compiler-emitted
assembly is labeled C inline assembly. The profile's generated
`assembly-provenance.json` distinguishes available generator inputs, actual
recorded perlasm commands and generated `.S`; generator availability alone is not
claimed execution. Exact compiler and perlasm invocations are in build logs.

Validation of this tranche independently checked all included source hashes,
12 ELF hashes against receipts/census/strip maps, both repeats' runtime results,
and all 36 measured command exit codes. Static census reports retain decoder
gaps and their limits. No source-semantic, functional-equivalence, Lean-proof or
FIPS claim is made. Shared indexes and the Lean registry are not modified.
The remaining optimization/platform builds continue separately and are not
counted here. Full local `make check` was not run; CI remains required.
