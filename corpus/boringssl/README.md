# Representative BoringSSL / BoringCrypto (BCM) is `crypto/fipsmodule` in that same tree. All configurations here are research builds without FIPS validation or certification.

Builds use upstream CMake/Ninja targets `crypto`, `ssl`, `bssl`, with a separately pinned [toolchain extension](../toolchain/boringssl/README.md). Both independent workers compare the complete extended package lock and recompute the Go tree/tool executable inventory before compiling. Release flags explicitly select the requested optimization and `-g0 -DNDEBUG`, replacing CMake's default optimization. Upstream also adds its own options: in particular GNU assembly compilation uses `-Wa,-g`, so unstripped assembly profiles can contain assembly debug metadata despite C/C++ `-g0`. Exact commands are retained rather than claiming debug-free assembly.

`no-asm` sets `OPENSSL_NO_ASM=ON`; `asm` enables upstream assembly. `fips-shared` sets `FIPS=ON` and `BUILD_SHARED_LIBS=ON`: upstream selects FIPS_SHARED, creates its genuine `bcm.o` with `fips_shared.lds`, and runs the pinned Go integrity-hash tool on libcrypto. The module and intermediate archive are preserved. This configuration does not establish validation, certification, or an approved cryptographic operating environment.

For ordinary non-FIPS configurations, the supplementary `boringcrypto-bcm.o` combines the actual upstream `fipsmodule` object-library objects using our explicit `ld -r` packaging command. Upstream links the original objects directly; the combined object is not falsely presented as upstream's FIPS_SHARED module. It is ET_REL, preserved unstripped with relocation/unresolved-symbol reports; both repeats must match. Linked libraries and CLI receive independent stripping comparisons and runtime observations.

Committed `gen/*.S` are upstream pregenerated compiler inputs, consumed verbatim. We preserve actual compiler dependencies, public perlasm/pregeneration/Go tooling sources, source-list manifests and licenses. No local perlasm regeneration is claimed. The FIPS_SHARED Go integrity invocation is recorded separately from pregenerated assembly. `configure-command.json`, verbose build log, `compile_commands.json`, CMake cache, Ninja build graph/commands/dependencies record actual selections and execution. Go uses local-only toolchain and disabled module network access, with fresh private cache directories per profile.

Smoke tests use the actual shared libraries for SHA-256/AES known answers,
Ed25519 signature acceptance/rejection, certificate signatures and a TLS 1.3
handshake/application transfer over a BIO pair. The CLI runs its sha256sum and
cipher enumeration commands. AArch64 runs under the pinned QEMU. These are
specific observations, not exhaustive upstream tests, semantic proofs or FIPS
validation. The TLS test checks a certificate signature separately; it does not
exercise certificate-chain/path validation or network I/O.

```sh
corpus/toolchain/image.sh
bash corpus/toolchain/boringssl/image.sh /work/out/boringssl-toolchain
python3 scripts/corpus/variants.py --package boringssl --configuration no-asm \
  --configuration asm --level O2 --work /work/out/boringssl-pool
```

Only completed variant receipts count as delivered artifacts. This recipe and
source selection alone do not assert that a profile has been built.
