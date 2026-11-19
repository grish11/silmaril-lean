# Actual native BoringSSL FIPS_SHARED O0 research artifacts

Six actual BoringSSL native x86_64 FIPS_SHARED O0 ELF rows provide libcrypto/libssl/bssl,
unstripped and stripped, at upstream commit ebd922adc708a48b0cccfcdf81e854a3fdc1b7b6.
Upstream FIPS=ON and BUILD_SHARED_LIBS=ON select its actual FIPS_SHARED branch.
The genuine upstream `bcm.o` and `libbcm_library.a` are preserved separately; the
actual Go integrity-injection command on libcrypto.so is retained in executed
Ninja logs. This differs from repository ld-r packaging in non-FIPS profiles.
BoringCrypto remains crypto/fipsmodule in this same checkout, not a new upstream.

Independent build/strip/module/archive/provenance byte comparisons passed. Both
repeats and forms passed SHA256/AES, Ed25519 acceptance/rejection, certificate
signature/TLS1.3 BIO handshake/application transfer and bssl observations.
Runtime FIPS_mode=1 identifies this compiled configuration only. **These are
research builds with no FIPS validation or certification claim.** Module artifacts
stay unstripped and are not executable/shared-library stripping rows; no standalone
module-runtime or strip-all linkability claim is made.

[summary.json](summary.json) maps hashes/receipts/census/strip maps/supplementary
artifacts, source inventories and actual timings. All included sources, all ELF,
module/archive/provenance hashes, both repeats runtime records and18 measured exits
were independently checked. First/repeat wall seconds: 65.718/50.102.

Same two independently initialized persistent extended-image workers, private
source/build/temp/home/shared-memory resets; reused containers, not new per profile.
Both verified220-package/tool/15659-file Go-tree locks. Local-only Go toolchain,
disabled module network access and new private Go cache per profile are recorded.
Public pregenerated assembly, source/generator inputs and licenses are preserved;
local Go integrity execution is separate from pregenerated upstream perlasm output.
C inlineasm remains lexical syntax with preprocessing/execution limits.

The subsequent GCC14 O2 FIPS_SHARED attempt failed upstream's linker guard against
referenced discarded data.rel.ro.local sections. No O2 artifact is counted, no
linker/integrity guard was changed, and no validation/certification is inferred from
O0 success. [Failure evidence](../boringssl-fips-o2-failure/README.md) records the
failed build and successful worker cleanup. No original paths/hashes, shared
indexes/UI/DB/Lean modules changed. No full local make check, exhaustive upstream
test, source-semantic/formal equivalence claim; CI remains required.
