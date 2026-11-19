# Actual pinned BoringSSL / BCM native no-asm O0 artifacts

Six actual ELF rows provide upstream BoringSSL libcrypto/libssl/bssl at pinned
commit [`ebd922adc708a48b0cccfcdf81e854a3fdc1b7b6`](https://github.com/google/boringssl/tree/ebd922adc708a48b0cccfcdf81e854a3fdc1b7b6),
native x86_64, no-asm, O0, unstripped and stripped. The exact public source archive
SHA256 is75ee588268ae3d7552f5be7e0849bdcc8e4159f22547dbfb4aae997784fdd345.
These are upstream public inputs under test; repository tools/smoke tests are
separate. Included sources retain upstream license notices and LICENSE.

Independent clean builds and independent strips match bytes. Both repeats and
both stripping forms passed SHA256/AES known answers, Ed25519 acceptance/rejection,
certificate signatures, an actual TLS1.3 BIO handshake/application transfer, bssl
SHA256 and cipher enumeration. Runtime FIPS_mode returned0. The TLS observation
checks a certificate signature separately; it does not exercise chain/path
validation or network I/O. No FIPS validation/certification is claimed.

The supplementary `boringcrypto-bcm.o` is ET_REL, preserving the actual upstream
CMake `fipsmodule` object boundary via an explicitly repository-authored ld-r
packaging step. It matches its independent repeat, with relocation and undefined
symbol reports. Upstream links those original objects directly. This is not
upstream FIPS_SHARED bcm.o or a separately invented BoringCrypto upstream. The
module stays unstripped, is not counted among the six executable/shared-library
rows, and has no standalone runtime or strip-all linkability claim.

The build uses upstream CMake/Ninja targets and the separately pinned extended
image80149c077dcc11f2063158a39721652a4039f5afabfcda4303715160345a8f2b.
Both independently initialized workers verified the complete220-package lock,
including all210 unchanged base versions, tool executable hashes and the15659-file
Go tree. This first profile used the newly initialized pair; subsequent profiles
reuse them with clean private workspaces. No per-profile fresh-container claim.
Sanitized environment, exact commands/flags/source/recipe/tool/image/lifecycle and
measurements are retained with the receipts.

[summary.json](summary.json) maps all ELF/receipt/census/strip-map and supplementary
hashes. Verification checked1181 included source files, all outputs/provenance,
both repeats' runtime records and18 successful measured commands. First/repeat
build wall seconds were 58.522/42.702.
The [source inventory](source-assembly.json) distinguishes151 available upstream
pregenerated standalone assembly files from7 C-family files with explicit volatile
inline-asm syntax. These are conservative preserved provenance: **no-asm compiles
no upstream assembly source lists**, no local perlasm generation is claimed, and
lexical syntax is not assumed to survive preprocessing or execute. Compile/Ninja
commands/dependencies/logs record actual target inputs. Compiler-emitted assembly
is not mislabeled inlineasm.

Existing artifact paths/hashes, shared indexes/browser and Lean modules are
unchanged. Static census decoder coverage/gaps remain explicit. No full local make
check, exhaustive upstream testing, source semantics, Lean proof or functional
equivalence claim. CI remains required. Other configurations/levels/targets are
not counted from this first profile; FIPS_SHARED remains separate research work.
