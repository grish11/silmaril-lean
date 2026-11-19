# Actual AArch64 OpenSSL assembly O1/O2 builds

This tranche adds 12 actual OpenSSL 3.5.9 AArch64 assembly-enabled ELF rows:
libcrypto/libssl/CLI at O1 and O2, unstripped and stripped. The paired independent
build outputs and independently stripped outputs match bytes. Both repeats and
both stripping forms passed recorded hash/AES/signature/certificate/TLS1.3
observations under the pinned QEMU. These are public upstream sources under test.

[summary.json](summary.json) maps every ELF to its exact hash, receipt, static
census and source inventory. Each profile retains paired executable-section and
address stripping maps, successful measured commands/timings, generated standalone
.S, public generator inputs and actual perlasm/compiler commands. The included C
source with explicit volatile inline-asm syntax is distinguished in the hash-checked
source inventories; lexical sites are not assumed active after preprocessing.

| Optimization | First build wall seconds | Independent repeat wall seconds | ELF rows |
| --- | ---: | ---: | ---: |
| O1 | 143.543 | 120.306 | 6 |
| O2 | 166.136 | 141.669 | 6 |

Validation independently checked all included source hashes, all 12 ELF hashes
against receipts/census/strip maps, both repeats' runtime records and all 36
measured command exit codes. Both profiles reused the original two independently
initialized persistent workers, resetting private source/build/temp/home/shared
memory workspaces. These are clean workspace repeats, not new containers per
profile. The exact image, whole package lock, sanitized environment, recipe and
controller identities remain in receipts. Earlier lifecycle reconnection is
recorded without claiming another build or replacement worker.

Existing paths/hashes, shared indexes, Lean modules and registry are unchanged.
Static census decoder gaps remain explicit. Runtime observations are not
exhaustive upstream tests, source semantics, formal equivalence or FIPS evidence.
Full local `make check` was not run; CI remains required. Remaining profiles are
still building separately and are excluded from this tranche.
