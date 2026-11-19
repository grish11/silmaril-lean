# Actual x86 OpenSSL no-asm O2 stripping pairs

Six actual OpenSSL3.5.9 x86_64 ELF rows add independent O2 unstripped/stripped
builds for libcrypto/libssl/CLI. Both clean builds match bytes; both independent
strips match bytes. Both repeats and both stripping forms pass recorded native
crypto/signature/certificate/TLS1.3 handshake/verification/application-transfer
observations. The three unstripped outputs also match canonical ELF bytes exactly:
see the profile's `canonical-comparison.json`. Canonical bytes/paths are unchanged;
these repeated rows are not three additional unique unstripped hashes.

[summary.json](summary.json) maps exact ELF hashes, receipts, paired executable
section/address maps, independent static census and source inventory. Included
source hashes, six ELF/receipt/census/strip-map hashes, both repeats' runtime
records and18 measured exits were independently checked. First/repeat build wall
seconds: 143.164/121.650.

The same original two independently initialized persistent containers are reused,
resetting private source/build/temp/home/shared memory workspaces. These are clean
workspace repeats, not fresh-container repeats. Exact image/package locks, recipe,
environment/controller lifecycle, commands, logs and measurements are retained.
Static census decoder gaps and lexical source-assembly limits remain explicit.
These are public upstream sources under test. Shared indexes/browser and Lean
modules are untouched. No full local `make check`, exhaustive upstream test,
source-semantic, Lean, functional-equivalence or FIPS claim is made. CI remains
required; x86 assembly-enabled builds are still running and excluded.
