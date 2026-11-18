# Actual x86 OpenSSL assembly-enabled O0 artifacts

Six actual OpenSSL3.5.9 x86_64 ASM ELF rows provide libcrypto/libssl/CLI at O0,
unstripped and stripped. Two clean workspace builds match bytes, as do the
independent stripping results. Both repeats and both stripping forms passed
recorded native crypto/signature/certificate/TLS1.3 handshake/verification and
application-transfer observations. These are public upstream inputs under test.

[summary.json](summary.json) maps exact hashes to receipts, static census and
source inventory. Verification independently checked all included source hashes,
six ELF/receipt/census/strip-map hashes, both repeats' runtime records and18
measured exits. First/repeat build wall seconds were 126.884/102.845.

The same original two independently initialized persistent containers are reused
with private source/build/temp/home/shared-memory workspaces reset each profile.
These are independent workspace repeats, not fresh-container repeats. Exact
image/package lock, sanitized environment, recipe/controller/lifecycle,
commands/logs and actual timings are retained.

The source inventory preserves 46 standalone assembly files and distinguishes
2 included C-family files with explicit volatile inline-asm syntax. Lexical
sites need not survive target preprocessing or execute. No compiler-emitted
assembly is labeled inlineasm. Generated assembly/perlasm provenance records
104 generator command lines with tool versions; available generators alone are
not claimed invoked. Exact compiler/linker commands remain in executed logs.

Existing canonical and no-asm bytes/paths, shared index/browser and Lean modules
are untouched. Census decoder gaps remain explicit. No full local `make check`,
exhaustive upstream test, semantic/formal or FIPS claim is made. CI remains
required; the other four x86 optimization levels are still running separately
and excluded from this tranche.
