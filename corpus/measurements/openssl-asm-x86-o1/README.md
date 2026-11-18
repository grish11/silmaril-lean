# Actual native OpenSSL ASM O1 artifacts

Six actual OpenSSL3.5.9 x86_64 assembly-enabled ELF rows provide libcrypto/libssl/CLI
at O1, unstripped and stripped. Independent clean workspace builds and independently
stripped outputs match bytes. Both repeats and both forms passed recorded native
crypto/signature/certificate/TLS1.3 handshake/verification/application-transfer
observations. These are public upstream sources under test.

[summary.json](summary.json) maps exact hashes to receipts, census, stripping maps
and source inventory. All included source hashes, six ELF/receipt/census/pair
hashes, both repeats' runtime records and18 measured exits were independently
checked. First/repeat build wall seconds: 132.836/109.546.

Generated standalone assembly, public perlasm/configuration inputs and actual
commands/tool versions/logs are preserved. The hash-checked source inventory
distinguishes 46 standalone assembly files from 2 C-family files with explicit
volatile inline-asm syntax. Lexical source inclusion need not survive target
preprocessing or execute; compiler-emitted assembly is not labeled C inlineasm.
Available generators are not all claimed invoked; use actual executed logs.

Same original two independently initialized persistent workers, private clean
source/build/temp/home/shared-memory workspaces per profile; not fresh-container
repeats. Image/package lock, environment, recipe/controller/lifecycle and actual
timings remain in receipts. Existing canonical/historical bytes, shared indexes,
browser and Lean modules are unchanged. Static census decoder gaps remain explicit.
No full local make check, exhaustive upstream test, source-semantic/formal or FIPS
claim. CI remains required; other optimization levels are excluded here.
