# Actual native OpenSSL ASM O3 artifacts

Six actual OpenSSL3.5.9 x86_64 assembly-enabled ELF rows provide libcrypto/libssl/CLI
at O3, unstripped and stripped. Independent clean workspace builds and independent
strips match bytes. Both repeats and both forms passed recorded native
crypto/signature/certificate/TLS1.3 handshake/verification/application-transfer
observations. These are public upstream inputs under test.

[summary.json](summary.json) maps exact hashes to receipts, census, stripping maps
and source inventory. All included source hashes, six ELF/receipt/census/pair
hashes, both repeats' runtime records and18 measured exits were independently
checked. First/repeat build wall seconds: 161.371/134.175.

Generated standalone.S, public perlasm/configuration inputs, actual command/tool
versions/logs and the separate C volatile-inlineasm lexical inventory are included.
Available generators are not all claimed invoked; syntax is not assumed active
after preprocessing. Compiler-emitted assembly is not labeled C inlineasm.
Same original two independently initialized persistent workers reset private clean
source/build/temp/home/shared-memory workspaces; not fresh-container repeats.
Image/package lock, environment, recipe/controller/lifecycle and timings remain in
receipts. Existing canonical/historical bytes and shared indexes/browser/Lean
modules are unchanged. Census decoder gaps remain explicit. No full local make
check, exhaustive upstream test, source-semantic/formal/FIPS claim. CI required.
