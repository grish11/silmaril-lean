# Actual native OpenSSL ASM O2 artifacts

Six actual OpenSSL3.5.9 x86_64 assembly-enabled ELF rows provide libcrypto/libssl/CLI
at O2, unstripped and stripped. Independent clean workspace builds and independent
strips match bytes. Both repeats and both forms passed recorded native
crypto/signature/certificate/TLS1.3 handshake/verification/application-transfer
observations. These are public upstream inputs under test.

[summary.json](summary.json) maps exact hashes to receipts, census, stripping maps
and source inventory. All included source hashes, six ELF/receipt/census/pair
hashes, both repeats' runtime records and18 measured exits were independently
checked. First/repeat build wall seconds: 151.716/129.609.

Generated standalone.S, public perlasm/configuration inputs, actual command/tool
versions/logs and the separate C volatile-inlineasm lexical inventory are included.
Available generators are not all claimed invoked, and source syntax is not assumed
active after preprocessing. Compiler-emitted assembly is not labeled inlineasm.
Same original two independently initialized persistent workers reset private clean
source/build/temp/home/shared-memory workspaces; not fresh-container repeats.
Image/package lock, environment, recipe/controller/lifecycle and timings remain in
receipts. Existing canonical/historical bytes and shared indexes/browser/Lean
modules are unchanged. Census decoder gaps remain explicit. No full local make
check, exhaustive upstream test, source-semantic/formal/FIPS claim. CI required.

[Configuration comparison](configuration-comparison.json) gives exact hashes and
sizes for populated native O2 no-asm/asm configurations at equal upstream version,
target and compiler. File sizes imply no performance or equivalence result.

| O2 object | no-asm bytes | asm bytes |
| --- | ---: | ---: |
| libcrypto.so.3 | 5585688 | 6889888 |
| libssl.so.3 | 1216856 | 1216880 |
| openssl | 1223152 | 1223152 |
