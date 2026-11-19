# Canonical OpenSSL whole-file checks

The x86_64 and AArch64 `libssl.so.3` reader bodies are split into bounded chunks
and assembled into whole-file parse theorems. Both `Decomp` roots passed
`lake build --wfail` in run `1d4a29de-011e-49b5-8852-c720993a7962`:
620.983 seconds wall, 6,633,060 KiB maximum child RSS, two configured workers.
The receipt binds all generated Lean modules and both ELF inputs by SHA256.

Canonical coverage is 52/54 whole-file parses with structural decomposition.
The two libcrypto files still have checked layout and structural decomposition only.

The canonical AArch64 openssl executable also passed bounded-window whole-file
parsing and its Decomp root in run `aee658e7-2ee9-4b26-998f-0e30daac4381`.
The successful exact-input receipt is included below runs/. It measures the
reader/decomposition Lean build with dependencies warm, generated targets cold
or invalidated; it excludes artifact acquisition and container builds. These checks establish no execution semantics,
instruction-decoding correctness, control-flow correctness or semantic proofs.
