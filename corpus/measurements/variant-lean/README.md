# Measured variant Lean checks

Two real cJSON 1.7.19 x86_64 O0 libcjson_utils variants (stripped and unstripped) have whole-file ELF parse and structural decomposition checks. `checks.json` binds exact artifact and generated-module hashes to the successful run receipt. The matrix rejects stale module hashes.

The same run checked the canonical x86_64 OpenSSL CLI whole-file parse using bounded symbol and relocation table chunks. This brings canonical whole-file parses to 49 of 54; five large OpenSSL files still have only checked layouts/decompositions. On the integrated 408-variant catalog, eighteen are checked and 390 remain unchecked. Four additional mimalloc 2.1.9 x86_64 O0/O3 stripped/unstripped roots passed in run 5fcdcf3d-5ad3-4453-b5ca-004f9a46abb1; its receipt and module hashes are retained alongside the first cJSON checks.

Run 1448c969-1ac0-43ae-845a-b92fe332cda5: 210.215 s wall, 379.35 s user CPU, 46.31 s system CPU, 4,085,804 KiB maximum child RSS; two Lean workers. Includes dependency work and warm caches; not a clean isolated elaboration benchmark. The receipt records inputs, toolchain and command. An earlier monolithic attempt was stopped and is not a successful measurement.

These are structural proofs, not instruction semantics, translation validation, or functional equivalence. The separate [formal function inventory](../formal-functions/README.md) contains one stated, unproved binary-equivalence problem; C-to-ELF remains uninstantiated. Stripped decompositions use retained symbols and gaps; external paired symbol maps do not become Lean-proved symbols.

All sixteen delivered mimalloc variants (both x86_64/AArch64, all O0/Og/O1/O3, stripped/unstripped) now have whole-file parse and structural decomposition checks. Run841dc4be-d3eb-4cf1-94b5-f8d932668972 checked all16 roots: twelve newly generated roots, four previously checked/cached. Original receipts for the earlier four are retained. AArch64 checks make no ISA semantics or contextual TV/equivalence claim.
