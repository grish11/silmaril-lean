# Jemalloc variant structural checks

All sixteen delivered jemalloc 5.3.0 variants are whole-file parsed and
structurally decomposed: x86_64 and AArch64, O0/Og/O1/O3, stripped and
unstripped. This checks actual Git ELF bytes, not planned builds.

Run `38f1b22f-76d5-4130-a722-10614aab940d` built all sixteen Decomp roots
with `lake build --wfail`: 1290.541 seconds wall, 6,517,996 KiB maximum
child RSS, two configured workers on CPUs 0–1. Dependency caches were
reused; the receipt's cache label is unspecified, so this is not a cold
baseline. Input/module hashes were revalidated before registration.

The checked variant registry now contains 227 entries. These checks
establish parsing and structural tiling, not instruction semantics,
allocator behavior, source correspondence or function equivalence.
