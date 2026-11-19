# Coreutils variant structural checks

All 112 delivered GNU coreutils 9.12 variants are whole-file parsed and
structurally decomposed: true, echo, cat, wc, head, sort and sha256sum;
x86_64/AArch64; O0/Og/O1/O3; stripped/unstripped. The actual GNU C programs
and ordinary Git ELF bytes are preserved.

Measured run `9a2968bc-fb57-4f83-93d5-942d68443687` passed all Decomp roots
with `lake build --wfail`: 1171.954 seconds wall, 4,388,736 KiB maximum child
RSS, two configured workers on CPUs 0–1. The receipt hashes every generated
Lean module and ELF input. This is structural evidence, not execution semantics.

With the eight additional cJSON O2 artifacts from the bounded build worker,
coverage is 208/416 delivered variants checked. New O2 rows remain unchecked.
No semantic statement or proof counts change in this tranche.
