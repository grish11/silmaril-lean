# Actual corpus metadata database generation baseline

`database.py` generated the actual 106-artifact catalog, with 45,681 function
mapping rows and measured-stage receipts, in **1.165 s wall**, 0.950 s user CPU,
0.200 s system CPU, **72,580 KiB peak RSS**. Exit status 0; SQLite quick_check passed.
This is one sequential run with unspecified cache state, not a cold/warm comparison.

The [run receipt](runs/b2aa9a8a-36ad-4eba-8b7e-604844b8a9ce.json) records the actual
command, input/script hashes, repository state, pinned Lean version (not executed
by this stage), runner and measurements. The output is generated from completed
Git ELF artifacts and their receipts; it contains metadata, not ELF byte blobs.

This stage includes hashing/validating those ELF inputs, reading corpus metadata,
function mappings and stage receipts, and SQLite insertion. It excludes acquisition,
C compilation, Lean parsing/decomposition/kernel checks, canonical project export,
and semantic problem/proof generation. It is not an end-to-end pipeline timing.

Reproduction and browser checks: [scripts/corpus/README.md](../../../scripts/corpus/README.md).

## Expanded catalog run

The 246-artifact catalog (240 distinct content hashes, 48,723 function mapping
rows) generated in **1.843 s wall**, 1.550 s user CPU, 0.260 s system CPU and
**73,780 KiB peak RSS**. Exit status 0 and SQLite quick_check passed. The
[run receipt](runs/4b5b16c7-3115-4761-80f0-3eb29cce6491.json) records this runner,
commands, input hashes and unspecified cache state. This single run has the same
stage boundaries as above; differing runners/inputs make the two runs unsuitable
for a regression claim. Catalog generation ingests per-run measurement records,
including prior database-generation runs, without mutating or merging writers.
