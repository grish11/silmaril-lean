# Optimization and stripping variants

These are real ELF bytes in ordinary Git, built by
[`scripts/corpus/variants.py`](../../scripts/corpus/variants.py) from the canonical
packages' pinned archives. The original `corpus/elf` objects remain intact.
[`corpus/matrix.json`](../matrix.json) indexes only completed, hash-checked outputs.
It separates source/build identity from content hashes, and records the hierarchy
project → version components → source identity → configuration → target → compiler
and flags → stripping/artifact. Version components retain upstream's spelling;
date/commit versions are not asserted to be semantic versions.

Delivered inventory: **842 artifact rows, 707 distinct content hashes**. Rows
retain build identity even when bytes match. The 54 canonical rows remain intact;
the additional 788 rows include optimization, stripping, assembly, version and
configuration examples. Every indexed row has an artifact-specific census and
hash-bound receipt; these are static tool evidence, not semantic proofs.

| Project | Delivered rows | Distinct hashes |
|---|---:|---:|
| BoringSSL | 60 | 36 |
| cJSON | 44 | 40 |
| GNU coreutils | 154 | 140 |
| darkhttpd | 22 | 20 |
| jemalloc | 22 | 21 |
| mimalloc | 22 | 20 |
| OpenSSL | 126 | 98 |
| Reference crypto | 154 | 136 |
| SQLite | 172 | 144 |
| TCP pingpong | 44 | 32 |
| TinyCC | 22 | 20 |

All listed families have actual x86_64 and AArch64 outputs. Original releases
have O0/Og/O1/O2/O3 examples and stripping pairs. OpenSSL 3.5.9 has both no-asm
and assembly-enabled profiles across these five levels on both targets; its
60 assembly-enabled rows have 60 distinct hashes. No-asm canonical O2 rows and
repeat-build O2 rows remain distinct observations when their bytes match.

SQLite 3.46.1, 3.50.4 and 3.54.1 have actual default, small and fts5-rtree
profiles at O0/O2 on both targets, each with library/CLI stripping pairs.
The original 3.54.1 default also has Og/O1/O3. These additional version/config
profiles are representative: Og/O1/O3 for the other combinations are not built.

The pinned BoringSSL revision has no-asm and asm O0/O2 library/CLI pairs on both
targets, plus actual FIPS_SHARED O0 outputs (including bcm.o and Go execution).
These are research artifacts, **not FIPS certification**. Native GCC 14 FIPS O2
failed the upstream guard and produced no artifact; AArch64 FIPS O2 was not
attempted. No retries or Clang extension are claimed. Og/O1/O3 are not built.
Supplementary non-FIPS `ld -r` ET_REL is not counted as a library/executable row.

Native jemalloc O2 records LG_VADDR=57 and a different image ID from the canonical
LG_VADDR=48 build. Treat these as distinct observed configurations; the record
establishes neither the cause of byte differences nor semantic equivalence.

Each profile directory has:

- `build.json`: archive identities, exact image/recipe hashes, source-input paths and
  hashes, generated inputs, environment, licence, run ID and precise proof status;
- `unstripped/` and `stripped/`: ELF outputs, SHA256SUMS and measured receipts;
- `<object>.pair.json`: all executable sections' byte hashes, addresses and sizes
  compared across this exact stripping pair; original nonzero function symbols;
- `runs/`: measured stages, including two clean builds, stripping, pair checks,
  runtime tests and receipt extraction;
- `logs/`: complete command logs compressed with deterministic gzip headers;
- optional `upstream/` and `generated/`: additional exact upstream inputs and
  configuration-generated inputs. Unchanged upstream files reference the existing
  canonical source paths rather than duplicating them.

The original runner used two fresh build containers. Later receipts use an
exactly two-worker persistent pool, with independent reset source/build workspaces,
sanitized environments and package/image locks. Their receipts explicitly record
container reuse; they do not claim fresh containers. Each worker was configured
for 3 CPUs/12 GiB with a read-only root. See the individual run's isolation and
cache observations rather than inferring enforcement from requested settings.
Historical cJSON receipts tested the first repeat and stripping forms; later
profiles test both repeats and both forms. No missing historical test is inferred.
Repeat byte identity and stripping checks are reproducibility evidence.

```sh
corpus/toolchain/image.sh
python3 scripts/corpus/variants.py --work /work/out/variant-builds
# Or a selected tranche:
python3 scripts/corpus/variants.py --package cjson --arch aarch64 --level O1 \
  --work /work/out/variant-builds --resume
python3 scripts/corpus/matrix.py --output corpus/matrix.json
```

The original runner defaults cover the original ten packages and O0/Og/O1/O3;
separate pinned profile recipes provide the additional O2, assembly, BoringSSL and
SQLite version/configuration outputs. Existing completed profiles are not
overwritten. Resume verifies hashes without claiming another build repetition.

All 54 canonical whole files have checked Lean parsing and structural
decomposition. The variant receipt registry contains 227 checks; this does not
cover every delivered variant. See [variant-lean](../measurements/variant-lean/README.md).
There are nine scalar contextual C/Core/ELF statements, one separate experimental
memory/global statement, and six binary-equivalence statements. **Semantic proofs:
zero.** Their exact assumptions and scope are in the
[formal registry](../measurements/formal-functions/README.md). Stripped address
maps, same-name symbols, matching hashes and structural checks do not establish
source-semantic equivalence. The compiler explorer's 16 fixtures are selected
examples, not a corpus-wide function mapping or interactive compilation service.

The architecture follow-ups remain [RISC-V64 #1022](https://github.com/hiloopai/silmaril-lean/issues/1022)
and [ARM32/Thumb #1023](https://github.com/hiloopai/silmaril-lean/issues/1023).
The latter is separate from delivered AArch64 support.

These inputs and outputs are [software under test](../UNDER-TEST.md). Owned build
scripts and local helpers retain normal code scanning; no findings are dismissed
or scans disabled by this representation.

Acquisition fallback: exact pinned TinyCC/coreutils archive, signature and keyring hashes
were validated from a public mirror after upstream connection timeouts. The acquisition
records are in `corpus/measurements/matrix-remainder/`. Resume validates published hashes
and preserves the original clean-build measurements; it does not claim new repetitions.
