# Optimization and stripping variants

These are real ELF bytes in ordinary Git, built by
[`scripts/corpus/variants.py`](../../scripts/corpus/variants.py) from the canonical
packages' pinned archives. The original `corpus/elf` objects remain intact.
[`corpus/matrix.json`](../matrix.json) indexes only completed, hash-checked outputs.
It separates source/build identity from content hashes, and records the hierarchy
project → version components → source identity → configuration → target → compiler
and flags → stripping/artifact. Version components retain upstream's spelling;
date/commit versions are not asserted to be semantic versions.

Delivered inventory: **462 artifact rows** (54 canonical O2 and 408 variants;
456 distinct content hashes). The following completed matrix covers both
`x86_64-linux-gnu` and `aarch64-linux-gnu`, all O0/Og/O1/O3 levels, and both
unstripped and stripped outputs:

| Project | Objects per target/profile | Variant ELF rows |
|---|---:|---:|
| cJSON | 2 | 32 |
| darkhttpd | 1 | 16 |
| TCP pingpong | 2 | 32 |
| Reference crypto | 7 | 112 |
| mimalloc | 1 | 16 |
| jemalloc | 1 | 16 |
| TinyCC | 1 | 16 |
| GNU coreutils | 7 | 112 |
| SQLite | 2 | 32 |

OpenSSL no-asm additionally has 24 x86_64 variants across all four levels and both
stripping states. Its 24 AArch64 variants remain unbuilt: Docker container initialization
failed with the session-keyring quota error before the first build began.
All 408 delivered variants have [artifact-specific static census reports](../census/variants/),
including decoder byte accounting and exact receipt identities; these are separate
from the formal stages listed below.

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

The runner uses an exact image ID, two genuinely fresh build containers and an
8 CPU / 32 GiB task budget. For this continuation, an external watcher
restricted build processes to six CPU cores, leaving two for independent Lean work;
Docker was configured to 6 CPU / 16 GiB after creation. Memory quota enforcement was
not demonstrated by this sandbox, so those settings are not a measured memory ceiling. Each pair of build outputs must match byte-for-byte. Both are
independently stripped and compared again. A separate reusable post-processing
container limits container churn; it does not replace either clean build.
The earliest receipts used fresh containers for every post-processing operation;
their commands and measurements record that distinction. Both stripping variants
must pass the existing package tests before a profile is published.

```sh
corpus/toolchain/image.sh
python3 scripts/corpus/variants.py --work /work/out/variant-builds
# Or a selected tranche:
python3 scripts/corpus/variants.py --package cjson --arch aarch64 --level O1 \
  --work /work/out/variant-builds --resume
python3 scripts/corpus/matrix.py --output corpus/matrix.json
```

Defaults cover all ten packages, both architectures, and O0/Og/O1/O3. Existing
completed profiles are never overwritten: `--resume` verifies output and included
source hashes and retains their original receipts without claiming new runs.
Builds not yet completed are absent from the matrix. The existing canonical O2
unstripped artifacts are indexed too; O2 stripped artifacts are not yet delivered.

The paired executable-byte check supplies tool-derived stripped address mappings,
not functional equivalence, source-semantic binding or a Lean proof. Two cJSON and all sixteen mimalloc variants have checked whole-file parsing and structural decompositions, with hash-bound measured receipts in [variant-lean](../measurements/variant-lean/README.md). The other 390 variants have no generated/checked Lean parsing or structural decompositions
and no concrete function statements. The corpus has **zero contextual C-to-ELF statements** and **one stated, unproved binary-equivalence problem** for two mimalloc variants; see [formal function receipts](../measurements/formal-functions/README.md). Source mappings
and those formal stages must be added separately. This tranche adds optimization
and stripping variants of existing releases; it does not provide the requested
rich multi-version/configuration matrix or assembly-enabled OpenSSL/BoringSSL.

These inputs and outputs are [software under test](../UNDER-TEST.md). Owned build
scripts and local helpers retain normal code scanning; no findings are dismissed
or scans disabled by this representation.

Acquisition fallback: exact pinned TinyCC/coreutils archive, signature and keyring hashes
were validated from a public mirror after upstream connection timeouts. The acquisition
records are in `corpus/measurements/matrix-remainder/`. Resume validates published hashes
and preserves the original clean-build measurements; it does not claim new repetitions.
