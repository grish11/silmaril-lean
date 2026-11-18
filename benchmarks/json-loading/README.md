# JSON loader benchmarks

Run from the repository root with the pinned Lean toolchain, Python 3, GNU `time` and `timeout`:

```sh
make json-loading-check
python3 benchmarks/json-loading/run.py /tmp/silmaril-json-bench --runs 2 --seconds 15
```

The runner generates synthetic fixtures (no large blobs in git), reuses three tracked input
files, writes `results.csv`, and keeps separate process logs and timing files. `--case` limits
it to named fixtures and is repeatable. The processes use one Lean thread, a 4,096 MiB Lean
memory limit, and a 32 MiB Lean thread stack. Each check has a wall-time limit. Kernel query
and agreement probes use `maxRecDepth 8192` and no heartbeat limit; the memory and time limits
still apply. For meaningful comparisons, avoid rebuilding the library during a run.

- **Runtime:** the same Lean `--run` harness reads each file as bytes, then times acceptance
  with `JsonWire.parse?` (the old ordered exact-decimal parser), `Fast.parseBytes`, and
  `Lean.Json.parse`. The last is a useful speed reference, not a compatible replacement: it
  does not expose ordered duplicate members or the same decimal/sign contract. Lean core and
  repository modules need not run through identical machine-code paths in this harness; this
  is not a standalone native executable benchmark.
- **Declare:** new Lean processes write an `.olean` for a source-only Wire or Fast parser
  application or a precomputed Fast constructor tree. The precomputed logs separate the
  compiled parse and expression emission, and Lean profiles kernel `type checking` and
  `.olean serialization`. External wall time includes startup, IO, elaboration and output.
- **Import:** a fresh Lean process only imports the corresponding `.olean`.
- **Query:** the same import plus one `decide +kernel` proof about a late element, including
  an indexed-versus-linear comparison on the same precomputed object. The list case uses
  chunk routing in both variants. Wall/RSS include the common module load; compare to import
  to approximate the incremental cost.
- **Agreement:** a fresh process checks `SourceMatches` for the complete precomputed result
  on the small and medium inputs, not just a field claim.

## Results

November 18, 2026; Linux/x86-64 sandbox, Lean `4.37.0-nightly-2026-11-05`
(`67dafde474f`). Medians of two fresh processes per cell; failures reproduced in both runs.
All runtime parsers accepted the tracked files they completed. The wide case has 42,001
members with a long shared key prefix; the list has 40,001 items; nested has 32 enclosing
objects around 33,000 records. The checker selects a late field/item, not the first one.

| Input | Bytes | Wire parse (ms) | Lean.Json parse (ms) | Fast parse (ms) |
| --- | ---: | ---: | ---: | ---: |
| Small | 442 | 1.02 | 0.064 | 0.51 |
| Medium | 35,686 | 121 | 0.40 | 20.2 |
| Wide | 2,772,046 | timeout | 27.2 | 1,516 |
| List | 3,280,007 | timeout | 16.8 | 1,473 |
| Nested | 2,959,906 | timeout | 33.4 | 1,807 |
| Tracked OCI manifest | 219 | 0.92 | 0.048 | 0.52 |
| Tracked litmus corpus | 116,688 | 5,803 | 1.92 | 75.7 |
| Tracked litmus metadata | 232,566 | timeout | 3.36 | 132 |

Fast completed the multi-MiB parses in 2.1–2.5 s wall, at 2,269–2,285 MiB process peak RSS
(about 2,207 MiB for the small input including the Lean environment). Wire hit the 15 s wall
limit on those three cases, not a measured completion time. On the medium fixture Fast was
6× faster than Wire by parse time. Core `Lean.Json` was substantially faster than both on
these inputs but does not implement the same API/semantics. In a wide-fixture pilot, Lean's
array quicksort took the Fast parser to about 13 s; the stable merge sort brought the same
parse to about 1.5 s, with insertion order retained within hash collisions.

| Input | Precomputed build wall (s) | `.olean` source / precomputed (MiB) | Import precomputed (s) | Wire / source kernel query (s) | Precomputed indexed / linear query (s) |
| --- | ---: | ---: | ---: | --- | --- |
| Small | 0.62 | 0.005 / 0.008 | 0.52 | no reduction / 0.71 | 0.54 / 0.55 |
| Medium | 0.57 | 0.038 / 0.49 | 0.53 | memory / no reduction | 0.56 / 3.51 |
| Wide | 3.98 | 2.65 / 36.69 | 0.50 | memory / memory | 0.55 / memory |
| List | 2.17 | 3.13 / 12.85 | 0.54 | memory / memory | 0.54 / 0.52 |
| Nested | 9.90 | 2.83 / 26.67 | 0.53 | memory / memory | 0.53 / 0.59 |

The source-only definitions (both parsers) built in roughly 0.5–0.9 s and imported in roughly
0.5 s. Their imports do not evaluate the parser. Precomputation trades larger declarations for
field proofs near the import-only cost. Prepared queries on large inputs peaked at 2,207–2,228
MiB; linear search on the medium object peaked at 3,013 MiB. The large memory failures peaked
near 4,100 MiB. The small Wire query and medium source query reported that `decide` did not
reduce (rather than returning `false`). On the small object there is no hash index to compare.

In the wide precomputed build, median parser/emitter/kernel-type-check/serialization times were
1,514/56/375/1,500 ms. For the list they were 1,469/13/31/103 ms, and for nested
1,807/164/357/6,975 ms. Nested builds ranged from 6.33 to 13.47 s wall, largely serialization
variance. The peak precomputed build RSS on large cases was about 2.4 GiB. Kernel-only full
`SourceMatches` verification took 0.66 s on the small input and exceeded the memory limit on the
medium input. The large selective proof times do **not** include that full certification.
