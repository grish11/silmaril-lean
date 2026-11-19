# Kernel Wasm source agreement

## Full Core equation: one passive data segment

`Packed.PassivePlan.Verified.sound` transfers to `Core.decode?` itself for a
header followed by one data section with one passive segment and no other
sections. The claimed positions are only hints: the kernel checks the Core
header, section id and wire size, vector count, passive mode and payload length
with the packed reader, then compares the bounded payload and checks EOF.
This also transfers the reference reader's vector guards, section-size check
and final module construction. It is not a general packed module decoder.

```sh
python3 benchmarks/wasm-kernel-decode/run.py /tmp/wasm-passive --mode passive \
  --seconds 15 --memory 4096 --cases data-4k data-1024k
lake env lean -DautoImplicit=false -E warning benchmarks/wasm-kernel-decode/PassiveRegression.lean
```

All three phases prove the identical `Core.decode? source.toByteArray = some
expected` on the same independent, explicitly quoted `expected` and source.
The fast phase applies `decodeF_eq`; the packed phase applies the certificate
theorem. In a single run, including imports and with a 15 s / 4096 MiB limit:

| Payload | List-slice proof | `decodeF` proof | Packed proof |
| --- | ---: | ---: | ---: |
| 4 KiB | 3.87 s / 2.07 GiB | 3.83 s / 2.08 GiB | 5.37 s / 1.95 GiB |
| 1 MiB | memory limit (14.91 s) | memory limit (13.54 s) | 4.17 s / 2.03 GiB |

The 1 MiB packed span check took 313 ms, but that excludes the other certificate
fields and import. The small case does not show a wall-time improvement.
The full-equation result does not cover arbitrary data, real code, or many-body
modules; the comparison for those fixtures is framing only.

## Packed framing stage

`Silmaril.Wasm.Binary.Packed` reads directly from a well-formed `KBytes` tree.
The cursor uses the proved cached length, and a section payload is itself a
packed cursor with a relative position and its own bound. Header, signed and
unsigned LEB, slice, and section-envelope correspondence compare both the
reference reader's result (including errors) and its final cursor. The ordered
scan also checks the Core section order and consumes the complete input. The
compiled Core decoder is unchanged by this stage.

The framing proposition is **not** `Core.decode? bytes = some module`.
In particular, the scan does not read section bodies, code entries, or custom
section names. It can accept envelopes of files the decoder rejects.

```sh
python3 benchmarks/wasm-kernel-decode/run.py /tmp/wasm-frames --mode framing \
  --seconds 15 --memory 4096 --cases empty-check lrat bodies-512 data-1024k
python3 benchmarks/wasm-kernel-decode/run.py /tmp/wasm-full --mode kernel \
  --seconds 15 --memory 4096 --cases empty-check lrat bodies-512 data-1024k
lake env lean -DautoImplicit=false -E warning benchmarks/wasm-kernel-decode/PackedRegression.lean
```

The two framing modes prove the identical `scanFramesSpec.run cursor.spec =
.ok (frames, finalCursor)` for each fixture. The direct baseline runs Core's
list-slice `readBytes` and demands the resulting span's size. The packed proof
computes with the cached size and applies `scanFramesSpec_of_ok`. The full
list-slice and `decodeF` baselines prove a separate, identical-to-each-other
full decode equation on the same bytes. The harness checks the checked-in
fixture hashes and records SHA-256 for every generated fixture. It records
whole-process wall time, GNU `time` peak RSS, and the timed kernel declaration
check; 15 seconds is a wall limit and 4096 MiB is the Lean allocator limit,
not an OS-enforced RSS limit. Compare only like propositions.

One run on Lean `nightly-2026-11-05` illustrates the stage boundary (wall seconds):

| Fixture | Packed framing | Direct framing | Full list slice | Full `decodeF` |
| --- | ---: | ---: | ---: | ---: |
| empty-check | 4.24 | 4.06 | 3.11 | 3.03 |
| LRAT | 3.04 | 4.27 | memory limit | memory limit |
| 512 bodies | 3.00 | 3.53 | memory limit | memory limit |
| 1 MiB passive data | 3.52 | timeout | memory limit | memory limit |

Packed framing peaked at 1.95 GiB and spent 7–12 ms in the timed kernel
declaration check, with imports accounting for most wall time. This one run is
not a throughput estimate. These framing measurements do not establish a
speedup of full module decoding.

## Full-decoder slice baseline

`Decode.readBytes` now slices the logical list rather than using the kernel's
indexed array-extract loop. `Decode.extractForKernel_eq` proves equality for
all inputs and endpoints, and `@[csimp]` retains `ByteArray.extract` in compiled
decoders. `decodeF_eq` and the reference decoder's grammar-soundness proof
still check. No validation rule, runtime decoder choice, or execution-memory
representation changes.

## Separate source and object terms

With the optional `Quote` module built (commands below):

```lean
module
import Quote

open Silmaril.Wasm.Binary.Core

wasm_bench_defs source decoded from "module.wasm"

theorem sourceMatches : decode? source.toByteArray = some decoded := by
  wasm_check_source
```

The command reads a file relative to the Lean file, runs the existing fast
decoder in elaboration, and writes independent `KBytes` and explicit `Module`
terms. Data payloads in the module use packed literals too. A malformed input
fails; no fallback decoder runs. Merely constructing these definitions or
checking a fact about `decoded` proves nothing about its source. The optional
tactic checks the displayed equation via `decodeF_eq` and a reflexivity term
checked by the kernel. It does not assert an evaluator result or require any
trust beyond Lean's kernel. The theorem is about the embedded bytes, not a
path, a file's provenance, or later filesystem contents. Decode agreement is
also distinct from Wasm validation. The commands are experimental and outside
the default build. The example is an explicit opt-in, not an import policy.

## Reproduce

From the repository root with the pinned Lean toolchain and a populated Lake
cache, use Python 3 and Linux `/usr/bin/time` and `timeout`:

```sh
python3 benchmarks/wasm-kernel-decode/run.py /tmp/wasm-kernel --mode kernel --seconds 15
python3 benchmarks/wasm-kernel-decode/run.py /tmp/wasm-native --mode native --seconds 15 --runs 3
python3 benchmarks/wasm-kernel-decode/run.py /tmp/wasm-windows --mode window --seconds 15 \
  --cases data-4k data-32k data-1024k
python3 benchmarks/wasm-kernel-decode/run.py /tmp/wasm-repeat --mode kernel --seconds 15 \
  --cases data-4k --runs 3
```

Use the benchmark-only commit `1e9ee619b540530567f34c3fda0f5e1e2d87859f`
(main `ea3f9f405` plus the harness, before the list-slice change) for the old
decoder comparison. Use the same cases, budgets, and toolchain on both. The
harness generates many-body and passive-data modules deterministically and
records input bytes and SHA-256 hashes. It does not check in generated binaries.

For the targeted regression, use the same build directory as the window run:

```sh
lake build --wfail +Silmaril.Wasm.Binary.Core.DecodeSound +Silmaril.Wasm.Perf.CoreDecode.Thms
LEAN_PATH=/tmp/wasm-windows/build lake env lean -j1 -DautoImplicit=false -E warning \
  --root=benchmarks/wasm-kernel-decode benchmarks/wasm-kernel-decode/Regression.lean
```

The regression covers agreement and a direct object query, malformed LEB128,
truncated sections/data, wrong code body length, a wrong header version, and
packed window success, contents mismatch, and overflow. It audits the proofs
for axioms. `wasm_bench_agreement` submits the *same* `reader source.toByteArray
= some expected` for `decode?` and `decodeF`, directly as a kernel-checked
declaration; it avoids doing the decoder reduction a second time in the tactic
elaborator. A failing process is not evidence of an agreement theorem.

## Kernel results

Linux x86-64 sandbox, Lean nightly 2026-11-05, one Lean worker, `-M4096`,
64 MiB thread stack, `maxRecDepth=100000`, no heartbeat cap, 15 s per fresh
process. Below: process wall seconds / peak RSS GiB, including import. Lean's
allocator cap is distinct from the measured process RSS. Rows are single runs
except the three repeated post-change 4 KiB runs (medians). The phases ran on
one worker/backend but are not a paired statistical test for small differences.

| Input | Bytes | Old `decode?` / `decodeF` | List slice `decode?` / `decodeF` |
| --- | ---: | --- | --- |
| Empty checker | 45 | 2.71 / 2.09; 2.87 / 2.10 | 2.84 / 2.09; 2.74 / 2.09 |
| Start fixture | 49 | 2.62 / 2.10; 2.66 / 2.10 | 2.90 / 2.10; 2.79 / 2.10 |
| Real LRAT checker | 1,812 | memory, 9.24 / 4.00; 10.03 / 4.00 | memory, 9.54 / 4.00; 10.23 / 4.00 |
| 64 code bodies | 341 | 6.37 / 3.03; 6.71 / 3.03 | 6.24 / 3.03; 5.86 / 3.03 |
| 512 / 2,048 code bodies | 2,584 / 10,264 | memory, ~9–10 / 4.00 | memory, ~10–12 / 4.00 |
| 4 KiB passive data | 4,111 | memory, 12.50 / 4.00; 12.76 / 4.00 | **3.29 / 2.20; 3.57 / 2.20** |
| 8 KiB passive data | 8,207 | not run | 4.60 / 2.37; 4.79 / 2.37 |
| 16 KiB passive data | 16,401 | not run | **7.25 / 2.77; 7.14 / 2.78** |
| 32 KiB passive data | 32,785 | depth limit, 9.81 / 3.52; 10.86 / 3.52 | wall limit, 15.03; 15.02 |
| 128 KiB passive data | 131,089 | memory, 11.49 / 4.00; 11.94 / 4.00 | memory, 13.61 / 4.00; 13.51 / 4.00 |
| 1 MiB passive data | 1,048,593 | memory, 11.57 / 4.00; 11.48 / 4.00 | memory, 11.62 / 4.00; 11.89 / 4.00 |

For 4 KiB, post-change median kernel declaration times were 0.637 / 0.733 s.
For 16 KiB they were 4.47 / 4.49 s. `decodeF`'s native optimizations do not
reliably accelerate kernel reduction. Construction, including environment
startup and `.olean` writing, was generally 2.5–3.3 s; the 1 MiB baseline
construction took 3.29 s, including 0.31 s module reification and 0.40 s source
emission/checking. Import-only and import plus a `head?.isSome` field query
typically took 2.5–2.9 s and about 2.07 GiB, even for inputs whose agreement
failed. These are separate processes; the query does not call a decoder.

## Narrow packed-byte result, and the next bottleneck

`Window.lean` proves the same `Decode.readBytes` success equation as raw
kernel reduction, including the output bytes and next cursor. It checks a
supplied offset and a packed expected byte window, then transfers via
well-formedness, the length and slice laws, and exact equality of the bytes.
It does **not** establish that the offset is a Wasm section boundary, check
any LEB field or show that a module decodes. Table: current checkout, same
process budget, one run; `length` reduces only the materialized size equation.

| Payload | Raw length | Raw `readBytes` | Packed check + transfer |
| --- | --- | --- | --- |
| 4 KiB | 3.10 s / 2.16 GiB | 3.48 s / 2.20 GiB | 2.79 s / 2.07 GiB (3.0 ms declaration) |
| 32 KiB | 7.88 s / 3.11 GiB | 15.20 s timeout | 2.99 s / 2.07 GiB (5.8 ms declaration) |
| 1 MiB | 13.30 s / 4.00 GiB, memory | 11.58 s / 4.00 GiB, memory | **2.92 s / 2.15 GiB** (243 ms declaration) |

On the old checkout the same 1 MiB packed check transferred successfully in
2.98 s / 2.15 GiB; raw `readBytes` used 4.00 GiB and failed. Materializing
packed source just to find its length is already prohibitive at 1 MiB. The
next experiment should keep a well-formed packed source and cached length in
the cursor, transferring bounds, byte reads and LEB128 first. Then prove exact
frame consumption and check a body or data segment without materializing the
rest of the file. The raw window theorem is reusable for that step, not a
full reader proof. The many-body/LRAT failures are not fixed by the slice
change; this experiment did not isolate each cause of their memory use.

## Compiled baseline (not evidence of kernel agreement)

One Lake executable uses both readers; the call site imports `CoreDecode.Defs`,
not the `decode?` compiler rewrite in `Thms`. Both readers keep the same
compiled slice primitive. Medians of three cold processes, inner decode only:
reference/fast 0.46/0.25 ms on LRAT, 1.61/0.78 ms on 2,048 bodies, and
0.50/0.51 ms on 1 MiB passive data. Process wall was ~0.03–0.05 s at ~67–73 MiB
RSS for the recorded suite. Startup/I/O are outside the decode timer and
reported separately. No speed claim for sub-millisecond differences on very
small inputs. The runtime path does **not** produce proofs.
