# Native memory runs under `decide +kernel`

`bench.py` times one `decide +kernel` check of a native-interpreter run
(`Binaryen.invokeRun`) on `Silmaril.Wasm.Interp.MemExample.memMod`, with the
memory resized to `pages` pages. The run is `f(7)`, which stores 7 at address 0
and loads it back. With 0 pages the expected behaviour is `traps` (out of
bounds); otherwise it is `returns [7]`.

## Provenance

One run of this script on commit `5fe46b1c` (2026-11-15; the benchmark imports only `MemExample.Defs`, unchanged since), Lean `nightly-2026-11-05`, on an
8-core Linux sandbox, one sample per case, with `set_option maxRecDepth 100000` in the
generated file:

```
lake build Silmaril.Wasm.Interp.MemExample.Defs
python3 -I benchmarks/native-memory-kernel/bench.py 0 1
```

Raw output: [`results-2026-11-15.tsv`](results-2026-11-15.tsv). Times are wall clock of
`lake env lean` on the generated file, including import of the Wasm library.

| pages | expected | time | status |
|---:|---|---:|---|
| 0 | `traps` | 3.31 s | ok |
| 1 | `returns [7]` | 213.08 s | kernel deterministic timeout |

Without the `maxRecDepth` option the 1-page case fails sooner (10.93 s), with the kernel's
"deep recursion" error.

## Reading

The core store's memory is a `ByteArray` (`MemInst.bytes`). One page is 65536 bytes, built
by `Memory.grow?`/`Array.replicate` and read by `Memory.load`/`readBytes` (`extract`).
In the kernel these are structural recursions over the whole page, so the cost scales with
the page size, not with the number of bytes the program touches.

The kernel-friendly byte representations already in the library (`Silmaril.KBytes`,
`Silmaril.Prelude.Bytes.Write`, `benchmarks/kernel-bytes-write`, and the `PageMem`
measurements of hiloopai/silmaril-lean#131 and #133) are not used by the Core store here.
Using them would need either a store whose memory is such a tree, or a proved
correspondence between the two. Neither exists for `MemInst` yet, and nothing here claims
that in-bounds memory runs are fast under the kernel.
