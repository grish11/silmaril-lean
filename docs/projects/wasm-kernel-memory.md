# Kernel evaluation of Core memory writes

Core's linear memory is a `ByteArray` (`Silmaril.Wasm.Execution.Memory`). Every Core write
goes through `Memory.writeBytes`: `store`, `memory.init` (data segments at instantiation),
`memory.copy` and `memory.fill`. It used to be `bytes.copySlice 0 memory start bytes.size`.

**The problem.** `decide +kernel` evaluates `ByteArray` operations through their list
definitions. `copySlice` rebuilds the whole destination, including the part after the written
range. On a 64 KiB memory that is about 65 000 nested list steps, and the kernel stops with
`(kernel) deep recursion detected`, even for a 3-byte write at a low address. `get!`, `set!`,
`size` and short `extract`s on the same memory are fine. So any Core run that writes memory,
including instantiating a module with a data segment, could not be kernel-checked. The
canonical ABI's `list<u8>` lowering stores into memory, so it was affected too.

**The change.** `writeBytes` now computes the written memory with `Memory.writeSlice`:

* `spliceL l start bs = take start l ++ bs ++ drop (start + bs.length) l`, by recursion on the
  first `start` elements only. The suffix after the written range is shared, not rebuilt
  (`spliceL_eq`).
* `writeSlice memory start bytes = bytes.copySlice 0 memory start bytes.size`, unconditionally
  (`writeSlice_eq`, a `@[simp]` lemma). Proofs that unfold `writeBytes` and simplify therefore
  still see `copySlice`, so no statement about memory changes.
* `@[csimp] writeSlice_eq_native : @writeSlice = @writeSliceNative`. Compiled code still runs
  `ByteArray.copySlice`, so native performance is unchanged. `@[csimp]` requires this
  equality to be a proved theorem.

**What this is not.** It does not replace `ByteArray` and adds no evaluator or trusted
component. The kernel evaluates the same definitions it always did; one definition is written
so its evaluation does not rebuild memory. The kernel-evaluation PRs #105, #131 and #133
measure packed and tree-shaped memories for a separate Wasm subset machine. Using those
inside Core needs Core's `Store` to take the memory type as a parameter, a much larger
refactor. They remain the route to memories well beyond 64 KiB and to write-heavy workloads.

## Measurements

The same check on `main` (`f7d69fb8`) and with this change: one run each, 2-vCPU sandbox,
wall time of `lake env lean` on a one-theorem file, peak RSS of the `lean` process.

| check (`decide +kernel`) | `main` | with `writeSlice` |
|---|---|---|
| `accept(list<u8>)` component, 64 KiB memory with a data segment, `run` records `"hi!"` | `deep recursion detected` (16 s, 3.4 GB) | **passes** (16 s, 3.1 GB) |
| exported `accept(list<u8>) -> bool`, `realloc` at 1024: `true` on `"hi!"`, `false` on `"hi"` | `deep recursion detected` (28 s, 3.4 GB) | **passes** (20 s, 3.2 GB) |
| `writeBytes` at address 65530 of 64 KiB, then `get!` | `deep recursion detected` (12 s, 2.5 GB) | **passes** (21 s, 4.5 GB) |

The kernel-checked theorems are `Ref.Examples.hiRecorded_records`, `hi_mem_direct`, `exportCall_hi`
and `exportCall_hi2`, and in `Ref/Typed/Examples.lean` `exportCallArgs_ill`,
`exportCallTyped_ill`, `exportCallTyped_hi`, `exportCallTyped_hi2`, `recordsTyped_hi` and
`recordsTyped_ill`. They are part of the library build, so CI kernel-checks them.

## Limits

Cost grows with the write address: a write at `a` rebuilds `a` list cells. Write-heavy runs
at high addresses, or memories of several MiB, remain expensive. The tree and packed
representations above address them.
