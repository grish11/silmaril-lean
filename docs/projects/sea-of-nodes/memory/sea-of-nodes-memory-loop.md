# Sea of Nodes tail-tested memory loop

IR ’95 §2.5 models the whole STORE as an SSA value that a Phi can merge.
Sections 3.1–3.2 and Figure 7 show a Loop Region latching by the arriving
control occurrence, with a tail If whose true projection goes back to
the header. Simple chapter 10 closes a loop's memory Phi with the memory
produced in the body. Its example uses a header test. This fragment uses
the paper's tail test and the same occurrence-to-memory correspondence.
[IR ’95](https://doi.org/10.1145/202530.202534) ·
[Simple chapter 10 at `f0a6c675`](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable)

The entry occurrence selects Start's initialized heap. The backedge
occurrence selects the preceding activation's final memory version. The
selected heap is memory version zero for the next activation's ordered
straight-line table. Each table contains a Load and a Store. The word
it exports is the tail If's data input. Comparing it to a typed invariant
word argument determines exit on equality and a backedge otherwise. The
exit observes that word and the latest heap. Zero backedges still execute
the table once.
[Definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Defs.lean) ·
[Straight-line memory profile](sea-of-nodes-memory.md)

Import `Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms` for
`Graph.returns_iff_mem_denote`. It identifies finite explicit-edge returns
with membership in the heap-threaded partial denotation, observing the
word and whole final heap. `Graph.returnsAfter_iff_evalAfter` adds an exact
completed-backedge count. The executable `evalAfter` yields `none` when
there is no return at that count. The model fixes the table's effect order
and uses already initialized word cells. It covers one header and one
backedge with a total body and total test.
[Theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Thms.lean)

The regression shifts one initialized cell into another and clears the
source cell. The one-activation case still performs both stores. In the
two-backedge case the first activation loads `1` and writes `2` to the same
address. The next activation loads that `2`, and the third loads `0` and
exits. The checks observe the entire final heap and its untouched cell.
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression
```

## Typed MLIR CF lowering

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Thms
```

`MLIR.lower` shares the [finite-cell body compiler](../../../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/MLIR/Finite/Defs.lean).
The fixed, initialized `Fin n → Word` heap is carried as `n` scalar `i64`
block arguments. The ordered body emits scalar scans for dynamic typed
addresses. Entry passes the initial heap to the header. The header runs
the body and forwards the returned word and updated heap to the test
block. The test emits `arith.cmpi eq` against the invariant typed stop word.
Its backedge feeds the updated heap into the header, and its other edge
passes the word and heap to exit. This is an SSA encoding of initialized,
in-bounds cells with a fixed cell count.
[CFG definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/Defs.lean)

`MLIR.lower_run_eq_some` gives the exact minimum `Cfg.run` budget of
`2 * k + 4` block ticks for a return with `k` completed backedges. `MLIR.lower_returns_iff` matches finite returns of the word and
entire heap. `MLIR.lower_denotePart` gives the corresponding observation
in the [existing partial CF evaluator](../../../../Silmaril/SSA/MLIR/CF/SwitchAssert/Denotation/Defs.lean),
and `MLIR.lower_diverges_iff` matches absence of any finite return.
[CFG theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/Thms.lean)

The emitted-CFG checks exercise the three-cell shift with zero and
two backedges, a removed store that preserves the word and changes the
final heap, and a fixed backedge with no finite return.
[CFG regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/MLIR/Regression.lean)

### Equations at typed entry valuations

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Institution.Thms
```

`MLIR.Institution.satisfaction` compares the two emitted CFGs using
the canonical scalar profile at the native model's cell count. It
preserves and reflects agreement on every initial heap, including
the absence of a finite return. `observe_mapGraph` and
`satisfaction_reindex` relate re-emission after a typed entry port map
to pullback of the native valuation, with the same heap and cell count.
These laws compare observations of generated CFGs over the existing
native models.
[Native institution](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Institution/Thms.lean) ·
[MLIR equation theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/Institution/Thms.lean)

### Compare emitted backend observations

```lean
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Thms
```

At a shared typed entry valuation and initial heap,
`lambda_observation_iff_mlir` identifies the λSSA return at label zero
with the CF observation of its packed word and whole final heap.
`mlir_observation_eq_map_theta` re-encodes the numbered θ result by
reading its word and heap wires into the scalar CF result tuple.
`mlir_observation_iff_run` connects that partial CF observation to
finite execution of the emitted CFG.
[Backend comparison](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Backends/Thms.lean)

`lambda_no_return_iff_mlir` and `theta_no_return_iff_mlir` match
absence of finite returns. The corresponding satisfaction laws
compare equations over all initial heaps at the chosen valuation.
The regression checks the three-cell result after two backedges
and the absence of a result in all three backends on a fixed backedge.
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Backends/Regression.lean)

The CF evaluator runs scalar bindings with a total bitvector
interpretation. The LLVM scalar profile rejects `llvm.load`.
The MLIR result in these laws uses the initialized cells carried
as SSA values above.
[CF evaluator](../../../../Silmaril/SSA/MLIR/CF/Basic/Defs.lean) ·
[LLVM admission example](../../../../Silmaril/SSA/MLIR/LLVM/Examples/Thms.lean)

## Typed MemRef activation

`MemRef.lowerActivation` reuses the [single-buffer body lowering](sea-of-nodes-memory.md#one-initialized-rank-one-memref).
It emits the native ordered `memref.load` and `memref.store` bindings
and appends `arith.cmpi ne` to compare the body's returned word with
the invariant stop operand. The comparison uses the ordered block's
two-way control type. Selector zero requests exit and selector one
requests a backedge. The monadic runtime carries every updated buffer
cell in either case.
[Activation definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/MemRef/Defs.lean) ·
[Ordered control syntax](../../../../Silmaril/SSA/RVSDG/MLIR/Graph/Feedback/Defs.lean) ·
[Pinned comparison operation](https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/include/mlir/Dialect/Arith/IR/ArithOps.td)

`lowerActivation_run` identifies the emitted selector, word, and complete
buffer. `observeActivation_eq_step` decodes the outcome and identifies it
with the native heap-threaded step for any starting buffer. This is a
one-activation law for one initialized, contiguous, statically sized
rank-one `i64` buffer with `Fin n` indices.
[Activation theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/MemRef/Thms.lean)

The activation regression also passes a restart buffer into a second
activation. Its one-cell case uses coincident indices and checks that
the last store wins. The same fixture requires a typed address, so its
entry valuation is uninhabited at zero cells.
[Regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/MLIR/MemRef/Regression.lean)

### Executing MemRef feedback

`MemRef.runAfter` repeatedly executes that emitted activation. An exit
returns the loaded word and whole final buffer. A backedge passes the
post-store buffer to the next activation with the original typed operands.
The budget counts **exactly** the requested backedges, so even budget zero
executes the entry activation and an earlier exit yields `none` at a larger
count. `MemRef.observe` describes the finite return across all counts.

The driver repeats the emitted ordered block using the decoded activation
outcome.
[Driver definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/MemRef/Feedback/Defs.lean)

`runAfter_eq_evalAfter` agrees with the native evaluator at every exact
count. `returnsAfter_iff_runAfter` and `returns_iff_mem_observe` preserve
and reflect the word and every cell in counted and finite returns.
`observe_eq_none_iff` identifies the absence of a finite return with
`none` at every count.
[Feedback theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/MemRef/Feedback/Thms.lean) ·
[Feedback regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/MLIR/MemRef/Feedback/Regression.lean)

### Emitted MemRef CF loop

`MemRef.CF.lower` emits a typed CFG with an entry branch, a header
conditional, and an exit return. Its header contains the same emitted
ordered MemRef activation. The typed entry valuation is captured by the
body interpretation, and the initialized buffer lives in `StateM`.
The activation's selector becomes an `i1` terminator operand. The
conditional takes a self edge on restart and passes the `i64` word
to the exit on completion. Both edges carry the whole updated buffer
through the shared monad.
[CFG definitions](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/MemRef/CF/Defs.lean) ·
[Ordered CF adapter](../../../../Silmaril/SSA/MLIR/CF/Ordered/Defs.lean)

`header_transition` identifies both actual successor frames and their
post-store buffer. `run_eq_some_iff` agrees with the exact-count driver
at any count within the CFG's backedge allowance. The CFG runner uses
one block step each for entry and exit and one per header activation.
The shared scheduler specializes to the pure CF evaluator via
`runBlock_id`.

At the native boundary, `Buffer.mk heap` uses the native `Fin n → Word`
heap as its cell function, and the typed input valuation is shared.
`cfg_run_eq_some_iff_returnsAfter` observes the returned word and every
cell exactly when a native return at count `k` fits the raw block fuel
(`k + 3 ≤ fuel`). The `run` wrapper uses `budget + 3` blocks, so
`run_eq_some_iff_returnsAfter` uses `k ≤ budget`. `run_eq_none_iff`
identifies bounded absence with failure at every native exact count
within that allowance. Across all allowances,
`exists_run_eq_some_iff_mem_denote` and
`forall_run_eq_none_iff_denote_eq_none` give finite observation and
no-finite-observation agreement with the native partial denotation.

This profile covers one initialized rank-one buffer with in-bounds
indices. Textual MLIR emission and general MemRef effects remain outside
the profile.
[CFG theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/MemRef/CF/Thms.lean) ·
[Pure specialization](../../../../Silmaril/SSA/MLIR/CF/Ordered/Thms.lean) ·
[CFG regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/MLIR/MemRef/CF/Regression.lean)

### Equations for emitted MemRef CF

`MemRef.CF.Institution.observe` collects finite returns of the emitted CFG
as a partial word-and-heap value at the native model's cell count and
typed entry valuation. `observe_eq` identifies that value with the native
partial denotation, including absence of a finite return.
`satisfaction` gives both directions of equation truth over all initial
heaps. `observe_mapGraph` and `satisfaction_reindex` reuse the native
typed entry-port maps and valuation reduct.
[MemRef equation theorems](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/MLIR/MemRef/CF/Institution/Thms.lean)

`mlir_observation_eq_map_memref` packs the MemRef result's word and every
cell into the scalar CF backend's partial observation.
The regression rejects two emitted programs with the same returned word
and different final heaps, and checks the absence of a finite return.
[Backend theorem](../../../../Silmaril/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Backends/Thms.lean) ·
[Equation regression](../../../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/Institution/Lowering/Backends/Regression.lean)

Save this example to a Lean file and run `lake env lean <file>`. The
activation results list the selector, word, and both final cells. The
feedback and CFG results list the word and both final cells on return.
The final examples check a partial observation and an equation at that
typed valuation.

```lean
module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Feedback.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Feedback.Defs

open Silmaril.SSA.RVSDG (Tuple)
open Silmaril.SSA.SeaOfNodes.Memory (Address Heap ValueSort Val Word)
open Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution (Signature Model)
open Silmaril.SSA.SeaOfNodes.Memory.Loop (Graph)
open Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution (Equation)
open Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Institution (Holds observe observe_eq satisfaction)
open Silmaril.MLIR.MemRef (Buffer)
open Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef (runActivation runAfter)
open Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF renaming run → runCfg

private abbrev args : List ValueSort := [.address, .word]

private def graph : Graph args where
  body := .load (.latest 0) (.arg .head)
    (.store (.latest 0) (.arg .head) (.arg (.tail .head))
      (.ret (.latest 1) (.output 0 .head)))
  effects := rfl
  stop := .tail .head

private def input : Tuple (Val 2) args :=
  .cons (0 : Address 2) (.cons (7 : Word) .nil)

private def start (old : Word) : Buffer 2 :=
  ⟨fun i => if i = 0 then old else 99⟩

private def exampleResult (old : Word) : Nat × Nat × Nat × Nat :=
  let (.cons selector values, final) :=
    runActivation graph input (start old)
  (selector.down.val, (values.get .head : Word).toNat,
    (final.cell 0).toNat, (final.cell 1).toNat)

#eval exampleResult 7  -- (0, 7, 7, 99)
#eval exampleResult 8  -- (1, 8, 7, 99)

private def feedbackResult (count : Nat) (old : Word) : Option (Nat × Nat × Nat) :=
  (runAfter graph input count (start old)).map fun (word, final) =>
    (word.toNat, (final.cell 0).toNat, (final.cell 1).toNat)

#eval feedbackResult 0 7  -- some (7, 7, 99)
#eval feedbackResult 0 8  -- none
#eval feedbackResult 1 8  -- some (7, 7, 99)

private def cfgResult (budget : Nat) (old : Word) : Option (Nat × Nat × Nat) :=
  (runCfg graph input budget (start old)).map fun (word, final) =>
    (word.toNat, (final.cell 0).toNat, (final.cell 1).toNat)

#eval cfgResult 0 7  -- some (7, 7, 99)
#eval cfgResult 0 8  -- none
#eval cfgResult 1 8  -- some (7, 7, 99)
#eval cfgResult 2 8  -- some (7, 7, 99)

private def signature : Signature := ⟨args⟩
private def model : Model signature := ⟨2, input⟩

example : observe graph model (start 8).cell = Part.some (7, (start 7).cell) := by
  refine (observe_eq (P := signature) graph model (start 8).cell).trans ?_
  apply Part.eq_some_iff.mpr
  apply (graph.returns_iff_mem_denote input (start 8).cell 7 (start 7).cell).mp
  refine ⟨1, (graph.returnsAfter_iff_evalAfter input (start 8).cell 1 7 (start 7).cell).mpr ?_⟩
  cbv
  congr 2
  funext i
  by_cases atHead : i = 0 <;> simp [Heap.write, Function.update, atHead]

example (e : Equation signature) : Holds e model ↔ e.Holds model :=
  satisfaction e model
```
