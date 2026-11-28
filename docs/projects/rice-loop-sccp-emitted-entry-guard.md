# Emit a typed CF entry guard for the two-route quad loop

`EntryGuard.compile p facts` runs the existing SCCP FIFO admission once.
On singleton admission it emits one typed CF graph with a new entry block
and both existing CF fragments. Each invocation of the graph checks the
concrete bank before the original preheader runs. A covered bank enters
the specialized fragment. An uncovered bank enters the original two-route
fragment. The compiler retains the existing `.bothMarked` and
`.neitherMarked` refusals when analysis admits no singleton.
[Compiler and entry block](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/MLIR/CF/EntryGuard/Defs.lean)

The guard uses existing typed constants, unsigned comparisons, `i1`
arithmetic and `cf.cond_br`. For a constant fact, both unsigned comparisons
must be false for equality. The guard conjoins these tests in `i1`.
Overdefined facts add no test, and a bottom fact forces the original
fragment. `entry_eval` identifies the actual successor with the
`TupleCovers` decision used by the host API. The two new entry labels
require no extra arguments. Each arm sees the original external bank in
its original slot order. Branches inside an arm keep their operands,
widths and order, with their labels scoped to that arm.
[Guard and observation laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/MLIR/CF/EntryGuard/Thms.lean) ·
[Typed CF linker](../../Silmaril/SSA/MLIR/CF/EntryBranch/Thms.lean) ·
[Host checked entry API](rice-loop-sccp-checked-entry.md)

At feedback limit `n`, `compile_run` compares `3*n+2` source visits
with `2*n+4` CF visits for a covered input or `3*n+4` CF visits otherwise.
Each CF budget includes one new guard visit. `compile_returns_iff`
quantifies the two budgets independently, and `compile_diverges_iff`
relates exhaustion at every CF budget to absence of any finite source
return. These laws require successful emission and apply to any concrete
typed input in the fixed pure two-route profile.

## Run both paths in one emitted graph

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.EntryGuard
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example (program facts)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)
open Silmaril.SSA.SeaOfNodes.MLIR.Lowering (encodeValues)

#eval
  let input := Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example.entry
  match compile program (facts (.constant ⟨true⟩)) with
  | .error _ => (none, none)
  | .ok cfg =>
    let run (side : Bool) (fuel : Nat) : Option Nat :=
      match cfg.run evalOp fuel (encodeValues (input true side)) with
      | some (.cons value .nil) => some value.toNat
      | none => none
    (run true 6, run false 7)
-- (some 99, some 7)
```

Both calls enter the same graph. The second call disagrees with the assumed
selector and takes the original path. The regressions also test a
different carried word, exhaustion on both paths, and both analysis
refusals. The emitted object is a project-typed CF graph executed by the
Lean CF runner.
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/MLIR/CF/EntryGuard/Regression.lean) ·
[Rice and Wegman–Zadeck correspondence](rice-loop-sccp-two-route-worklist.md#source-correspondence)
