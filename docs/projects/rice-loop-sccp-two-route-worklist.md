# Compile the two-route SCCP quad with a typed worklist

`Bypass.Backends.Worklist.compile program facts` runs the two-route FIFO and
passes its final occurrence marks to the shared dispatch checker. It returns
the same retained route, typed MLIR CF and numbered RVSDG as
`Backends.compile`. Both refusals are preserved. The shared checker consumes
the equality proof erased by Lean, so the executable worklist path uses only
the FIFO result.
[Worklist compiler](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Backends/Worklist/Defs.lean) ·
[Paired compiler contract](rice-loop-sccp-compile-backends.md)

The existing carried-bank sparse solver's equations have one feedback
occurrence. This adapter reuses its typed job enumeration, FIFO and
potential proof. Control publishes all four occurrence marks, each Φ job
writes one typed destination, and result publishes the exit fact. A Φ job
watches the entry, true-feedback and false-feedback marks separately. It
uses the carried bank only when a feedback occurrence is enabled, and
evaluates only enabled predecessor columns. Control watches the bank after
entry is enabled, and result watches it after exit is enabled. Bank
dependencies are conservative whole-bank comparisons. Changes notify
absent jobs in FIFO order with duplicate suppression.
[Shared FIFO](../../Silmaril/SSA/SeaOfNodes/Loop/SCCP/Worklist/FIFO/Thms.lean) ·
[Two-route equations and watches](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Worklist/Defs.lean)

`evaluate_eq` identifies each pop with its projection of the existing
simultaneous equations. `solve_eq_simultaneous` proves equality of the
entire drained assignment, including every mark, typed Φ fact and result
fact. `compile_eq_simultaneous` transfers all of the paired compiler's
observation laws. Those laws still require successful compilation and
`TupleCovers facts input`. At feedback limit `n`, the source uses
`3 * n + 2` block visits, CF uses `2 * n + 3`, and θ uses bound `n`.
These bounds count execution, independently of the worklist pop count.
[Solver laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Worklist/Thms.lean) ·
[Compiler equality](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Backends/Worklist/Thms.lean)

## Run the example

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.Example
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Example
  (computesSelector stoppingFacts)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example
  (entry facts program)

#eval (runPrefix 5).pending == [.control]                                  -- true
#eval feedbackMarks (runPrefix 5)                                           -- (false, false)
#eval feedbackMarks (runPrefix 6)                                           -- (false, true)
#eval observations computesSelector (facts .overdefined) (entry true true) 1
#eval observations program (facts (.constant ⟨true⟩)) (entry true true) 1
#eval (Worklist.compile program (facts .overdefined)).map Targets.retained
#eval (Worklist.compile program stoppingFacts).map Targets.retained
```

The preheader computes the false selector despite an overdefined entry
selector. After five pops, the typed selector write has reached Φ and
control is pending. Its next pop marks false feedback only. The two
successful compile-and-run calls return `.ok (false, some 7, some 7)`
and `.ok (true, some 99, some 99)`, in retained-route, CF, numbered
order. The last two calls return `.error .bothMarked` and
`.error .neitherMarked`.
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Backends/Worklist/Regression.lean)

## Source correspondence

Click's Rice dissertation, *Combining Analyses, Combining Optimizations*
(1995), §3.5 on printed p. 25 requeues users when an equation's value
changes. This FIFO does so at the granularity of control, typed Φ
destinations and result. The underlying reachability and conditional
gates follow §3.6 Figure 3.7 and §3.7 Figure 3.8 on printed pp. 26 and 28.
The checked Rice scan has handle `1911/16807` and SHA-256
`30bec541a006b0a912cb5407b6a37758f8e6c1849ecb7dcfb48cfbf73df3be4c`.
[Rice dissertation](https://hdl.handle.net/1911/16807) ·
[Two-route SCCP equations](rice-loop-sccp-two-backedges.md)

Wegman and Zadeck's *Constant Propagation with Conditional Branches*,
TOPLAS 13(2), April 1991, pp. 181–210, DOI `10.1145/103135.103136`,
supplies the sparse conditional algorithm's executable-edge and
SSA-user scheduling baseline. Here one FIFO coordinates both kinds of
updates in a fixed pure quad. Whole-bank watches and the fixed
occurrence set delimit the implementation and its cost claims.
[Wegman–Zadeck](https://doi.org/10.1145/103135.103136) ·
[Existing typed single-feedback FIFO](rice-loop-sccp-split-fifo.md)
