# Compile one SCCP-pruned quad loop to both backends

`Bypass.Backends.compile program facts` takes the original typed
five-block `TwoBackedges.Program` and its abstract entry tuple. It uses
the fixed-width pure arithmetic and unsigned-comparison model shared by
MLIR CF and the numbered RVSDG lowering. The register sorts need a
`BankDecidableEq Word (dataPorts regs)` instance, and the source returns
one word. Compilation runs the existing simultaneous least-fixed-point
solver once. The dispatcher check passes the same singleton-feedback
certificate to both emitters. On success the result contains the retained
Boolean route, the typed `MLIR.CF.Cfg`, and the numbered
`NestedTheta.Graph`.
[Compiler API](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Backends/Defs.lean) ·
[CF lowering](rice-loop-sccp-bypass-mlir.md) ·
[Numbered lowering](rice-loop-sccp-bypass-numbered.md)

`compile_error_iff` characterizes refusal exactly by the solver's feedback
marks. `.bothMarked` means that both feedback occurrences remain possible
according to the analysis. `.neitherMarked` means that the singleton-route
pipeline has no feedback occurrence to retain. Either refusal leaves the
caller with the original source and no emitted pair. `compile_components`
identifies the selected mark and relates both fields to the separate
compilers.
[Dispatcher admission](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/Defs.lean) ·
[Compiler laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Backends/Thms.lean)

The observation theorems require `compile program facts = .ok targets`
and `TupleCovers facts input`. Coverage holds port by port. A constant
fact requires the concrete value to match it, an overdefined fact allows
any value, and bottom covers no value. For a feedback limit `n`,
`compile_run` compares return or exhaustion at source block budget
`3 * n + 2`, CF block budget `2 * n + 3`, and θ bound `n`.
`compile_returns_iff` and `compile_noReturn_iff` also compare finite
returns and their absence using each runner's own bound.

## Run the example

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Example
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example
  (facts program looping)

#eval observations program true false 1
#eval observations program true true 1
#eval observations program false true 0
#eval observations looping true true 9
#eval (compile program (facts .overdefined)).map Targets.retained
#eval (compile computesSelector (facts .overdefined)).map Targets.retained
#eval (compile program stoppingFacts).map Targets.retained
```

The first four evaluations return `.ok` with the retained route and the
source, CF and numbered observations. In order, they produce
`(false, some 7, some 7, some 7)`,
`(true, some 99, some 99, some 99)`,
`(true, some 7, some 7, some 7)`, and
`(true, none, none, none)`. The last three yield `.error .bothMarked`,
`.ok false`, and `.error .neitherMarked`. The middle call derives the
false route from a typed preheader computation even with an overdefined
entry selector. The unchanged source with those facts allows either
concrete route.
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Backends/Regression.lean)

## Source correspondence

Clifford Noel Click Jr.'s Rice dissertation, *Combining Analyses, Combining
Optimizations* (1995), §3.6 Figure 3.7 on printed p. 26 gives the cyclic
reachability equations. The checked scan is Rice handle `1911/16807`,
SHA-256 `30bec541a006b0a912cb5407b6a37758f8e6c1849ecb7dcfb48cfbf73df3be4c`.
Here `successors` marks branch occurrences, and `phiFacts` gates each
incoming column by its mark before joining it, corresponding to the
conditional equations in §3.7 Figure 3.8 on printed p. 28.
`solve` uses the simultaneous formulation before the worklist in §3.5,
in the order dual with optimistic bottom.
[Rice scan and inventory](sea-of-nodes/coverage.md#rice-dissertation) ·
[Dissertation record](https://hdl.handle.net/1911/16807) ·
[Typed equations](rice-loop-sccp-two-backedges.md)

Wegman and Zadeck, *Constant Propagation with Conditional Branches*,
ACM TOPLAS 13(2), April 1991, pp. 181–210, DOI
`10.1145/103135.103136`, supplies the executable-edge baseline.
This compiler consumes the two feedback marks of one fixed pure quad
shape. Its theorems concern the admission and the two existing emitters
for that shape.
[Wegman–Zadeck](https://doi.org/10.1145/103135.103136)
