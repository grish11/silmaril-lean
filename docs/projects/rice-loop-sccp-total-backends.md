# Compile the pure two-route quad at every SCCP marking

`Bypass.Backends.Total.compile program facts` returns a pair of typed
MLIR CF and numbered RVSDG artifacts in one of three outcomes. It takes the
same fixed five-block source, fixed-width word result, and
`BankDecidableEq Word (dataPorts regs)` instance as the specialist. It runs the certified SCCP FIFO
once and uses the existing dispatch admission.
[Total API](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Backends/Total/Defs.lean) ·
[Worklist compiler](rice-loop-sccp-two-route-worklist.md)

| Outcome | Feedback marks | Artifacts |
| --- | --- | --- |
| `.specialized` | Exactly one | Existing singleton-route bypass |
| `.twoLive` | Both | Original dispatch and both feedback routes |
| `.neitherMarked` | Neither | Original dispatch with its own outcome tag |

`compile_specialized_iff`, `compile_twoLive_iff` and
`compile_neitherMarked_iff` check the classification and the emitted
artifacts. The existing `Backends.compile` and `Backends.Worklist.compile`
continue to report their precise singleton-specialization refusals.
[Outcome and execution laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Backends/Total/Thms.lean) ·
[Specialization contract](rice-loop-sccp-compile-backends.md)

The original CF target uses the shared source-table emitter. It retains
the dispatch's original arm labels and passes each feedback block's full
typed bank to the header. The table also retains a label for source block
zero. The external entry runs that body directly and no edge revisits it.
The numbered target uses a shared entry γ to
test the first header before θ starts. A continuing θ body uses a second
γ to choose the original feedback column, runs the next header, and
returns its whole bank with the next test. An immediate exit reads the
first header's result at θ bound zero.
[CF frames](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/MLIR/CF/Thms.lean) ·
[Numbered packet and runner](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/Numbered/Thms.lean)

For feedback limit `n`, the matched budgets are `3 * n + 2` original
blocks, `3 * n + 3` original CF blocks, and `n` θ activations. The extra
CF visit is its explicit return block. The specialized CF budget remains
`2 * n + 3` for covered inputs. The original-emitter laws apply to every
typed input because the fallback retains the dispatch. `twoLive_run`
covers return and exhaustion at the matched budgets.
`twoLive_returns_iff` and `twoLive_noReturn_iff` preserve and reflect
finite return values and their absence across each runner's own bounds.

## Run the example

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Example
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Example
  (stoppingFacts)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Example
  (entry facts program looping)

#eval observations bothRoutes (facts .overdefined) (entry true true) 1
#eval observations bothRoutes (facts .overdefined) (entry true true) 2
#eval observations bothRoutes (facts .overdefined) (entry true false) 1
#eval observations bothRoutes (facts .overdefined) (entry false true) 0
#eval observations looping (facts .overdefined) (entry true true) 8
#eval observations program (facts (.constant ⟨true⟩)) (entry true true) 1
#eval observations program stoppingFacts (entry false true) 0
```

Each row gives the outcome and the source, CF, and numbered observations.

| Outcome | Source | CF | Numbered |
| --- | --- | --- | --- |
| `twoLive` | `none` | `none` | `none` |
| `twoLive` | `198` | `198` | `198` |
| `twoLive` | `14` | `14` | `14` |
| `twoLive` | `7` | `7` | `7` |
| `twoLive` | `none` | `none` | `none` |
| `specialized` | `99` | `99` | `99` |
| `neitherMarked` | `7` | `7` | `7` |

The returning run at limit two takes true feedback, writes `99`, and
selects false for the next dispatch. False feedback doubles that reaching
byte and stops. Entry with false selected reaches just the doubling route.
The immediate exit returns the original `7` without a feedback visit.
Lean also checks that the continuing fixture has no finite return in
either backend.
[Checked regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/SCCP/Dispatch/DeleteRoute/Bypass/Backends/Total/Regression.lean)

Rice §3.6 Figure 3.7 and §3.7 Figure 3.8 motivate the executable-edge
marks used to choose the outcome. The worklist guide pins the Rice scan
and the Wegman–Zadeck algorithm reference. The original emission covers
the fixed pure quad shape.
[Source correspondence](rice-loop-sccp-two-route-worklist.md#source-correspondence)
