module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.CheckedEntry.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.Observation.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.CheckedEntry.Correctness

/-! Correctness of concrete entry dispatch without a coverage hypothesis. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.CheckedEntry

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {result : Width} {p : Program Op regs (.data result)}

/-- The selected artifacts match the original source on the checked input,
both at the typed budget correspondence and for all finite returns. -/
theorem dispatch_correct [BankDecidableEq Word (dataPorts regs)] (prepared : Prepared p)
    (input : Bank (regs := regs) model) : (dispatch prepared input).execution.Correct p input :=
  Proofs.dispatch_correct prepared input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Total.CheckedEntry
