module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.MLIR.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Numbered.Defs

/-! Check a two-route quad loop once and emit its two checked backends. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Tuple)

variable {regs : List (ValueSort Width)} {result : Width}

/-- Both artifacts come from the same successful singleton-feedback check. -/
structure Targets (p : Program Op regs (.data result)) where
  retained : Bool
  cf : Bypass.MLIR.CF.Target regs result
  numbered : Numbered.Target p

/-- Use the existing emitters on one shared dispatch certificate. -/
def emit [BankDecidableEq Word (dataPorts regs)]
    {p : Program Op regs (.data result)} {facts : Tuple (Fact Word) (dataPorts regs)}
    (checked : Checked model p facts) : Targets p :=
  ⟨checked.side, Bypass.MLIR.CF.lower checked, Numbered.lower checked⟩

/-- Run the fixed-point admission check on the original source and facts.
On success, both emitters consume that one certificate. -/
def compile [BankDecidableEq Word (dataPorts regs)]
    (p : Program Op regs (.data result)) (facts : Tuple (Fact Word) (dataPorts regs)) :
    Except Refusal (Targets p) :=
  (admit model p facts).map emit

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends
