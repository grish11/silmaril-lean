module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Worklist.Thms
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Defs

/-! Use the typed FIFO for the existing checked paired compilation. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist

open SeaOfNodes.Diamond (Model ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open RVSDG (Tuple)

universe u v w

/-- Project the drained worklist marking into the shared singleton checker.
Equality to the simultaneous marking is a proof argument. -/
def admit {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
    {regs : List (ValueSort Data)} {out : ValueSort Data}
    (m : Model.{u, v, w} Op) [BankDecidableEq m.value (dataPorts regs)]
    (p : Program Op regs out) (facts : Tuple (Fact m.value) (dataPorts regs)) :
    Except Refusal (Checked m p facts) :=
  admitWith m p facts (SCCP.Worklist.solve m p facts).1
    (congrArg Prod.fst (SCCP.Worklist.solve_eq_simultaneous m p facts))

open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)

def compile {regs : List (ValueSort Width)} {result : Width} [BankDecidableEq Word (dataPorts regs)]
    (p : Program Op regs (.data result)) (facts : Tuple (Fact Word) (dataPorts regs)) :
    Except Refusal (Targets p) :=
  (admit model p facts).map emit

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist
