module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.Thms

/-! The worklist returns the same certificate or refusal and the same artifacts. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist

open SeaOfNodes.Diamond (Model ValueSort dataPorts)
open SeaOfNodes.Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open RVSDG (Tuple)

universe u v w

theorem admit_eq_simultaneous {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
    {regs : List (ValueSort Data)} {out : ValueSort Data}
    (m : Model.{u, v, w} Op) [BankDecidableEq m.value (dataPorts regs)]
    (p : Program Op regs out) (facts : Tuple (Fact m.value) (dataPorts regs)) :
    admit m p facts = Dispatch.admit m p facts :=
  Dispatch.admitWith_eq _ _

open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)

theorem compile_eq_simultaneous
    {regs : List (ValueSort Width)} {result : Width} [BankDecidableEq Word (dataPorts regs)]
    (p : Program Op regs (.data result)) (facts : Tuple (Fact Word) (dataPorts regs)) :
    compile p facts = Backends.compile p facts :=
  congrArg (Except.map emit) (admit_eq_simultaneous model p facts)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass.Backends.Worklist
