module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Defs

/-! Bypass the empty dispatcher of the checked compact quad source. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass

open Diamond (Model Signature ValueSort dataPorts sortValue)
open Diamond.SCCP (Fact)
open SeaOfNodes.Loop.SCCP (BankDecidableEq)
open Blocks (Bank)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data}
variable {m : Model.{u, v, w} Op} {p : Program Op regs out}

/-- Keep compact entry 0, header 1, and feedback 3 in that order. -/
def retainedBlock (index : Fin 3) : Fin 4 :=
  if index = 2 then 3 else index.castSucc

def predecessor : SeaOfNodes.Loop.Incoming → Fin 3
  | .entry => 0
  | .backedge => 2

variable [BankDecidableEq m.value (dataPorts regs)]
variable {input : Tuple (Fact m.value) (dataPorts regs)}

/-- Keep the original header test and return port. On true, jump directly
to the retained feedback body. Admission comes from the fixed compact shape. -/
def bypass (checked : Checked m p input) : Tail.Source Op regs out :=
  fun index =>
    ⟨(compact checked (retainedBlock index)).body,
      if index = 1 then .branch p.again (.jump 2) (.ret p.result)
      else .transfer (.jump 1)⟩

def rewrite (m : Model.{u, v, w} Op) (p : Program Op regs out)
    [BankDecidableEq m.value (dataPorts regs)] (input : Tuple (Fact m.value) (dataPorts regs)) :
    Option (Tail.Source Op regs out) :=
  (check m p input).map bypass

/-- An actual finite source return, indexed by the number of taken feedback
steps before the returning header. -/
inductive ReturnsAfter (p : Program Op regs out) (m : Model.{u, v, w} Op) :
    Nat → Bank (regs := regs) m → sortValue m.value out → Prop where
  | exit {old value} (taken : p.step m old = .inl value) : ReturnsAfter p m 0 old value
  | feedback {count old side next value} (taken : p.step m old = .inr (side, next))
      (rest : ReturnsAfter p m count next value) : ReturnsAfter p m (count + 1) old value

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.SCCP.Dispatch.DeleteRoute.Bypass
