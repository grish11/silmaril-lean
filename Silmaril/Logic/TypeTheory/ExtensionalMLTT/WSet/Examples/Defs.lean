module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet.Graph.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet.Examples

universe u

noncomputable section

/-- A concrete nullary W-node in the actual set carrier. -/
def leaf : carrier (SetSem.tt : ZFSet.{u}) (fun _ => ∅) :=
  sup (A := SetSem.tt) (B := fun _ => ∅) ⟨∅, by simp⟩
    (fun b => False.elim (ZFSet.notMem_empty b.val b.property))

/-- A graph-valued induction step whose motive is the singleton of `z`. -/
def constantStep (A : ZFSet.{u}) (B : ZFSet.{u} → ZFSet.{u}) (z : ZFSet.{u}) :
    ZFSet.{u} :=
  SetSem.lam A fun a =>
    SetSem.lam (SetSem.pi (B a) (fun _ => carrier A B)) fun _ =>
      SetSem.lam (SetSem.pi (B a) (fun _ => {z})) fun _ => z

end
end Silmaril.Logic.TypeTheory.ExtensionalMLTT.WSet.Examples
