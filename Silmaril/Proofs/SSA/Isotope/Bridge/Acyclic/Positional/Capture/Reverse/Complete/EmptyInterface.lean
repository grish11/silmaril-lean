module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Complete.Defs
public import Silmaril.SSA.Isotope.LetCase.Structural.Finite.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse

open LetCase.Structural.Finite
open Region (packedExitType)
open scoped LetCase.Structural.Finite

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {n : Nat} {β : Context n}

private theorem assignment_exists (input : StructuralContext β) : Nonempty (Assignment β) := by
  induction input with
  | nil => exact ⟨fun i => i.elim0⟩
  | snoc _ shape ih =>
    obtain ⟨ρ⟩ := ih
    exact ⟨ρ.snoc shape.witness⟩

private theorem empty_head {t : LetCase.Structural.Finite.Term Φ 0} (p : Head .empty t) : False := by
  induction p with
  | ret v => cases v
  | request f _ _ _ _ _ ih => exact ih ((LetCase.Structural.Finite.Signature.target f).witness)

theorem finite_exits_proof {L : List Types} (input : StructuralContext β) (a : Operand Φ β (packedExitType L)) :
    L ≠ [] := by
  rintro rfl
  obtain ⟨ρ⟩ := assignment_exists input
  obtain ⟨_, head, _⟩ := normalize a.2 ρ
  exact empty_head head

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse
