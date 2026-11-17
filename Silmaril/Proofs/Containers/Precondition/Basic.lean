module

public import Silmaril.Containers.Precondition.Defs
public import Silmaril.Containers.Runtime.Thms

/-!
# Proofs: preconditions under explicit environment assumptions

Proofs for `Silmaril.Containers.Precondition.Thms`. Nothing imports this module except that header.
-/

@[expose] public section

namespace Silmaril.Proofs.Containers.Precondition

open Silmaril.Containers

variable {I P E : Type}

theorem vpreAssuming_of_restrict {R : Runtime I P E} {isIn : E → Bool} {A : List E → Prop}
    {φ : Spec E} {i : I} (h : vpre (R.restrict (Spec.onInputs isIn A)) φ i) :
    vpreAssuming R isIn A φ i := by
  intro b hb hA
  apply h b
  cases hl : R.load i with
  | error r =>
    exact (Runtime.beh_error (R := R.restrict _) hl b).2 ((Runtime.beh_error hl b).1 hb)
  | ok p =>
    obtain ⟨b₀, hs, ho⟩ := (Runtime.beh_ok hl b).1 hb
    exact (Runtime.beh_ok (R := R.restrict _) hl b).2 ⟨b₀, hs, ho, .inl hA⟩

/-- The model of the counterexample: the input `true` leads to undefined behaviour, the input
`false` to exit 0. -/
def twoInputs : Runtime Unit Unit Bool :=
  Runtime.exact (fun _ => .ok ())
    (fun _ b => b = .done [true] (.undefined .other) ∨ b = .done [false] (.exited 0))

theorem restrict_strictly_conservative :
    vpreAssuming twoInputs id (fun t => true ∉ t) (fun _ => True) () ∧
      ¬ vpre (twoInputs.restrict (Spec.onInputs id fun t => true ∉ t)) (fun _ => True) () := by
  constructor
  · intro b hb hA
    obtain ⟨b₀, hs, rfl⟩ := (Runtime.beh_ok (R := twoInputs) rfl b).1 hb
    rcases hs with rfl | rfl
    · exact (hA [true] (List.prefix_refl _) (by simp)).elim
    · exact ⟨trivial, trivial⟩
  · intro h
    exact (h (.done [true] (.undefined .other))
      ((Runtime.beh_ok (R := twoInputs.restrict _) rfl _).2
        ⟨_, .inl rfl, rfl, .inr id⟩)).1

end Silmaril.Proofs.Containers.Precondition
