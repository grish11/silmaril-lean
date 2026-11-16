module

public import Silmaril.Logic.Egg.Core.Examples.Defs
public import Silmaril.Logic.Egg.Core.Thms

@[expose] public section

namespace Silmaril.Logic.Egg.Core.Examples

open Silmaril.Logic.Institution.Examples

private theorem instantiate_zero {n m : Nat} (δ : Fin n → Term m) :
    Pattern.instantiate δ (zero (n := n)) = zero := by
  change (.app .zero _ : Term m) = (.app .zero _ : Term m)
  congr 1
  funext i
  exact Fin.elim0 i

private theorem instantiate_add {n m : Nat} (δ : Fin n → Term m) (x y : Term n) :
    Pattern.instantiate δ (add x y) = add (Pattern.instantiate δ x) (Pattern.instantiate δ y) := by
  change (.app .add _ : Term m) = (.app .add _ : Term m)
  congr 1
  funext i
  refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

/-- Normalization of the two rule steps in the captured official engine explanation.
The capture tool is separate; this finite certificate is replayed in Lean. -/
theorem fixture_certificate : Explanation rules ∅ initial a := by
  apply Explanation.trans (b := add a zero)
  · have h := Explanation.rewrite (premises := (∅ : Set (Equality signature (context 0))))
      addZero (Set.mem_singleton _) (fun _ => add a zero) (fun _ he => by cases he)
    simpa only [rules, initial, addZero, instantiate_add, instantiate_zero, Pattern.instantiate] using h
  · have h := Explanation.rewrite (premises := (∅ : Set (Equality signature (context 0))))
      addZero (Set.mem_singleton _) (fun _ => a) (fun _ he => by cases he)
    simpa only [rules, initial, addZero, instantiate_add, instantiate_zero, Pattern.instantiate] using h

theorem addZero_holds : addZero.Holds model := by
  intro ρ _
  change Fin 1 → Nat at ρ
  change ρ (0 : Fin 1) + 0 = ρ 0
  exact Nat.add_zero _

theorem fixture_sound : initial.eval model Fin.elim0 = a.eval model Fin.elim0 :=
  explanation_sound model Fin.elim0 (fun _r hr => (Set.mem_singleton_iff.mp hr) ▸ addZero_holds)
    (fun _ he => False.elim he) fixture_certificate

theorem guarded_holds : guarded.Holds model := by
  intro ρ h
  change Fin 2 → Nat at ρ
  have hz : ρ (0 : Fin 2) = 0 := by
    exact h (⟨(), .var 0, zero⟩ : Equality signature (context 2)) (.head _)
  change ρ 0 + ρ 1 = ρ 1
  rw [hz, Nat.zero_add]

theorem omitted_guard_false : ¬ (add (n := 0) a zero).eval model Fin.elim0 = zero.eval model Fin.elim0 := by
  change ¬ (7 : Nat) = 0
  decide

/-- An arbitrary trusted union is not accepted as semantic evidence. -/
theorem no_unjustified_union : ¬ Explanation (∅ : Set (Rule signature)) ∅ (a (n := 0)) zero := by
  intro h
  have impossible : (7 : Nat) = 0 := explanation_sound model Fin.elim0
    (fun _ he => False.elim he) (fun _ he => False.elim he) h
  cases impossible

end Silmaril.Logic.Egg.Core.Examples
