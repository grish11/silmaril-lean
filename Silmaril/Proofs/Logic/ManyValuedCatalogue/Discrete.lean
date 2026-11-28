module

public import Silmaril.Logic.ManyValuedCatalogue.Discrete.Defs

public section

namespace Silmaril.Proofs.Logic.ManyValuedCatalogue

open Silmaril.Logic.ManyValuedCatalogue

namespace Post

theorem neg_val {n : ℕ} (x : Grid n) :
    (Post.neg x).val = if x = 0 then n + 1 else x.val - 1 :=
  Fin.coe_sub_one x

theorem neg_bijective (n : ℕ) : Function.Bijective (Post.neg : Grid n → Grid n) := by
  refine ⟨fun x y h => ?_, fun x => ⟨x + 1, ?_⟩⟩
  · exact sub_left_injective h
  · exact add_sub_cancel_right x 1

theorem designated_one {n : ℕ} (x : Grid n) : Post.designated 1 x ↔ Goedel.designated x := by
  simp only [Post.designated, Goedel.designated, Fin.ext_iff, Fin.val_top]
  have := x.isLt
  omega

end Post

namespace Bochvar

open Silmaril.Logic.ManyValuedCatalogue.Bochvar

theorem toGrid_injective : Function.Injective toGrid := by
  intro x y h
  cases x <;> cases y <;> first | rfl | contradiction

theorem toGrid_iff (x y : Bochvar) :
    toGrid (Bochvar.iff x y) =
      Goedel.and (Goedel.or (Grid.lukNeg (toGrid x)) (toGrid y))
        (Goedel.or (Grid.lukNeg (toGrid y)) (toGrid x)) := by
  cases x <;> cases y <;> rfl

end Bochvar

namespace Rose

open Silmaril.Logic.ManyValuedCatalogue.Rose

/-- Rose's Figure 3 assignment evaluates his distributivity formula to its third atom. -/
theorem diamond_distributivity_formula :
    let a : Diamond 3 := .atom 0
    let b : Diamond 3 := .atom 1
    let c : Diamond 3 := .atom 2
    Rose.imp (Rose.and (Rose.or a c) (Rose.or b c)) (Rose.or (Rose.and a b) c) = c := by
  decide

end Rose

namespace FaultValue

open Silmaril.Logic.ManyValuedCatalogue.FaultValue

theorem observations_injective :
    Function.Injective (fun x : FaultValue => (faultFree x, faulty x)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [faultFree, faulty, Prod.ext_iff]

theorem distinct : List.Nodup [zero, one, unknown, d, dBar] := by
  decide

theorem exhaustive (x : FaultValue) :
    x = zero ∨ x = one ∨ x = unknown ∨ x = d ∨ x = dBar := by
  cases x with
  | none => simp [unknown]
  | some pair =>
    rcases pair with ⟨good, bad⟩
    cases good <;> cases bad <;> simp [zero, one, d, dBar]

end FaultValue

theorem graphIndicator_unique {Input Output : Type*} [DecidableEq Output]
    (f : Input → Output) (input : Input) :
    ∃! output, graphIndicator f input output = true := by
  refine ⟨f input, by simp [graphIndicator], ?_⟩
  intro output h
  simpa [graphIndicator, eq_comm] using h

namespace Qudit

open Silmaril.Logic.ManyValuedCatalogue.Qudit

theorem relabel_basis {d : ℕ} {R : Type*} [Zero R] [One R] (p : Equiv.Perm (Fin d)) (i : Fin d) :
    relabel p (basis i : Fin d → R) = basis (p i) := by
  funext j
  simp [relabel, basis, Equiv.symm_apply_eq]

theorem relabel_inverse {d : ℕ} {R : Type*} (p : Equiv.Perm (Fin d)) (state : Fin d → R) :
    relabel p.symm (relabel p state) = state := by
  funext j
  simp [relabel]

end Qudit

end Silmaril.Proofs.Logic.ManyValuedCatalogue
