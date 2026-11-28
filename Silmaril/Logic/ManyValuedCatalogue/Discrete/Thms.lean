module

public import Silmaril.Logic.ManyValuedCatalogue.Discrete.Defs
import Silmaril.Proofs.Logic.ManyValuedCatalogue.Discrete

/-! Checked operations and encodings for the discrete catalogue. -/

public section

namespace Silmaril.Logic.ManyValuedCatalogue

namespace Post

theorem neg_val {n : ℕ} (x : Grid n) :
    (Post.neg x).val = if x = 0 then n + 1 else x.val - 1 :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.Post.neg_val x

theorem neg_bijective (n : ℕ) : Function.Bijective (Post.neg : Grid n → Grid n) :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.Post.neg_bijective n

theorem designated_one {n : ℕ} (x : Grid n) : Post.designated 1 x ↔ Goedel.designated x :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.Post.designated_one x

end Post

namespace Bochvar

@[simp] theorem lift₂_none_left (f : Bool → Bool → Bool) (y : Bochvar) :
    lift₂ f none y = none := rfl

@[simp] theorem lift₂_none_right (f : Bool → Bool → Bool) (x : Bochvar) :
    lift₂ f x none = none := by
  cases x <;> rfl

theorem lift₂_eq_some_iff (f : Bool → Bool → Bool) (x y : Bochvar) (b : Bool) :
    lift₂ f x y = some b ↔
      ∃ a c, x = some a ∧ y = some c ∧ f a c = b :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.Bochvar.lift₂_eq_some_iff f x y b

theorem iff_eq (x y : Bochvar) :
    Bochvar.iff x y = Bochvar.and (Bochvar.imp x y) (Bochvar.imp y x) :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.Bochvar.iff_eq x y

theorem toGrid_injective : Function.Injective toGrid :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.Bochvar.toGrid_injective

theorem toGrid_neg (x : Bochvar) : toGrid (Bochvar.neg x) = Grid.lukNeg (toGrid x) :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.Bochvar.toGrid_neg x

/-- Weak biconditional agrees with the strong Kleene material biconditional
on these three indices. -/
theorem toGrid_iff (x y : Bochvar) :
    toGrid (Bochvar.iff x y) =
      Goedel.and (Goedel.or (Grid.lukNeg (toGrid x)) (toGrid y))
        (Goedel.or (Grid.lukNeg (toGrid y)) (toGrid x)) :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.Bochvar.toGrid_iff x y

/-- False with an unknown input has different weak and strong conjunctions. -/
theorem and_unknown :
    toGrid (Bochvar.and (some false) none) = 1 ∧
      Goedel.and (toGrid (some false)) (toGrid none) = 0 := by
  decide

end Bochvar

namespace Rose

variable {A : Type*} [Lattice A] [BoundedOrder A] [DecidableEq A]

@[simp] theorem swapTop_top (a : A) : swapTop a ⊤ = a := Equiv.swap_apply_left ..

@[simp] theorem swapTop_self (a : A) : swapTop a a = ⊤ := Equiv.swap_apply_right ..

/-- Rose's Figure 3 assignment evaluates his distributivity formula to its third atom. -/
theorem diamond_distributivity_formula :
    let a : Diamond 3 := .atom 0
    let b : Diamond 3 := .atom 1
    let c : Diamond 3 := .atom 2
    Rose.imp (Rose.and (Rose.or a c) (Rose.or b c)) (Rose.or (Rose.and a b) c) = c :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.Rose.diamond_distributivity_formula

/-- On a three-element chain, the middle-to-bottom implications differ. -/
theorem imp_middle :
    Rose.imp (1 : Grid 1) ⊥ = ⊤ ∧ Goedel.imp (1 : Grid 1) ⊥ = ⊥ := by
  decide

end Rose

namespace FaultValue

theorem observations_injective :
    Function.Injective (fun x : FaultValue => (faultFree x, faulty x)) :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.FaultValue.observations_injective

theorem distinct : List.Nodup [zero, one, unknown, d, dBar] :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.FaultValue.distinct

theorem exhaustive (x : FaultValue) :
    x = zero ∨ x = one ∨ x = unknown ∨ x = d ∨ x = dBar :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.FaultValue.exhaustive x

end FaultValue

theorem graphIndicator_unique {Input Output : Type*} [DecidableEq Output]
    (f : Input → Output) (input : Input) :
    ∃! output, graphIndicator f input output = true :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.graphIndicator_unique f input

namespace Qudit

theorem relabel_basis {d : ℕ} {R : Type*} [Zero R] [One R] (p : Equiv.Perm (Fin d)) (i : Fin d) :
    relabel p (basis i : Fin d → R) = basis (p i) :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.Qudit.relabel_basis p i

theorem relabel_inverse {d : ℕ} {R : Type*} (p : Equiv.Perm (Fin d)) (state : Fin d → R) :
    relabel p.symm (relabel p state) = state :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.Qudit.relabel_inverse p state

end Qudit

end Silmaril.Logic.ManyValuedCatalogue
