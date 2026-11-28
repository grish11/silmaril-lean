module

public import Silmaril.Logic.ManyValued.Thms
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

@[simp] theorem toOptionBool_ofBool (b : Bool) : (ofBool b).toOptionBool = some b := by
  cases b <;> rfl

theorem ofBool_injective : Function.Injective ofBool := by
  intro a b h
  simpa using congrArg toOptionBool h

@[simp] theorem toOptionBool_ofOptionBool (x : Option Bool) :
    (ofOptionBool x).toOptionBool = x := by
  cases x with
  | none => rfl
  | some b => exact toOptionBool_ofBool b

@[simp] theorem ofOptionBool_toOptionBool (x : Bochvar) : ofOptionBool x.toOptionBool = x := by
  cases x <;> rfl

@[simp] theorem lift₂_unknown_left (f : Bool → Bool → Bool) (y : Bochvar) :
    lift₂ f .unknown y = .unknown := rfl

@[simp] theorem lift₂_unknown_right (f : Bool → Bool → Bool) (x : Bochvar) :
    lift₂ f x .unknown = .unknown := by
  cases x <;> rfl

@[simp] theorem lift₂_ofBool (f : Bool → Bool → Bool) (a b : Bool) :
    lift₂ f (ofBool a) (ofBool b) = ofBool (f a b) := by
  simp [lift₂, ofOptionBool]

theorem toOptionBool_lift₂ (f : Bool → Bool → Bool) (x y : Bochvar) :
    (lift₂ f x y).toOptionBool = x.toOptionBool.bind (fun a => y.toOptionBool.map (f a)) :=
  toOptionBool_ofOptionBool _

@[simp] theorem neg_ofBool (b : Bool) : neg (ofBool b) = ofBool (!b) := by
  cases b <;> rfl

theorem toOptionBool_neg (x : Bochvar) : (neg x).toOptionBool = x.toOptionBool.map Bool.not := by
  cases x <;> rfl

theorem iff_eq (x y : Bochvar) :
    Bochvar.iff x y = Bochvar.and (Bochvar.imp x y) (Bochvar.imp y x) := by
  cases x <;> cases y <;> rfl

theorem toGrid_injective : Function.Injective toGrid :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.Bochvar.toGrid_injective

theorem toGrid_neg (x : Bochvar) : toGrid (Bochvar.neg x) = Grid.lukNeg (toGrid x) := by
  cases x <;> rfl

/-- Weak biconditional agrees with the strong Kleene material biconditional
on these three indices. -/
theorem toGrid_iff (x y : Bochvar) :
    toGrid (Bochvar.iff x y) =
      Goedel.and (Goedel.or (Grid.lukNeg (toGrid x)) (toGrid y))
        (Goedel.or (Grid.lukNeg (toGrid y)) (toGrid x)) :=
  Silmaril.Proofs.Logic.ManyValuedCatalogue.Bochvar.toGrid_iff x y

open Silmaril.Logic.ManyValued (K3)

theorem k3_neg (x : K3) :
    neg (ofOptionBool x.toOptionBool) = ofOptionBool x.neg.toOptionBool := by
  cases x <;> rfl

theorem k3_materialIff (x y : K3) :
    iff (ofOptionBool x.toOptionBool) (ofOptionBool y.toOptionBool) =
      ofOptionBool (x.materialIff y).toOptionBool := by
  cases x <;> cases y <;> rfl

theorem k3_designated (x : K3) :
    designated (ofOptionBool x.toOptionBool) ↔ x.isDesignated = true := by
  cases x <;> simp [designated, ofOptionBool, ofBool, K3.toOptionBool, K3.isDesignated]

/-- Weak and strong conjunction give different values for false and unknown. -/
theorem and_unknown :
    and (ofOptionBool K3.ff.toOptionBool) (ofOptionBool K3.unknown.toOptionBool) = .unknown ∧
      ofOptionBool (K3.ff.conj K3.unknown).toOptionBool = .ff := by
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
