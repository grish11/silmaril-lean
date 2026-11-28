module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Structural.Defs

public section

namespace Silmaril.Isotope.LetSeq.StraightLine.Structural

open Silmaril.Isotope.Semantics (BoundEnv)

variable {α : Type}
set_option backward.isDefEq.respectTransparency false

theorem Split.env_append {n m k : Nat} {β : Context α n} {γ : Context α m} {δ : Context α k}
    (p : Split β γ) (q : Split γ δ) (ρ : BoundEnv Value β) :
    (p.append q).env ρ = q.env (p.env ρ) := by
  induction p with
  | nil => rfl
  | pair s next ih => exact ih q _

theorem Slot.value_rename_split {n m : Nat} {β : Context α n} {γ : Context α m} {A : Ty α}
    (p : Split β γ) (s : Slot β A) (ρ : BoundEnv Value β) :
    (s.rename p.rename).value (p.env ρ) = s.value ρ := by
  induction p with
  | nil => rfl
  | pair slot next ih =>
    exact ih ⟨s.1.succ.succ, s.2⟩ _

theorem Separates.mono {n : Nat} {β : Context α n} {ρ : BoundEnv Value β} {s t : Set Nat}
    (h : Separates ρ s) (le : s ⊆ t) : Separates ρ t :=
  ⟨h.injective, fun a slot => le (h.allocated a slot)⟩

def Shape.tokens : (s : Shape α) → Value s.ty → Set Nat
  | .atom _, a => {a}
  | .unit, _ => ∅
  | .pair a b, ab => a.tokens ab.1 ∪ b.tokens ab.2

def Shape.exposed : (s : Shape α) → Value s.ty → Set Nat
  | .atom _, a => {a}
  | .unit, _ | .pair _ _, _ => ∅

def Shape.pending : (s : Shape α) → Value s.ty → Set Nat
  | .atom _, _ | .unit, _ => ∅
  | .pair a b, ab => a.tokens ab.1 ∪ b.tokens ab.2

def Shape.distinct : (s : Shape α) → Value s.ty → Prop
  | .atom _, _ | .unit, _ => True
  | .pair a b, ab => a.distinct ab.1 ∧ b.distinct ab.2 ∧ Disjoint (a.tokens ab.1) (b.tokens ab.2)

theorem Shape.exposed_le {s : Shape α} (x : Value s.ty) : s.exposed x ⊆ s.tokens x := by
  cases s <;> first | exact Set.Subset.rfl | exact Set.empty_subset _

theorem Shape.pending_le {s : Shape α} (x : Value s.ty) : s.pending x ⊆ s.tokens x := by
  cases s <;> first | exact Set.Subset.rfl | exact Set.empty_subset _

theorem Shape.exposed_disjoint_pending {s : Shape α} (x : Value s.ty) :
    Disjoint (s.exposed x) (s.pending x) := by
  cases s <;> first | exact disjoint_bot_left | exact disjoint_bot_right

private theorem exposed_at_zero (s : Shape α) (x : Value s.ty) (a : α) (e : s.ty = .base a) :
    cast (congrArg Value e) x ∈ s.exposed x := by
  cases s with
  | atom b =>
    have eq := Ty.base.inj e
    subst a
    exact rfl
  | unit => cases e
  | pair l r => cases e

theorem Separates.snoc {n : Nat} {β : Context α n} {ρ : BoundEnv Value β} {used : Set Nat}
    (h : Separates ρ used) (s : Shape α) (x : Value s.ty) (fresh : Disjoint used (s.exposed x)) :
    Separates (ρ.snoc x) (used ∪ s.exposed x) where
  injective a := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    revert hi hj
    refine Fin.cases (fun hi => ?_) (fun i hi => ?_) i
    · refine Fin.cases (fun hj _ => rfl) (fun j hj eq => ?_) j
      have same : cast (congrArg Value hi) x = Slot.value (⟨j, hj⟩ : Slot β (.base a)) ρ := eq
      exact ((Set.disjoint_left.mp fresh) (h.allocated a ⟨j, hj⟩)
        (same ▸ exposed_at_zero s x a hi)).elim
    · refine Fin.cases (fun hj eq => ?_) (fun j hj eq => ?_) j
      · have same : cast (congrArg Value hj) x = Slot.value (⟨i, hi⟩ : Slot β (.base a)) ρ := eq.symm
        exact ((Set.disjoint_left.mp fresh) (h.allocated a ⟨i, hi⟩)
          (same ▸ exposed_at_zero s x a hj)).elim
      · have same := h.injective a (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) eq
        exact Subtype.ext (congrArg Fin.succ (congrArg Subtype.val same))
  allocated a := by
    rintro ⟨i, hi⟩
    revert hi
    refine Fin.cases (fun hi => ?_) (fun j hj => ?_) i
    · exact Or.inr (exposed_at_zero s x a hi)
    · exact Or.inl (h.allocated a ⟨j, hj⟩)

theorem unpack_separates {n : Nat} {β : Context α n} (s : Shape α) (slot : Slot β s.ty)
    (ρ : BoundEnv Value β) (used : Set Nat) (sep : Separates ρ used)
    (fresh : Disjoint used (s.pending (slot.value ρ))) (distinct : s.distinct (slot.value ρ)) :
    Separates ((s.unpack slot).split.env ρ) (used ∪ s.pending (slot.value ρ)) := by
  induction s generalizing n used with
  | atom a => exact sep.mono (Set.subset_union_left)
  | unit => exact sep.mono (Set.subset_union_left)
  | pair a b iha ihb =>
    let ab := slot.value ρ
    let ρ' := (ρ.snoc ab.1).snoc ab.2
    let used' := (used ∪ a.exposed ab.1) ∪ b.exposed ab.2
    let lslot : Slot ((β.snoc a.ty).snoc b.ty) a.ty := ⟨1, rfl⟩
    let rslot : Slot ((β.snoc a.ty).snoc b.ty) b.ty := ⟨0, rfl⟩
    let l := a.unpack lslot
    let r := b.unpack (rslot.rename l.split.rename)
    have ha : Disjoint used (a.tokens ab.1) := (Set.disjoint_union_right.mp fresh).1
    have hb : Disjoint used (b.tokens ab.2) := (Set.disjoint_union_right.mp fresh).2
    have hd : Disjoint (a.tokens ab.1) (b.tokens ab.2) := distinct.2.2
    have initial : Separates ρ' used' :=
      (sep.snoc a ab.1 (ha.mono_right (a.exposed_le ab.1))).snoc b ab.2
        (Set.disjoint_union_left.mpr ⟨hb.mono_right (b.exposed_le ab.2),
          hd.mono (a.exposed_le ab.1) (b.exposed_le ab.2)⟩)
    have leftFresh : Disjoint used' (a.pending ab.1) :=
      Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr
        ⟨ha.mono_right (a.pending_le ab.1), a.exposed_disjoint_pending ab.1⟩,
        hd.symm.mono (b.exposed_le ab.2) (a.pending_le ab.1)⟩
    have left : Separates (l.split.env ρ') (used' ∪ a.pending ab.1) :=
      iha lslot ρ' used' initial leftFresh distinct.1
    have rightValue : (rslot.rename l.split.rename).value (l.split.env ρ') = ab.2 :=
      Slot.value_rename_split l.split rslot ρ'
    have rightFresh : Disjoint (used' ∪ a.pending ab.1) (b.pending ab.2) :=
      Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr
        ⟨hb.mono_right (b.pending_le ab.2), hd.mono (a.exposed_le ab.1) (b.pending_le ab.2)⟩,
        b.exposed_disjoint_pending ab.2⟩, hd.mono (a.pending_le ab.1) (b.pending_le ab.2)⟩
    have right := ihb (rslot.rename l.split.rename) (l.split.env ρ') _ left
      (rightValue ▸ rightFresh) (rightValue ▸ distinct.2.1)
    change Separates ((l.split.append r.split).env ρ') (used ∪ (a.tokens ab.1 ∪ b.tokens ab.2))
    rw [Split.env_append]
    apply right.mono
    rw [rightValue]
    intro x hx
    rcases hx with (((hu | hla) | hrb) | hl) | hr
    · exact Or.inl hu
    · exact Or.inr (Or.inl (a.exposed_le _ hla))
    · exact Or.inr (Or.inr (b.exposed_le _ hrb))
    · exact Or.inr (Or.inl (a.pending_le _ hl))
    · exact Or.inr (Or.inr (b.pending_le _ hr))

theorem fresh_bounds (s : Shape α) (k : Nat) :
    ∀ x ∈ s.tokens (s.fresh k), k ≤ x ∧ x < k + s.leaves := by
  induction s generalizing k with
  | atom a =>
    intro x hx
    have h : x = k := hx
    subst x
    exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
  | unit => exact fun _ hx => hx.elim
  | pair a b iha ihb =>
    intro x hx
    rcases hx with hx | hx
    · have bounds := iha k x hx
      exact ⟨bounds.1, by simp only [Shape.leaves]; omega⟩
    · have bounds := ihb (k + a.leaves) x hx
      exact ⟨by omega, by simp only [Shape.leaves]; omega⟩

theorem fresh_distinct (s : Shape α) (k : Nat) : s.distinct (s.fresh k) := by
  induction s generalizing k with
  | atom | unit => trivial
  | pair a b iha ihb =>
    refine ⟨iha _, ihb _, Set.disjoint_left.mpr ?_⟩
    intro x hx hy
    have lower := (fresh_bounds b (k + a.leaves) x hy).1
    have upper := (fresh_bounds a k x hx).2
    omega

theorem fresh_after {n : Nat} {β : Context α n} {ρ : BoundEnv Value β} {k : Nat}
    (h : Separates ρ (Set.Iio k)) (s : Shape α) :
    Separates ((s.unpack (β := β.snoc s.ty) ⟨0, rfl⟩).split.env (ρ.snoc (s.fresh k)))
      (Set.Iio (k + s.leaves)) := by
  have away : Disjoint (Set.Iio k) (s.tokens (s.fresh k)) := Set.disjoint_left.mpr
    (fun _ hx hy => (Nat.not_lt_of_ge (fresh_bounds s k _ hy).1) hx)
  have added := h.snoc s (s.fresh k) (away.mono_right (s.exposed_le _))
  have rest := unpack_separates s ⟨0, rfl⟩ (ρ.snoc (s.fresh k)) _ added
    (Set.disjoint_union_left.mpr ⟨away.mono_right (s.pending_le _), s.exposed_disjoint_pending _⟩)
    (fresh_distinct s k)
  apply rest.mono
  intro x hx
  rcases hx with (old | exposed) | pending
  · exact Nat.lt_of_lt_of_le old (Nat.le_add_right _ _)
  · exact (fresh_bounds s k _ (s.exposed_le _ exposed)).2
  · exact (fresh_bounds s k _ (s.pending_le _ pending)).2

end Silmaril.Isotope.LetSeq.StraightLine.Structural
