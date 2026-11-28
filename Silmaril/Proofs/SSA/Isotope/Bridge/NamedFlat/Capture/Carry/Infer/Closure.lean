module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Capture.Carry.Infer.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Support.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Capture.Carry
open Silmaril.Isotope.LambdaSSA (FiniteCFG Flat)
open Silmaril.Isotope.LetCase.LocallyNameless (Tm)
open Morphism.CaseSSA (erase)

universe u
variable {F : Type u} {blocks exits labels n m k : Nat}

private theorem flat_scoped_iff (t : Flat F labels n) (bound : Nat) :
    t.erase.Scoped labels bound ↔ ∀ i, UsesVar t i → i < bound := by
  induction t generalizing bound with
  | br j a =>
    simp only [Flat.erase, LambdaSSA.Region.Scoped, UsesVar, j.isLt, true_and,
      LambdaSSA.Tm.scoped_iff_usesVar_lt]
  | let₁ _ _ first | let₂ _ _ first =>
    simp only [Flat.erase, LambdaSSA.Region.Scoped, UsesVar, LambdaSSA.Tm.scoped_iff_usesVar_lt,
      first, Silmaril.DeBruijn.older_bound, or_imp, forall_and]
  | case _ _ _ left right =>
    simp only [Flat.erase, LambdaSSA.Region.Scoped, UsesVar, LambdaSSA.Tm.scoped_iff_usesVar_lt,
      left, right, Silmaril.DeBruijn.older_bound, or_imp, forall_and]

private theorem flat_scoped (t : Flat F labels n) : t.erase.Scoped labels n := by
  induction t with
  | br i a => exact ⟨i.isLt, Morphism.CaseSSA.scoped_erase a⟩
  | let₁ a _ ih | let₂ a _ ih => exact ⟨Morphism.CaseSSA.scoped_erase a, ih⟩
  | case a _ _ left right => exact ⟨Morphism.CaseSSA.scoped_erase a, left, right⟩

private theorem operand_uses_rename (a : Tm Empty F m) (ρ : Fin m → Fin k) (i : Fin k)
    (used : (erase (a.rename ρ)).UsesVar i.val) :
    ∃ j : Fin m, (erase a).UsesVar j.val ∧ ρ j = i := by
  let ren (j : Nat) := if h : j < m then (ρ ⟨j, h⟩).val else 0
  have related (j : Fin m) : (ρ j).val = ren j.val := by simp [ren, j.isLt]
  rw [Morphism.CaseSSA.erase_rename ρ ren related, LambdaSSA.Tm.usesVar_rename] at used
  obtain ⟨j, found, eq⟩ := used
  have bound : j < m :=
    ((erase a).scoped_iff_usesVar_lt m).mp (Morphism.CaseSSA.scoped_erase a) j found
  exact ⟨⟨j, bound⟩, found, Fin.ext (by simpa [ren, bound] using eq)⟩

private theorem under_binder {ρ : Fin m → Fin k} {p : Nat → Prop} {slot i : Fin k}
    (used : (∃ j : Fin (m + 1), p j.val ∧ Tm.up ρ j = i.succ) ∨ slot.succ = i.succ) :
    (∃ j : Fin m, p (j.val + 1) ∧ ρ j = i) ∨ slot = i := by
  rcases used with ⟨j, found, eq⟩ | same
  · revert found eq
    refine Fin.cases (fun _ eq => (Fin.succ_ne_zero i eq.symm).elim) (fun j found eq => ?_) j
    exact .inl ⟨j, found, Fin.succ_inj.mp eq⟩
  · exact .inr (Fin.succ_inj.mp same)

private theorem body_uses (t : Flat F (blocks + exits) m) (ρ : Fin m → Fin k) (slot i : Fin k)
    (used : UsesVar (body t ρ slot) i.val) :
    (∃ j : Fin m, UsesVar t j.val ∧ ρ j = i) ∨ slot = i := by
  induction t generalizing k with
  | br target a =>
    revert used
    refine Fin.addCases (fun localTarget => ?_) (fun externalTarget => ?_) target
    · intro used
      simp only [body, Fin.addCases_left, UsesVar, erase, LambdaSSA.Tm.UsesVar] at used
      exact used.imp (operand_uses_rename a ρ i) (fun same => Fin.ext same.symm)
    · intro used
      simp only [body, Fin.addCases_right, UsesVar] at used
      exact .inl (operand_uses_rename a ρ i used)
  | let₁ a tail ih =>
    rcases used with arg | used
    · obtain ⟨j, found, eq⟩ := operand_uses_rename a ρ i arg
      exact .inl ⟨j, .inl found, eq⟩
    · exact (under_binder (ih (Tm.up ρ) slot.succ i.succ used)).imp
        (fun ⟨j, found, eq⟩ => ⟨j, .inr found, eq⟩) id
  | let₂ a tail ih =>
    rcases used with arg | used
    · obtain ⟨j, found, eq⟩ := operand_uses_rename a ρ i arg
      exact .inl ⟨j, .inl found, eq⟩
    · have once := under_binder (p := UsesVar tail) (ih (Tm.up (Tm.up ρ)) slot.succ.succ i.succ.succ used)
      exact (under_binder (p := fun j => UsesVar tail (j + 1)) once).imp
        (fun ⟨j, found, eq⟩ => ⟨j, .inr found, eq⟩) id
  | case a l r left right =>
    rcases used with discr | used | used
    · obtain ⟨j, found, eq⟩ := operand_uses_rename a ρ i discr
      exact .inl ⟨j, .inl found, eq⟩
    · exact (under_binder (left (Tm.up ρ) slot.succ i.succ used)).imp
        (fun ⟨j, found, eq⟩ => ⟨j, .inr (.inl found), eq⟩) id
    · exact (under_binder (right (Tm.up ρ) slot.succ i.succ used)).imp
        (fun ⟨j, found, eq⟩ => ⟨j, .inr (.inr found), eq⟩) id

private theorem graph_older {g : FiniteCFG F blocks exits n} {slot older : Fin n} {row : Fin blocks}
    (used : UsesVar ((graph g slot).block row) older.succ.val) :
    UsesVar (g.block row) older.succ.val ∧ older ≠ slot := by
  let index := older.succ.succ.succ
  change older.val + 1 = 0 ∨ UsesVar (body (g.block row) (decodedIndex slot) 0) index.val at used
  have tail := used.resolve_left (by omega)
  rcases body_uses _ (decodedIndex slot) 0 index tail with ⟨j, found, eq⟩ | eq
  · revert found eq
    refine Fin.cases (fun _ eq => ?_) (fun j found eq => ?_) j
    · have bound := congrArg Fin.val eq
      change 1 = older.val + 3 at bound
      omega
    · by_cases same : j = slot
      · simp only [decodedIndex, Fin.cases_succ, same, ↓reduceIte] at eq
        have bound := congrArg Fin.val eq
        change 0 = older.val + 3 at bound
        omega
      · simp only [decodedIndex, Fin.cases_succ, same, ↓reduceIte] at eq
        have olderEq : j = older := by
          apply Fin.ext
          have bound := congrArg Fin.val eq
          change j.val + 3 = older.val + 3 at bound
          omega
        subst j
        exact ⟨found, same⟩
  · have bound := congrArg Fin.val eq
    change 0 = older.val + 3 at bound
    omega

theorem graphList_older {g : FiniteCFG F blocks exits n} {slots : List (Fin n)} {older : Fin n} {row : Fin blocks}
    (used : UsesVar ((graphList g slots).block row) older.succ.val) :
    UsesVar (g.block row) older.succ.val ∧ older ∉ slots := by
  induction slots generalizing g with
  | nil => exact ⟨used, List.not_mem_nil⟩
  | cons slot rest ih =>
    obtain ⟨remains, missing⟩ := ih (g := graph g slot) used
    obtain ⟨original, different⟩ := graph_older remains
    exact ⟨original, by simp [different, missing]⟩

theorem mem_inferSlots (g : FiniteCFG F blocks exits n) (slot : Fin n) :
    slot ∈ inferSlots g ↔ ∃ i, UsesVar (g.block i) slot.succ.val := by
  simp [inferSlots, List.any_eq_true]

theorem packetOnly_of_covers (g : FiniteCFG F blocks exits n) (slots : List (Fin n))
    (covers : ∀ row slot, UsesVar (g.block row) slot.succ.val → slot ∈ slots) (row : Fin blocks) :
    ((graphList g slots).block row).erase.Scoped (blocks + exits) 1 := by
  apply (flat_scoped_iff _ _).mpr
  intro i used
  by_contra older
  have bounded := (flat_scoped_iff _ _).mp (flat_scoped _) i used
  let slot : Fin n := ⟨i - 1, by omega⟩
  have index : slot.succ.val = i := by
    change i - 1 + 1 = i
    omega
  rw [← index] at used
  obtain ⟨original, missing⟩ := graphList_older used
  exact missing (covers row slot original)

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Capture.Carry
