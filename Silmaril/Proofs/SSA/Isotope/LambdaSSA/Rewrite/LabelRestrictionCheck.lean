module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Restriction.Check.Defs

/-! # Successful sparse readback preserves all written control -/

public section

universe u

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.LabelRestrictionCheck

open Silmaril.Isotope.LambdaSSA Silmaril.DeBruijn

theorem family {α : Type u} {n : Nat} {f : Fin n → Option α} {g : Fin n → α}
    (h : Region.checkFamily n f = some g) : ∀ i, f i = some (g i) := by
  induction n with
  | zero => exact fun i => Fin.elim0 i
  | succ n ih =>
      simp only [Region.checkFamily, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨head, hhead, tail, htail, rfl⟩ := h
      exact fun i => Fin.cases hhead (ih htail) i

theorem readback {Φ : Type u} (r : Region Φ) {bound : Nat} {ρ : Nat → Nat} {s : Region Φ}
    (ok : r.restrictLabels? bound ρ = some s) :
    s.LabelsBound bound ∧ s.renameLabels ρ = r := by
  induction r generalizing bound ρ s with
  | br i a =>
      cases hit : (List.finRange bound).find? (fun j => ρ j.val == i) with
      | none => simp [Region.restrictLabels?, hit] at ok
      | some j =>
          simp only [Region.restrictLabels?, hit, Option.some.injEq] at ok
          subst s
          have eq : ρ j.val = i := beq_iff_eq.mp (List.find?_some (p := fun k : Fin bound => ρ k.val == i) hit)
          exact ⟨j.isLt, by rw [Region.renameLabels, eq]⟩
  | case a l r ihl ihr =>
      simp only [Region.restrictLabels?, Option.bind_eq_some_iff, Option.some.injEq] at ok
      obtain ⟨l', hl, r', hr, rfl⟩ := ok
      obtain ⟨ls, le⟩ := ihl hl
      obtain ⟨rs, re⟩ := ihr hr
      exact ⟨⟨ls, rs⟩, by rw [Region.renameLabels, le, re]⟩
  | let₁ a body ih =>
      simp only [Region.restrictLabels?, Option.bind_eq_some_iff, Option.some.injEq] at ok
      obtain ⟨b, hb, rfl⟩ := ok
      obtain ⟨scope, eq⟩ := ih hb
      exact ⟨scope, by rw [Region.renameLabels, eq]⟩
  | let₂ a body ih =>
      simp only [Region.restrictLabels?, Option.bind_eq_some_iff, Option.some.injEq] at ok
      obtain ⟨b, hb, rfl⟩ := ok
      obtain ⟨scope, eq⟩ := ih hb
      exact ⟨scope, by rw [Region.renameLabels, eq]⟩
  | cfg entry n blocks ihe ihb =>
      simp only [Region.restrictLabels?, Option.bind_eq_some_iff, Option.some.injEq] at ok
      obtain ⟨e, he, bs, hbs, rfl⟩ := ok
      obtain ⟨es, ee⟩ := ihe he
      have rows := fun i => ihb i (family hbs i)
      refine ⟨⟨es, fun i => (rows i).1⟩, ?_⟩
      rw [Region.renameLabels, ee, funext (fun i => (rows i).2)]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.LabelRestrictionCheck
