module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Initial.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Thms

/-! # Structural initiality in the guarded Paper category -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Initial

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits Paper.TypeCategory
open Silmaril.DeBruijn (lift)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

set_option backward.isDefEq.respectTransparency false

theorem case_ignoring {A B : τ} {Γ L : List (τ)} {r : Region Φ}
    {i : Nat} (hi : At Γ i (Silmaril.coprod A B)) (hr : Region.HasType Γ r L) :
    Paper.Eqv Γ (.case (.var i) (r.renameVars Nat.succ) (r.renameVars Nat.succ)) r L := by
  have e := SubstitutionEquiv.caseValue (.var hi) (hr.renameVars (Ren.wk Γ (Silmaril.coprod A B)))
  have skip (a : Tm Φ) : Tm.replaceNewest a ∘ Nat.succ = Tm.var ∘ Nat.succ := rfl
  have drop : Tm.singleSubst (Tm.var (Φ := Φ) i) ∘ Nat.succ = Tm.var := rfl
  apply Paper.Eqv.cfgEta
  apply CfgEta.Eqv.native
  simpa only [substVars_renameVars, skip, drop, substVars_var, ← renameVars_eq_substVars] using e

private theorem unpack_ignoring {A B : τ} {Γ L : List (τ)} {r : Region Φ}
    {i : Nat} (hi : At Γ i (Silmaril.product A B)) (hr : Region.HasType Γ r L) :
    Paper.Eqv Γ (.let₂ (.var i) (r.renameVars (Nat.succ ∘ Nat.succ))) r L := by
  let eta : Paper.Eqv (Φ := Φ) Γ (.let₂ (.var i) (.br 0 (.pair (.var 1) (.var 0))))
      (.br 0 (.var i)) [Silmaril.product A B] := .productEta (.let₂Eta hi rfl)
  have hσ : LSubst.HasType Γ [Silmaril.product A B] L (fun _ => r.renameVars Nat.succ) := by
    intro _ C hC
    have h : C = Silmaril.product A B := List.mem_singleton.mp (List.mem_of_getElem? hC)
    subst C
    exact hr.renameVars (Ren.wk Γ _)
  have e := eta.lsubstPost
    (.let₂ (.var hi) (.br rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))))
    (.br rfl (.var hi)) hσ
  have drop : Tm.singleSubst (Tm.var (Φ := Φ) i) ∘ Nat.succ = Tm.var := rfl
  have inserted : Tm.singleSubst (Tm.pair (Φ := Φ) (.var 1) (.var 0)) ∘
      (lift Nat.succ ∘ (lift Nat.succ ∘ Nat.succ)) = Tm.var ∘ (Nat.succ ∘ Nat.succ) := rfl
  simpa only [lsubst, liftLSubstVars, renameVars_comp, substVars_renameVars, drop, inserted,
    substVars_var, ← renameVars_eq_substVars] using e

theorem eqv_of_empty_slot {P : τ} (hP : Paper.StructurallyEmpty P)
    {Γ L : List (τ)} {i : Nat} (hi : At Γ i P) {r s : Region Φ}
    (hr : Region.HasType Γ r L) (hs : Region.HasType Γ s L) : Paper.Eqv Γ r s L := by
  induction hP generalizing Γ i r s with
  | empty => exact .cfgEta (.native (.initial (.var hi) hr hs))
  | @sum A B _ _ ihA ihB =>
    have left : Ren Γ (A :: Γ) Nat.succ := Ren.wk Γ A
    have right : Ren Γ (B :: Γ) Nat.succ := Ren.wk Γ B
    exact (case_ignoring hi hr).symm.trans
      ((Paper.Eqv.case (.var hi)
        (ihA (i := 0) rfl (hr.renameVars left) (hs.renameVars left))
        (ihB (i := 0) rfl (hr.renameVars right) (hs.renameVars right))).trans (case_ignoring hi hs))
  | @left A B _ ih =>
    have shift := (Ren.wk Γ A).comp (Ren.wk (A :: Γ) B)
    exact (unpack_ignoring hi hr).symm.trans
      ((Paper.Eqv.let₂ (.var hi)
        (ih (i := 1) rfl (hr.renameVars shift) (hs.renameVars shift))).trans (unpack_ignoring hi hs))
  | @right A B _ ih =>
    have shift := (Ren.wk Γ A).comp (Ren.wk (A :: Γ) B)
    exact (unpack_ignoring hi hr).symm.trans
      ((Paper.Eqv.let₂ (.var hi)
        (ih (i := 0) rfl (hr.renameVars shift) (hs.renameVars shift))).trans (unpack_ignoring hi hs))

theorem initial {P : τ} (hP : Paper.StructurallyEmpty P) :
    Nonempty (IsInitial (ofType (Φ := Φ) P)) := by
  have collapse {Y : Paper.TypeCategory (τ := τ) Φ} (f g : ofType P ⟶ Y) : f = g := by
    obtain ⟨_, hf, rfl⟩ := exists_ofRegion f
    obtain ⟨_, hg, rfl⟩ := exists_ofRegion g
    exact (ofRegion_eq_iff hf hg).mpr (eqv_of_empty_slot hP (i := 0) rfl hf.hasType hg.hasType)
  exact ⟨IsInitial.ofUniqueHom (fun Y => iterate (coprod.inr : ofType P ⟶ Y ⨿ ofType P))
    (fun _ f => collapse f _)⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Initial
