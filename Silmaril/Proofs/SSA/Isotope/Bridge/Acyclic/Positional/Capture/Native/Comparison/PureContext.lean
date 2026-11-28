module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Comparison.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Comparison.Pure
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Comparison.Replay
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture

open Silmaril.DeBruijn (lift)
open Region (HasType)
open Region.Paper
open Region.Paper.RetainedLet (returnOnce)
open Morphism.CaseSSA (erase erase_pure erase_hasType)

universe u v

variable {Φ : Type u} [HasTy Φ (Ty Empty)] {ε : Type v} [HasEff Φ ε] {pe : ε}
  {Γ : VCtx (Ty Empty)} {L : LCtx (Ty Empty)} {A B D : Ty Empty} {r s : Region Φ}

set_option backward.isDefEq.respectTransparency false

omit [HasTy Φ (Ty Empty)] in
private theorem closed_value_subst {a : Tm Φ} (h : Tm.BranchValue [] a A) (σ : Nat → Tm Φ) :
    a.subst σ = a := by
  induction h with
  | var bad => cases bad
  | unit => rfl
  | pair _ _ l r => exact congrArg₂ Tm.pair l r
  | inl _ h => exact congrArg Tm.inl h
  | inr _ h => exact congrArg Tm.inr h

omit [HasTy Φ (Ty Empty)] in
private theorem closed_value_weaken {a : Tm Φ} (h : Tm.BranchValue [] a A) :
    Tm.BranchValue Γ a A := by
  induction h with
  | var bad => cases bad
  | unit => exact .unit
  | pair _ _ l r => exact .pair l r
  | inl _ h => exact .inl h
  | inr _ h => exact .inr h

omit [HasTy Φ (Ty Empty)] in
private theorem drop_kept (r : Region Φ) :
    (r.renameVars (lift Nat.succ)).substVars (Tm.singleSubst (.var 0)) = r := by
  rw [Region.substVars_renameVars]
  have indices : Tm.singleSubst (.var 0 : Tm Φ) ∘ lift Nat.succ = Tm.var := by
    funext i
    cases i <;> rfl
  rw [indices, Region.substVars_var]

private theorem unit_expand (hr : HasType (Ty.unit :: Γ) r L) :
    ReplayEqv pe (Ty.unit :: Γ) r ((r.substVars (Tm.singleSubst .unit)).renameVars Nat.succ) L := by
  let k := r.renameVars (lift Nat.succ)
  have hk := hr.renameVars ((Ren.wk Γ Ty.unit).lift Ty.unit)
  have slot : Tm.BranchValue (Ty.unit :: Γ) (.var 0 : Tm Φ) Ty.unit := .var rfl
  have plugged := Extension.Eqv.lsubstPost (K := L) (σ := fun _ => k) (unit_branch (pe := pe) slot)
    (.br (ℓ := 0) rfl .unit) (.br (ℓ := 0) rfl slot)
    (fun _ _ had => (List.mem_singleton.mp (List.mem_of_getElem? had)).symm ▸ hk)
  change ReplayEqv pe (Ty.unit :: Γ) (k.substVars (Tm.singleSubst .unit))
    (k.substVars (Tm.singleSubst (.var 0))) L at plugged
  have unit : k.substVars (Tm.singleSubst .unit) = (r.substVars (Tm.singleSubst .unit)).renameVars Nat.succ := by
    dsimp only [k]
    rw [Region.substVars_renameVars, Region.renameVars_substVars]
    congr 1
    funext i
    cases i <;> rfl
  rw [unit, drop_kept] at plugged
  exact plugged.symm

private theorem specializeSum_typed {a : Tm Φ} (hr : HasType (D :: Γ) r L)
    (ha : Tm.HasType (A :: Γ) a D) : HasType (A :: Γ) (r.substVars (Tm.replaceNewest a)) L := by
  have wk : Tm.Subst.HasType (Φ := Φ) Γ (A :: Γ) (Tm.var ∘ Nat.succ) := by
    intro i X slot
    exact .var ((Ren.wk Γ A) slot)
  exact hr.substVars (Tm.Subst.HasType.cons wk ha)

omit [HasTy Φ (Ty Empty)] in
private theorem sum_arm (r : Region Φ) (v : Tm Φ) (h : v.rename (lift Nat.succ) = v) :
    (r.renameVars (lift Nat.succ)).substVars (Tm.replaceNewest v) =
      (r.substVars (Tm.replaceNewest v)).renameVars (lift Nat.succ) := by
  rw [Region.substVars_renameVars, Region.renameVars_substVars]
  congr 1
  funext i
  cases i with
  | zero => exact h.symm
  | succ i => rfl

private theorem sum_expand (hr : HasType (Ty.coprod A B :: Γ) r L) :
    ReplayEqv pe (Ty.coprod A B :: Γ) r
      (.case (.var 0) ((r.substVars (Tm.replaceNewest (.inl (.var 0)))).renameVars (lift Nat.succ))
        ((r.substVars (Tm.replaceNewest (.inr (.var 0)))).renameVars (lift Nat.succ))) L := by
  have spr : Tm.BranchValue (Ty.coprod A B :: Γ) (.var 0 : Tm Φ) (Ty.coprod A B) := .var rfl
  let k := r.renameVars (lift Nat.succ)
  have base := Extension.Eqv.paper (Seed := ReplaySeed pe)
    (.cfgEta (.native (.caseValue spr (hr.renameVars ((Ren.wk Γ (Ty.coprod A B)).lift (Ty.coprod A B))))))
  change ReplayEqv pe _ (.case (.var 0) (k.substVars (Tm.replaceNewest (.inl (.var 0))))
    (k.substVars (Tm.replaceNewest (.inr (.var 0))))) (k.substVars (Tm.singleSubst (.var 0))) L at base
  dsimp only [k] at base
  rw [drop_kept, sum_arm r (.inl (.var 0)) rfl, sum_arm r (.inr (.var 0)) rfl] at base
  exact base.symm

private def pairSpecialization (r : Region Φ) : Region Φ :=
  r.substVars (Tm.consSubst (.pair (.var 1) (.var 0)) (Tm.var ∘ (Nat.succ ∘ Nat.succ)))

private theorem specializePair_typed (hr : HasType (Ty.product A B :: Γ) r L) :
    HasType (B :: A :: Γ) (pairSpecialization r) L := by
  let wk := (Ren.wk Γ A).comp (Ren.wk (A :: Γ) B)
  have move : Tm.Subst.HasType (Φ := Φ) Γ (B :: A :: Γ) (Tm.var ∘ (Nat.succ ∘ Nat.succ)) := by
    intro i X slot
    exact .var (wk slot)
  exact hr.substVars (Tm.Subst.HasType.cons move (.pair (.var (i := 1) rfl) (.var (i := 0) rfl)))

private theorem pair_expand (hr : HasType (Ty.product A B :: Γ) r L) :
    ReplayEqv pe (Ty.product A B :: Γ) r
      (.let₂ (.var 0) ((pairSpecialization r).renameVars (lift (lift Nat.succ)))) L := by
  let P := Ty.product A B
  let k := r.renameVars (lift Nat.succ)
  have hk := hr.renameVars ((Ren.wk Γ P).lift P)
  have slot : Tm.BranchValue (P :: Γ) (.var 0 : Tm Φ) P := .var rfl
  have pair : Tm.BranchValue (B :: A :: P :: Γ) (.pair (.var 1) (.var 0) : Tm Φ) P :=
    .pair (.var (i := 1) rfl) (.var (i := 0) rfl)
  have step : ReplayEqv pe (P :: Γ) (.let₂ (.var 0) (.br 0 (.pair (.var 1) (.var 0))))
      (.br 0 (.var 0)) [P] :=
    .paper (.productEta (Region.ProductEta.Step.let₂Eta (Φ := Φ) (i := 0) (ℓ := 0) (A := A) (B := B) rfl rfl))
  have plugged := Extension.Eqv.lsubstPost (K := L) (σ := fun _ => k) step
    (.let₂ slot.hasType (.br (ℓ := 0) rfl pair)) (.br (ℓ := 0) rfl slot)
    (fun _ _ had => (List.mem_singleton.mp (List.mem_of_getElem? had)).symm ▸ hk)
  change ReplayEqv pe (P :: Γ) (.let₂ (.var 0)
    (((k.renameVars (lift Nat.succ)).renameVars (lift Nat.succ)).substVars
      (Tm.singleSubst (.pair (.var 1) (.var 0))))) (k.substVars (Tm.singleSubst (.var 0))) L at plugged
  have unpack :
      ((k.renameVars (lift Nat.succ)).renameVars (lift Nat.succ)).substVars
        (Tm.singleSubst (.pair (.var 1) (.var 0))) = (pairSpecialization r).renameVars (lift (lift Nat.succ)) := by
    dsimp only [k, pairSpecialization]
    rw [Region.renameVars_comp, Region.renameVars_comp, Region.substVars_renameVars, Region.renameVars_substVars]
    congr 1
    funext i
    cases i <;> rfl
  rw [unpack, drop_kept] at plugged
  exact plugged.symm

omit [HasTy Φ (Ty Empty)] in
private theorem specialize_sum_constructor (r : Region Φ) (v : Tm Φ) (tag : Tm Φ → Tm Φ)
    (h : (tag (.var 0)).subst (Tm.singleSubst v) = tag v) :
    (r.substVars (Tm.replaceNewest (tag (.var 0)))).substVars (Tm.singleSubst v) =
      r.substVars (Tm.singleSubst (tag v)) := by
  rw [Region.substVars_comp]
  congr 1
  funext i
  cases i with
  | zero => exact h
  | succ i => rfl

omit [HasTy Φ (Ty Empty)] in
private theorem specialize_pair_constructor (r : Region Φ) (v w : Tm Φ) (hw : Tm.BranchValue [] w B) :
    ((pairSpecialization r).substVars (Tm.singleSubst w)).substVars (Tm.singleSubst v) =
      r.substVars (Tm.singleSubst (.pair v w)) := by
  simp only [pairSpecialization, Region.substVars_comp]
  congr 1
  funext i
  cases i with
  | zero =>
    change Tm.pair v (w.subst (Tm.singleSubst v)) = Tm.pair v w
    rw [closed_value_subst hw]
  | succ i => rfl

/-- Constructor specialization suffices for replay at an atom-free input slot.
The sum and product rules preserve the older slots. -/
private theorem slot_ext (X : Ty Empty) (hr : HasType (X :: Γ) r L) (hs : HasType (X :: Γ) s L)
    (h : ∀ v, Tm.BranchValue [] v X →
      ReplayEqv pe Γ (r.substVars (Tm.singleSubst v)) (s.substVars (Tm.singleSubst v)) L) :
    ReplayEqv pe (X :: Γ) r s L := by
  induction X generalizing Γ r s with
  | base x => exact x.elim
  | empty => exact .paper (.cfgEta (.native (.initial (.var (i := 0) rfl) hr hs)))
  | unit => exact (unit_expand hr).trans (((h .unit .unit).renameVars (Ren.wk _ _)).trans (unit_expand hs).symm)
  | coprod A B ia ib =>
    have left : Tm.HasType (A :: Γ) (.inl (.var 0) : Tm Φ) (Ty.coprod A B) := .inl (.var (i := 0) rfl)
    have right : Tm.HasType (B :: Γ) (.inr (.var 0) : Tm Φ) (Ty.coprod A B) := .inr (.var (i := 0) rfl)
    have el := ia (specializeSum_typed hr left) (specializeSum_typed hs left) (by
      intro v hv
      rw [specialize_sum_constructor r v .inl rfl, specialize_sum_constructor s v .inl rfl]
      exact h (.inl v) (.inl hv))
    have er := ib (specializeSum_typed hr right) (specializeSum_typed hs right) (by
      intro v hv
      rw [specialize_sum_constructor r v .inr rfl, specialize_sum_constructor s v .inr rfl]
      exact h (.inr v) (.inr hv))
    exact (sum_expand hr).trans ((Extension.Eqv.case (.var (i := 0) rfl)
      (el.renameVars ((Ren.wk Γ (Ty.coprod A B)).lift A))
      (er.renameVars ((Ren.wk Γ (Ty.coprod A B)).lift B))).trans (sum_expand hs).symm)
  | product A B ia ib =>
    have rt := specializePair_typed hr
    have st := specializePair_typed hs
    have fields := ib rt st (by
      intro w hw
      let wk : Tm.BranchValue (A :: Γ) w B := closed_value_weaken hw
      apply ia (rt.substVars (Tm.Subst.HasType.single wk.hasType))
        (st.substVars (Tm.Subst.HasType.single wk.hasType))
      intro v hv
      rw [specialize_pair_constructor r v w hw, specialize_pair_constructor s v w hw]
      exact h (.pair v w) (.pair hv hw))
    exact (pair_expand hr).trans ((Extension.Eqv.let₂ (.var (i := 0) rfl)
      (fields.renameVars (((Ren.wk Γ (Ty.product A B)).lift A).lift B))).trans (pair_expand hs).symm)

omit [HasTy Φ (Ty Empty)] in
private theorem close_cons (r : Region Φ) {v : Tm Φ} (hv : Tm.BranchValue [] v A) (σ : Nat → Tm Φ) :
    (r.substVars (Tm.singleSubst v)).substVars σ = r.substVars (Tm.consSubst v σ) := by
  rw [Region.substVars_comp]
  congr 1
  funext i
  cases i with
  | zero => exact closed_value_subst hv σ
  | succ i => rfl

private theorem context_ext (hr : HasType Γ r L) (hs : HasType Γ s L)
    (h : ∀ σ, ConstructorSubst Γ σ → ReplayEqv pe [] (r.substVars σ) (s.substVars σ) L) :
    ReplayEqv pe Γ r s L := by
  induction Γ generalizing r s with
  | nil =>
    simpa only [Region.substVars_var] using (h Tm.var (ConstructorSubst.nil Tm.var))
  | cons X Γ ih =>
    apply slot_ext X hr hs
    intro v hv
    have sv := Tm.Subst.HasType.single (closed_value_weaken (Γ := Γ) hv).hasType
    apply ih (hr.substVars sv) (hs.substVars sv)
    intro σ vals
    rw [close_cons r hv σ, close_cons s hv σ]
    exact h _ (vals.cons hv)

omit [HasTy Φ (Ty Empty)] in
private theorem subst_commuted (k a : Tm Φ) (σ : Nat → Tm Φ) :
    (k.subst (Tm.singleSubst a)).subst σ =
      (k.subst (Tm.liftSubst σ)).subst (Tm.singleSubst (a.subst σ)) := by
  rw [subst_lift_single, Tm.subst_comp]
  congr 1
  funext i
  cases i <;> rfl

theorem pure_beta_proof (noPure : ∀ f : Φ, ¬ IsPure pe f) {a b : Tm Φ}
    (pure : Tm.Pure pe a) (ha : Tm.HasType Γ a A) (hb : Tm.HasType (A :: Γ) b D) :
    ReplayEqv pe Γ (returnOnce (.let₁ a b)) (returnOnce (b.subst (Tm.singleSubst a))) [D] := by
  have h := UnaryReturn.returnOnce_valueBranches (.let₁ ha hb)
  have k := UnaryReturn.returnOnce_valueBranches (hb.subst (Tm.Subst.HasType.single ha))
  apply context_ext h.hasType k.hasType
  intro σ values
  have typed := values.typed
  obtain ⟨v, hv, e⟩ := normalize_pure noPure ha pure values
  change ReplayEqv pe [] (returnOnce (.let₁ (a.subst σ) (b.subst (Tm.liftSubst σ))))
    (returnOnce ((b.subst (Tm.singleSubst a)).subst σ)) [D]
  rw [subst_commuted]
  exact let_beta_of_value (ha.subst typed) (hb.subst (typed.lift A)) hv e

theorem pureLetBetaReplay_proof (noPure : ∀ f : Φ, ¬ IsPure pe f) :
    PureLetBetaReplay (α := Empty) (Ψ := Φ) pe := by
  intro n β a b A B pure ha hb _
  rw [erase_instantiate_single]
  exact pure_beta_proof noPure (erase_pure pure) (erase_hasType ha) (erase_hasType hb)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
