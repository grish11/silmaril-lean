module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Substitution
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.CfgEta

/-! # Preservation by native equations and CFG η
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift liftN)
open Silmaril.Isotope.LambdaSSA.Semantics (extend extend_rename)
open scoped Paper.BoundSimulation.Obstruction
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
  (UnitPayloadPolicy Env EnvTy Val ValTy Result ResultTy cfgRun
  cfgRun_out cfgRun_local cfgRun_fault cfgRun_diverges cfgRun_congr cfgRun_shiftOut mapOut shiftOut)

universe u v

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)]

variable {observation : TermObservation (α := α) Φ}

local notation "evalTerm" => evalTermWith observation
local notation "evalRegion" => evalRegionWith observation

set_option linter.concreteInstances false

variable [UnitPayloadPolicy]

def SameWith (observation : TermObservation (α := α) Φ) (Γ : VCtx (Ty α)) (r s : Region Φ) : Prop :=
  ∀ env, EnvTy Γ env → evalRegionWith observation r env = evalRegionWith observation s env

local notation "Same" => SameWith observation

theorem SameWith.refl (Γ : VCtx (Ty α)) (r : Region Φ) : Same Γ r r :=
  fun _ _ => rfl

theorem SameWith.symm {Γ : VCtx (Ty α)} {r s : Region Φ}
    (h : Same Γ r s) : Same Γ s r := fun env he => (h env he).symm

theorem SameWith.trans {Γ : VCtx (Ty α)} {r s t : Region Φ}
    (h : Same Γ r s) (h' : Same Γ s t) : Same Γ r t :=
  fun env he => (h env he).trans (h' env he)

theorem SameWith.let₁ {Γ : VCtx (Ty α)} {t : Tm Φ} {A : Ty α} {r s : Region Φ}
    (ht : Tm.HasType Γ t A) (h : Same (A :: Γ) r s) :
    Same Γ (.let₁ t r) (.let₁ t s) := by
  intro env he
  by_cases marked : (startsLet t && observation.boundUnaryLet) = true
  · simp [evalRegionWith, marked]
  · cases eq : evalTerm t env with
    | none => simp [evalRegionWith, marked, eq]
    | some v =>
      have hv := evalTerm_typed ht he eq
      simpa only [evalRegionWith, marked, Bool.false_eq_true, ite_false, eq] using h (extend env v) (he.extend hv)

theorem SameWith.let₂ {Γ : VCtx (Ty α)} {t : Tm Φ} {A B : Ty α} {r s : Region Φ}
    (ht : Tm.HasType Γ t (.product A B)) (h : Same (B :: A :: Γ) r s) :
    Same Γ (.let₂ t r) (.let₂ t s) := by
  intro env he
  by_cases marked : (observation.computedRegionLet₂ && computes t) = true
  · simp [evalRegionWith, marked]
  · cases eq : evalTerm t env with
    | none => simp [evalRegionWith, marked, eq]
    | some v =>
      have hv := evalTerm_typed ht he eq
      cases hv with
      | pair ha hb =>
        simpa only [evalRegionWith, marked, Bool.false_eq_true, ite_false, eq] using h _ ((he.extend ha).extend hb)

theorem SameWith.case {Γ : VCtx (Ty α)} {t : Tm Φ} {A B : Ty α} {l l' r r' : Region Φ}
    (ht : Tm.HasType Γ t (.coprod A B)) (hl : Same (A :: Γ) l l') (hr : Same (B :: Γ) r r') :
    Same Γ (.case t l r) (.case t l' r') := by
  intro env he
  cases eq : evalTerm t env with
  | none => simp [evalRegionWith, eq]
  | some v =>
    have hv := evalTerm_typed ht he eq
    cases hv with
    | inl hv => simpa only [evalRegionWith, eq] using hl _ (he.extend hv)
    | inr hv => simpa only [evalRegionWith, eq] using hr _ (he.extend hv)

theorem SameWith.cfg {Γ L : List (Ty α)} {n : Nat} {e e' : Region Φ}
    {bs bs' : Fin n → Region Φ} (R : Fin n → Ty α)
    (ht : HasType Γ e (List.ofFn R ++ L))
    (hbs : ∀ i, HasType (R i :: Γ) (bs i) (List.ofFn R ++ L))
    (he : Same Γ e e') (hb : ∀ i, Same (R i :: Γ) (bs i) (bs' i)) :
    Same Γ (.cfg e n bs) (.cfg e' n bs') := by
  intro env henv
  simp only [evalRegionWith, ← he env henv]
  exact cfgRun_congr R L (evalRegion_typed ht henv)
    (fun i _ hv => evalRegion_typed (hbs i) (henv.extend hv))
    (fun i _ hv => hb i _ (henv.extend hv))

theorem cfgEquiv_same {Γ L : List (Ty α)} {r s : Region Φ}
    (h : CfgEquiv Γ r s L) : Same Γ r s := by
  induction h with
  | refl _ => exact SameWith.refl _ _
  | symm _ ih => exact ih.symm
  | trans _ _ il ir => exact il.trans ir
  | let₁ ht _ ih => exact ih.let₁ ht
  | let₂ ht _ ih => exact ih.let₂ ht
  | case ht _ _ il ir => exact SameWith.case ht il ir
  | cfg R he hb ie ib => exact SameWith.cfg R he.typed.1 (fun i => (hb i).typed.1) ie ib
  | cfgZero ht bs =>
    intro env henv
    rw [evalRegionWith]
    cases evalRegion _ env with
    | jump i v => rw [cfgRun_out _ _ (Nat.zero_le i), Nat.sub_zero]
    | diverges => exact cfgRun_diverges 0 _
    | fault => exact cfgRun_fault 0 _
  | cfgBrExit R hi ht hb =>
    intro env henv
    obtain ⟨v, eq, hv⟩ := evalValue (observation := observation) ht henv
    simp only [evalRegionWith, eq]
    rw [cfgRun_out _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  | @cfgBrLocal Δ K n t bs R i ht hb =>
    intro env henv
    obtain ⟨v, eq, hv⟩ := evalValue (observation := observation) ht henv
    simp only [evalRegionWith, value_startsLet ht, Bool.false_and, Bool.false_eq_true, ite_false, eq]
    exact cfgRun_local _ _ i.isLt

theorem rewriteEquiv_same {Γ L : List (Ty α)} {r s : Region Φ}
    (h : RewriteEquiv Γ r s L) : Same Γ r s := by
  induction h with
  | entry he => exact cfgEquiv_same he
  | symm _ ih => exact ih.symm
  | trans _ _ il ir => exact il.trans ir
  | let₁ ht _ ih => exact ih.let₁ ht
  | let₂ ht _ ih => exact ih.let₂ ht
  | case ht _ _ il ir => exact SameWith.case ht il ir
  | cfg R he hb ie ib => exact SameWith.cfg R he.typed.1 (fun i => (hb i).typed.1) ie ib
  | letBr ht hb hi =>
    intro env henv
    obtain ⟨v, eq, hv⟩ := evalValue (observation := observation) ht henv
    simp only [evalRegionWith, value_startsLet ht, Bool.false_and, Bool.false_eq_true, ite_false,
      eq, evalTerm_subst _ (RealizesWith.single eq (value_not_computed ht))]
  | @caseInl _ t _ _ _ _ _ ha hl hr =>
    intro env he
    by_cases marked : (startsLet t && observation.boundUnaryLet) = true
    · simp [evalRegionWith, evalTermWith, marked]
    · cases eq : evalTerm t env <;> simp [evalRegionWith, evalTermWith, marked, eq]
  | @caseInr _ t _ _ _ _ _ hb hl hr =>
    intro env he
    by_cases marked : (startsLet t && observation.boundUnaryLet) = true
    · simp [evalRegionWith, evalTermWith, marked]
    · cases eq : evalTerm t env <;> simp [evalRegionWith, evalTermWith, marked, eq]

theorem caseCfg_same {Γ : List (Ty α)} {t : Tm Φ} {A B : Ty α} {l r : Region Φ}
    (ht : Tm.HasType Γ t (.coprod A B)) : Same Γ (.case t l r) (caseCfg t l r) := by
  intro env he
  cases eq : evalTerm t env with
  | none => simp [evalRegionWith, eq, caseCfg, cfgRun_fault]
  | some v =>
    have hv := evalTerm_typed ht he eq
    cases hv with
    | inl hv =>
      simp only [caseCfg, evalRegionWith, eq]
      change _ = cfgRun 2 _ (.jump 0 _) (markFeedback observation 2)
      rw [cfgRun_local _ _ (show 0 < 2 by decide)]
      change _ = cfgRun 2 _ (evalRegion (l.renameLabels (2 + ·)) _) (markFeedback observation 2)
      rw [evalRegion_renameLabels]
      exact (cfgRun_shiftOut 2 _ _).symm
    | inr hv =>
      simp only [caseCfg, evalRegionWith, eq]
      change _ = cfgRun 2 _ (.jump 1 _) (markFeedback observation 2)
      rw [cfgRun_local _ _ (show 1 < 2 by decide)]
      change _ = cfgRun 2 _ (evalRegion (r.renameLabels (2 + ·)) _) (markFeedback observation 2)
      rw [evalRegion_renameLabels]
      exact (cfgRun_shiftOut 2 _ _).symm

theorem substitutionEquiv_same {Γ L : List (Ty α)} {r s : Region Φ}
    (h : SubstitutionEquiv Γ r s L) : Same Γ r s := by
  induction h with
  | base he => exact rewriteEquiv_same he
  | symm _ ih => exact ih.symm
  | trans _ _ il ir => exact il.trans ir
  | let₁ ht _ ih => exact ih.let₁ ht
  | let₂ ht _ ih => exact ih.let₂ ht
  | case ht _ _ il ir => exact SameWith.case ht il ir
  | cfg R he hb ie ib => exact SameWith.cfg R he.typed.1 (fun i => (hb i).typed.1) ie ib
  | letValue ht hr =>
    intro env he
    obtain ⟨v, eq, hv⟩ := evalValue (observation := observation) ht he
    simp only [evalRegionWith, value_startsLet ht, Bool.false_and, Bool.false_eq_true, ite_false,
      eq, evalRegion_subst _ (RealizesWith.single eq (value_not_computed ht))]
  | @caseValue Δ t A B r K ht hr =>
    intro env he
    obtain ⟨v, eq, hv⟩ := evalValue (observation := observation) ht he
    rw [evalRegion_subst r (RealizesWith.single eq (value_not_computed ht))]
    cases hv with
    | inl hv =>
      simp only [evalRegionWith, eq]
      apply evalRegion_subst r
      intro i
      cases i <;> exact ⟨rfl, rfl⟩
    | inr hv =>
      simp only [evalRegionWith, eq]
      apply evalRegion_subst r
      intro i
      cases i <;> exact ⟨rfl, rfl⟩
  | caseCfg ht hl hr => exact caseCfg_same ht
  | initial ht hr hs =>
    intro env he
    obtain ⟨v, eq, hv⟩ := evalValue (observation := observation) ht he
    cases hv
  | cfgOutward R hr hb =>
    intro env he
    rw [evalRegionWith, evalRegion_renameLabels]
    exact cfgRun_shiftOut _ _ _

theorem eta_same {Γ L : List (Ty α)} {entry block : Region Φ} {A : Ty α}
    (he : ValueBranches Γ entry (A :: L)) :
    Same Γ (CfgEta.singleCfg entry block) (entry.lsubst (CfgEta.reentry block)) := by
  intro env henv
  let bs := fun (_ : Fin 1) v => evalRegion block (extend env v)
  have re (i : Nat) (v : Val) :
      evalRegion (CfgEta.reentry block i) (extend env v) = cfgRun 1 bs (.jump i v) := by
    change cfgRun 1 (fun _ w => evalRegion (block.renameVars (lift Nat.succ)) (extend (extend env v) w))
      (.jump i v) = _
    congr 1
    funext j w
    exact evalRegion_renameVars block
      (extend_rename (env := env) (env' := extend env v) (ρ := Nat.succ) (fun _ => rfl) w)
  rw [evalRegion_lsubst he henv]
  change cfgRun 1 bs (evalRegion entry env) = _
  cases evalRegion entry env with
  | jump i v => exact (re i v).symm
  | diverges => exact cfgRun_diverges 1 bs
  | fault => exact cfgRun_fault 1 bs

theorem cfgEta_same {Γ L : List (Ty α)} {r s : Region Φ}
    (h : CfgEta.Eqv Γ r s L) : Same Γ r s := by
  induction h with
  | native h => exact substitutionEquiv_same h
  | symm _ ih => exact ih.symm
  | trans _ _ il ir => exact il.trans ir
  | let₁ ht _ ih => exact ih.let₁ ht
  | let₂ ht _ ih => exact ih.let₂ ht
  | case ht _ _ il ir => exact SameWith.case ht il ir
  | cfg R he hb ie ib => exact SameWith.cfg R he.typed.1 (fun i => (hb i).typed.1) ie ib
  | @etaPost Γ entry A L block K σ he hb hσ =>
    intro env henv
    have hs : ValueBranches Γ (CfgEta.singleCfg entry block) L :=
      .cfg (fun _ : Fin 1 => _) he (fun _ => hb)
    have hre : LSubst.ValueFamily Γ (A :: L) L (CfgEta.reentry block) := by
      intro i T hi
      exact .cfg (fun _ : Fin 1 => _) (.br hi (.var (i := 0) rfl))
        (fun _ => hb.renameVars ((Ren.wk _ T).lift _))
    rw [evalRegion_lsubst hs henv, evalRegion_lsubst (he.lsubst hre) henv, eta_same he env henv]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer
