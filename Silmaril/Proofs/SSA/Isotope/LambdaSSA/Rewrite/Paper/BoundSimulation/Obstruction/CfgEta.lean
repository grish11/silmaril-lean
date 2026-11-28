module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Substitution
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Thms

/-! # Preservation by native and CFG η equations
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift liftN)
open Silmaril.Isotope.LambdaSSA.Semantics (extend extend_rename)
open scoped Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction
open scoped Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer.AlternateUnit

def Same (Γ : VCtx (Ty Empty)) (r s : Region Empty) : Prop :=
  ∀ env, EnvTy Γ env → evalRegion r env = evalRegion s env

theorem Same.refl (Γ : VCtx (Ty Empty)) (r : Region Empty) : Same Γ r r :=
  fun _ _ => rfl

theorem Same.symm {Γ : VCtx (Ty Empty)} {r s : Region Empty}
    (h : Same Γ r s) : Same Γ s r := fun env he => (h env he).symm

theorem Same.trans {Γ : VCtx (Ty Empty)} {r s t : Region Empty}
    (h : Same Γ r s) (h' : Same Γ s t) : Same Γ r t :=
  fun env he => (h env he).trans (h' env he)

theorem Same.let₁ {Γ : VCtx (Ty Empty)} {t : Tm Empty} {A : Ty Empty} {r s : Region Empty}
    (ht : Tm.HasType Γ t A) (h : Same (A :: Γ) r s) :
    Same Γ (.let₁ t r) (.let₁ t s) := by
  intro env he
  cases eq : evalTerm t env with
  | none => simp [evalRegion, eq]
  | some v =>
    have hv := evalTerm_typed ht he eq
    simpa only [evalRegion, eq] using h (extend env v) (he.extend hv)

theorem Same.let₂ {Γ : VCtx (Ty Empty)} {t : Tm Empty} {A B : Ty Empty} {r s : Region Empty}
    (ht : Tm.HasType Γ t (.product A B)) (h : Same (B :: A :: Γ) r s) :
    Same Γ (.let₂ t r) (.let₂ t s) := by
  intro env he
  cases eq : evalTerm t env with
  | none => simp [evalRegion, eq]
  | some v =>
    have hv := evalTerm_typed ht he eq
    cases hv with
    | pair ha hb =>
      simpa only [evalRegion, eq] using h _ ((he.extend ha).extend hb)

theorem Same.case {Γ : VCtx (Ty Empty)} {t : Tm Empty} {A B : Ty Empty} {l l' r r' : Region Empty}
    (ht : Tm.HasType Γ t (.coprod A B)) (hl : Same (A :: Γ) l l') (hr : Same (B :: Γ) r r') :
    Same Γ (.case t l r) (.case t l' r') := by
  intro env he
  cases eq : evalTerm t env with
  | none => simp [evalRegion, eq]
  | some v =>
    have hv := evalTerm_typed ht he eq
    cases hv with
    | inl hv => simpa only [evalRegion, eq] using hl _ (he.extend hv)
    | inr hv => simpa only [evalRegion, eq] using hr _ (he.extend hv)

theorem Same.cfg {Γ L : List (Ty Empty)} {n : Nat} {e e' : Region Empty}
    {bs bs' : Fin n → Region Empty} (R : Fin n → Ty Empty)
    (ht : HasType Γ e (List.ofFn R ++ L))
    (hbs : ∀ i, HasType (R i :: Γ) (bs i) (List.ofFn R ++ L))
    (he : Same Γ e e') (hb : ∀ i, Same (R i :: Γ) (bs i) (bs' i)) :
    Same Γ (.cfg e n bs) (.cfg e' n bs') := by
  intro env henv
  simp only [evalRegion, ← he env henv]
  exact cfgRun_congr R L (evalRegion_typed ht henv)
    (fun i _ hv => evalRegion_typed (hbs i) (henv.extend hv))
    (fun i _ hv => hb i _ (henv.extend hv))

theorem cfgRun_shiftOut {mark : Bool} (n : Nat) (bs : Fin n → Val → Result) (r : Result) :
    cfgRun n bs (shiftOut n r) mark = r :=
  finish_of_terminal bs _ (k := 0) (enter_shiftOut n r)

theorem cfgEquiv_same {Γ L : List (Ty Empty)} {r s : Region Empty}
    (h : CfgEquiv Γ r s L) : Same Γ r s := by
  induction h with
  | refl _ => exact Same.refl _ _
  | symm _ ih => exact ih.symm
  | trans _ _ il ir => exact il.trans ir
  | let₁ ht _ ih => exact ih.let₁ ht
  | let₂ ht _ ih => exact ih.let₂ ht
  | case ht _ _ il ir => exact Same.case ht il ir
  | cfg R he hb ie ib => exact Same.cfg R he.typed.1 (fun i => (hb i).typed.1) ie ib
  | cfgZero ht bs =>
    intro env henv
    rw [evalRegion]
    cases evalRegion _ env with
    | jump i v => rw [cfgRun_out _ _ (Nat.zero_le i), Nat.sub_zero]
    | diverges => exact cfgRun_diverges 0 _
    | fault => exact cfgRun_fault 0 _
  | cfgBrExit R hi ht hb =>
    intro env henv
    obtain ⟨v, eq, hv⟩ := evalValue ht henv
    simp only [evalRegion, eq]
    rw [cfgRun_out _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  | @cfgBrLocal Δ K n t bs R i ht hb =>
    intro env henv
    obtain ⟨v, eq, hv⟩ := evalValue ht henv
    simp only [evalRegion, eq]
    exact cfgRun_local _ _ i.isLt

theorem rewriteEquiv_same {Γ L : List (Ty Empty)} {r s : Region Empty}
    (h : RewriteEquiv Γ r s L) : Same Γ r s := by
  induction h with
  | entry he => exact cfgEquiv_same he
  | symm _ ih => exact ih.symm
  | trans _ _ il ir => exact il.trans ir
  | let₁ ht _ ih => exact ih.let₁ ht
  | let₂ ht _ ih => exact ih.let₂ ht
  | case ht _ _ il ir => exact Same.case ht il ir
  | cfg R he hb ie ib => exact Same.cfg R he.typed.1 (fun i => (hb i).typed.1) ie ib
  | letBr ht hb hi =>
    intro env henv
    obtain ⟨v, eq, hv⟩ := evalValue ht henv
    simp only [evalRegion, eq, evalTerm_subst _ (Realizes.single eq)]
  | @caseInl _ t _ _ _ _ _ ha hl hr =>
    intro env he
    cases eq : evalTerm t env <;> simp [evalRegion, evalTerm, eq]
  | @caseInr _ t _ _ _ _ _ hb hl hr =>
    intro env he
    cases eq : evalTerm t env <;> simp [evalRegion, evalTerm, eq]

theorem caseCfg_same {Γ : List (Ty Empty)} {t : Tm Empty} {A B : Ty Empty} {l r : Region Empty}
    (ht : Tm.HasType Γ t (.coprod A B)) : Same Γ (.case t l r) (caseCfg t l r) := by
  intro env he
  cases eq : evalTerm t env with
  | none => simp [evalRegion, eq, caseCfg, cfgRun_fault]
  | some v =>
    have hv := evalTerm_typed ht he eq
    cases hv with
    | inl hv =>
      simp only [caseCfg, evalRegion, eq]
      change _ = cfgRun 2 _ (.jump 0 _)
      rw [cfgRun_local _ _ (show 0 < 2 by decide)]
      change _ = cfgRun 2 _ (evalRegion (l.renameLabels (2 + ·)) _)
      rw [evalRegion_renameLabels]
      exact (cfgRun_shiftOut 2 _ _).symm
    | inr hv =>
      simp only [caseCfg, evalRegion, eq]
      change _ = cfgRun 2 _ (.jump 1 _)
      rw [cfgRun_local _ _ (show 1 < 2 by decide)]
      change _ = cfgRun 2 _ (evalRegion (r.renameLabels (2 + ·)) _)
      rw [evalRegion_renameLabels]
      exact (cfgRun_shiftOut 2 _ _).symm

theorem substitutionEquiv_same {Γ L : List (Ty Empty)} {r s : Region Empty}
    (h : SubstitutionEquiv Γ r s L) : Same Γ r s := by
  induction h with
  | base he => exact rewriteEquiv_same he
  | symm _ ih => exact ih.symm
  | trans _ _ il ir => exact il.trans ir
  | let₁ ht _ ih => exact ih.let₁ ht
  | let₂ ht _ ih => exact ih.let₂ ht
  | case ht _ _ il ir => exact Same.case ht il ir
  | cfg R he hb ie ib => exact Same.cfg R he.typed.1 (fun i => (hb i).typed.1) ie ib
  | letValue ht hr =>
    intro env he
    obtain ⟨v, eq, hv⟩ := evalValue ht he
    simp only [evalRegion, eq, evalRegion_subst _ (Realizes.single eq)]
  | @caseValue Δ t A B r K ht hr =>
    intro env he
    obtain ⟨v, eq, hv⟩ := evalValue ht he
    rw [evalRegion_subst r (Realizes.single eq)]
    cases hv with
    | inl hv =>
      simp only [evalRegion, eq]
      apply evalRegion_subst r
      intro i
      cases i <;> rfl
    | inr hv =>
      simp only [evalRegion, eq]
      apply evalRegion_subst r
      intro i
      cases i <;> rfl
  | caseCfg ht hl hr => exact caseCfg_same ht
  | initial ht hr hs =>
    intro env he
    obtain ⟨v, eq, hv⟩ := evalValue ht he
    cases hv
  | cfgOutward R hr hb =>
    intro env he
    rw [evalRegion, evalRegion_renameLabels]
    exact cfgRun_shiftOut _ _ _

theorem eta_same {Γ L : List (Ty Empty)} {entry block : Region Empty} {A : Ty Empty}
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

theorem cfgEta_same {Γ L : List (Ty Empty)} {r s : Region Empty}
    (h : CfgEta.Eqv Γ r s L) : Same Γ r s := by
  induction h with
  | native h => exact substitutionEquiv_same h
  | symm _ ih => exact ih.symm
  | trans _ _ il ir => exact il.trans ir
  | let₁ ht _ ih => exact ih.let₁ ht
  | let₂ ht _ ih => exact ih.let₂ ht
  | case ht _ _ il ir => exact Same.case ht il ir
  | cfg R he hb ie ib => exact Same.cfg R he.typed.1 (fun i => (hb i).typed.1) ie ib
  | @etaPost Γ entry A L block K σ he hb hσ =>
    intro env henv
    have hs : ValueBranches Γ (CfgEta.singleCfg entry block) L :=
      .cfg (fun _ : Fin 1 => _) he (fun _ => hb)
    have hre : LSubst.ValueFamily Γ (A :: L) L (CfgEta.reentry block) := by
      intro i T hi
      exact .cfg (fun _ : Fin 1 => _) (.br hi (.var (i := 0) rfl))
        (fun _ => hb.renameVars ((Ren.wk _ T).lift _))
    rw [evalRegion_lsubst hs henv, evalRegion_lsubst (he.lsubst hre) henv, eta_same he env henv]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
