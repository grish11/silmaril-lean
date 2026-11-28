module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.CfgEta
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Feedback
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Thms

/-! # Preservation by Paper, unary fusion, and their contextual closure
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift liftN)
open Silmaril.Isotope.LambdaSSA.Semantics (extend extend_rename)
open scoped Paper.BoundSimulation.Obstruction
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
  (UnitPayloadPolicy Env EnvTy Val ValTy Result ResultTy cfgRun one onState
  mergeFeedback one_codiagonal one_eq_of_runs run_simulation mapOut mapOut_congr)

universe u v

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)]

variable {observation : TermObservation (α := α) Φ}

local notation "evalTerm" => evalTermWith observation
local notation "evalRegion" => evalRegionWith observation

local notation "Same" => SameWith observation
local notation "Realizes" => RealizesWith observation

theorem observes_collapse {e p : Region Φ} (env : Env) :
    evalRegion (CfgEta.Codiagonal.nested e p) env =
      evalRegion (CfgEta.Codiagonal.flattened e p) env := by
  dsimp only [CfgEta.Codiagonal.nested, CfgEta.Codiagonal.flattened, CfgEta.singleCfg, evalRegionWith]
  simp only [evalRegion_renameLabels]
  change _ = one (mergeFeedback ∘ fun v => evalRegion p (extend env v)) (evalRegion e env)
  rw [← one_codiagonal]
  congr 1
  funext i v
  change one (fun w => evalRegion (p.renameVars (lift Nat.succ)) (extend (extend env v) w)) (.jump 0 v) =
    one (fun w => evalRegion p (extend env w)) (.jump 0 v)
  congr 1
  funext w
  exact evalRegion_renameVars p (extend_rename (ρ := Nat.succ) (fun _ => rfl) w)


set_option linter.concreteInstances false

variable [UnitPayloadPolicy]

theorem mapOut_localMap {Γ : VCtx (Ty α)} {A D : Ty α} {a : Tm Φ}
    (ha : Tm.BranchValue (A :: Γ) a D) {env : Env} (he : EnvTy Γ env)
    {L : LCtx (Ty α)} {x : Result} (ht : ResultTy (A :: L) x) :
    mapOut (fun i v => evalRegion (CfgEta.Uniformity.localMap a i) (extend env v)) x =
      onState (fun v => (evalTerm a (extend env v)).getD .unit) x := by
  cases x with
  | fault => rfl
  | diverges => rfl
  | jump i v =>
    cases i with
    | succ i => rfl
    | zero =>
      obtain ⟨T, hi, hv⟩ := ht
      cases Option.some.inj hi
      obtain ⟨w, hw, _⟩ := evalValue (observation := observation) ha (he.extend hv)
      simp only [mapOut, CfgEta.Uniformity.localMap, evalRegionWith, hw, onState, Option.getD_some]

theorem observes_uniform {Γ L : List (Ty α)} {A D : Ty α}
    {e p q : Region Φ} {a : Tm Φ}
    (he : ValueBranches Γ e (A :: L)) (hp : ValueBranches (A :: Γ) p (A :: L))
    (ha : Tm.BranchValue (A :: Γ) a D)
    (square : Same (A :: Γ)
      (p.lsubst (liftLSubstVars (CfgEta.Uniformity.localMap a)))
      ((Region.br 0 a).lsubst (liftLSubstVars (fun _ => q)))) :
    Same Γ (CfgEta.singleCfg e p) (CfgEta.singleCfg (e.lsubst (CfgEta.Uniformity.localMap a)) q) := by
  intro env henv
  let f := fun v => (evalTerm a (extend env v)).getD .unit
  let body := fun v => evalRegion p (extend env v)
  let body' := fun v => evalRegion q (extend env v)
  let start := evalRegion e env
  change one body start = one body' (evalRegion (e.lsubst (CfgEta.Uniformity.localMap a)) env)
  rw [evalRegion_lsubst he henv, mapOut_localMap ha henv (evalRegion_typed he.hasType henv)]
  have good {x : Result} (hx : ResultTy (A :: L) x) (v : Val) (eq : x = .jump 0 v) : ValTy v A := by
    rw [eq] at hx
    obtain ⟨T, hi, hv⟩ := hx
    cases Option.some.inj hi
    exact hv
  have stable (v w : Val) (hv : ValTy v A) (eq : body v = .jump 0 w) : ValTy w A :=
    good (evalRegion_typed hp.hasType (henv.extend hv)) w eq
  have comm (v : Val) (hv : ValTy v A) : body' (f v) = onState f (body v) := by
    have h := square _ (henv.extend hv)
    have branch : ValueBranches (A :: Γ) (Region.br 0 a) (D :: L) := .br (ℓ := 0) rfl ha
    have lhs : evalRegion (p.lsubst (liftLSubstVars (CfgEta.Uniformity.localMap a))) (extend env v) =
        onState f (body v) := by
      rw [evalRegion_lsubst hp (henv.extend hv)]
      simp only [eval_liftLSubstVars]
      exact mapOut_localMap ha henv (evalRegion_typed hp.hasType (henv.extend hv))
    rw [lhs, evalRegion_lsubst branch (henv.extend hv)] at h
    obtain ⟨w, hw, _⟩ := evalValue (observation := observation) ha (henv.extend hv)
    simp only [evalRegionWith, hw, mapOut, eval_liftLSubstVars] at h
    simpa only [f, hw, Option.getD_some] using h.symm
  apply one_eq_of_runs
  intro r _
  exact run_simulation stable comm (good (evalRegion_typed he.hasType henv))


theorem paper_same {Γ L : List (Ty α)} {r s : Region Φ}
    (h : Paper.Eqv Γ r s L) : Same Γ r s := by
  induction h with
  | cfgEta h => exact cfgEta_same h
  | productBeta h =>
    cases h with
    | @let₂Beta a _ b _ _ _ ha hb hr =>
      intro env henv
      obtain ⟨v, ev, _⟩ := evalValue (observation := observation) ha henv
      obtain ⟨w, ew, _⟩ := evalValue (observation := observation) hb henv
      have realized : Realizes env (extend (extend env v) w) (Tm.consSubst b (Tm.singleSubst a)) := by
        intro i
        cases i with
        | zero => exact ⟨ew, value_not_computed hb⟩
        | succ i => exact RealizesWith.single ev (value_not_computed ha) i
      simp [evalRegionWith, evalTermWith, ev, ew, value_startsLet ha, value_startsLet hb,
        computes, value_not_computed ha, value_not_computed hb]
      exact (evalRegion_subst _ realized).symm
  | productEta h =>
    cases h with
    | @let₂Eta _ i ℓ A B hi hℓ =>
      intro env henv
      have hv := henv hi
      cases eq : env i with
      | pair a b => simp [evalRegionWith, evalTermWith, startsLet, computes, eq, extend]
      | atom x => exact x.elim
      | unit => rw [eq] at hv; cases hv
      | inl x => rw [eq] at hv; cases hv
      | inr x => rw [eq] at hv; cases hv
  | symm _ ih => exact ih.symm
  | trans _ _ ih ij => exact ih.trans ij
  | let₁ ht _ ih => exact ih.let₁ ht
  | let₂ ht _ ih => exact ih.let₂ ht
  | case ht _ _ il ir => exact SameWith.case ht il ir
  | cfg R he hb ie ib => exact SameWith.cfg R he.typed.1 (fun i => (hb i).typed.1) ie ib
  | lsubstCongr hp h ih =>
    intro env he
    rw [evalRegion_lsubst hp he, evalRegion_lsubst hp he]
    exact mapOut_congr (evalRegion_typed hp.hasType he) (fun i A hi v hv =>
      ih hi _ (he.extend hv))
  | lsubstPost h hr hs hσ ih =>
    intro env he
    rw [evalRegion_lsubst hr he, evalRegion_lsubst hs he, ih env he]
  | @substVars G r s L D θ h hθ ih =>
    intro env he
    let env' := fun i => (evalTerm (θ i) env).getD .unit
    have ht (i : Nat) (A : Ty α) (hi : At G i A) :
        evalTerm (θ i) env = some (env' i) ∧ ValTy (env' i) A := by
      obtain ⟨v, eq, hv⟩ := evalValue (observation := observation) (hθ hi) he
      simpa [env', eq] using hv
    rw [evalRegion_substOn h.typed.1 (fun i A hi => ⟨(ht i A hi).1, value_not_computed (hθ hi)⟩),
        evalRegion_substOn h.typed.2 (fun i A hi => ⟨(ht i A hi).1, value_not_computed (hθ hi)⟩)]
    exact ih env' (fun {i A} hi => (ht i A hi).2)
  | renameLabels h hρ ih =>
    intro env he
    rw [evalRegion_renameLabels, evalRegion_renameLabels, ih env he]
  | @collapsePost Γ e A L p K σ he hp hσ =>
    intro env henv
    have hn : ValueBranches Γ (CfgEta.Codiagonal.nested e p) L :=
      .cfg (fun _ : Fin 1 => A) he (fun _ =>
        .cfg (fun _ : Fin 1 => A) (.br (ℓ := 0) rfl (.var (i := 0) rfl))
          (fun _ => hp.renameVars ((Ren.wk Γ A).lift A)))
    have hb : ValueBranches (A :: Γ) (p.renameLabels Nat.pred) (A :: L) := by
      rw [renameLabels_eq_lsubst]
      exact hp.lsubst (fun i _ hi =>
        .br (ℓ := i.pred) (CfgEta.Codiagonal.mergeLabels A L hi) (.var rfl))
    have hf : ValueBranches Γ (CfgEta.Codiagonal.flattened e p) L :=
      .cfg (fun _ : Fin 1 => A) he (fun _ => hb)
    rw [evalRegion_lsubst hn henv, evalRegion_lsubst hf henv, observes_collapse]
  | uniform he hp hq ha square ih => exact observes_uniform he hp ha ih


open CfgEta.TypeCategory (returnRegion returnRegion_typed) in
/-- Lowering an expression preserves its marked observation. The extra tests
are performed inside expressions, including expressions moved under a let. -/
theorem evalReturnRegion {Γ : VCtx (Ty α)} {t : Tm Φ} {A : Ty α}
    (ht : Tm.HasType Γ t A) {env : Env} (he : EnvTy Γ env) :
    evalRegion (returnRegion t) env =
      match evalTerm t env with
      | none => .fault
      | some v => .jump 0 v := by
  have bound (t : Tm Φ) (env : Env) (shape : startsLet t = false) : evalRegion (.let₁ t (.br 0 (.var 0))) env =
      match evalTerm t env with
      | none => .fault
      | some v => .jump 0 v := by
    simp only [evalRegionWith, shape, Bool.false_and, Bool.false_eq_true, ite_false]
    cases evalTerm t env <;> rfl
  induction ht generalizing env with
  | @let₁ _ a b A D ha hb ia ib =>
    rw [returnRegion, evalRegion_lsubst (returnRegion_typed ha) he, ia he, evalTermWith]
    cases h : evalTerm a env with
    | none => rfl
    | some v =>
      change evalRegion (returnRegion b) (extend env v) = _
      exact ib (he.extend (evalTerm_typed ha he h))
  | _ => exact bound _ _ rfl

theorem unary_fusion_same {Γ L : List (Ty α)} {r s : Region Φ}
    (unmarked : observation.boundUnaryLet = false)
    (h : Paper.UnaryReturn.Step Γ r s L) : Same Γ r s := by
  cases h with
  | @fuse A D a b ha hb =>
    intro env _
    unfold Paper.RetainedLet.returnOnce
    simp only [evalRegionWith, evalTermWith, unmarked, Bool.and_false, Bool.false_eq_true, ite_false]
    cases evalTerm a env <;> rfl

theorem extension_same {Seed : VCtx (Ty α) → Region Φ → Region Φ → LCtx (Ty α) → Prop}
    (seedSame : ∀ {Γ L r s}, Seed Γ r s L → Same Γ r s)
    {Γ L : List (Ty α)} {r s : Region Φ}
    (h : Paper.Extension.Eqv Seed Γ r s L) : Same Γ r s := by
  induction h with
  | paper h => exact paper_same h
  | extra _ _ h => exact seedSame h
  | symm _ ih => exact ih.symm
  | trans _ _ ih ij => exact ih.trans ij
  | let₁ ht _ ih => exact ih.let₁ ht
  | let₂ ht _ ih => exact ih.let₂ ht
  | case ht _ _ il ir => exact SameWith.case ht il ir
  | cfg R he hb ie ib => exact SameWith.cfg R he.typed.1 (fun i => (hb i).typed.1) ie ib
  | lsubstCongr hp h ih =>
    intro env he
    rw [evalRegion_lsubst hp he, evalRegion_lsubst hp he]
    exact mapOut_congr (evalRegion_typed hp.hasType he) (fun i A hi v hv =>
      ih hi _ (he.extend hv))
  | lsubstPost h hr hs hσ ih =>
    intro env he
    rw [evalRegion_lsubst hr he, evalRegion_lsubst hs he, ih env he]
  | @substVars G r s L D θ h hθ ih =>
    intro env he
    let env' := fun i => (evalTerm (θ i) env).getD .unit
    have ht (i : Nat) (A : Ty α) (hi : At G i A) :
        evalTerm (θ i) env = some (env' i) ∧ ValTy (env' i) A := by
      obtain ⟨v, eq, hv⟩ := evalValue (observation := observation) (hθ hi) he
      simpa [env', eq] using hv
    rw [evalRegion_substOn h.typed.1 (fun i A hi => ⟨(ht i A hi).1, value_not_computed (hθ hi)⟩),
        evalRegion_substOn h.typed.2 (fun i A hi => ⟨(ht i A hi).1, value_not_computed (hθ hi)⟩)]
    exact ih env' (fun {i A} hi => (ht i A hi).2)
  | renameLabels h hρ ih =>
    intro env he
    rw [evalRegion_renameLabels, evalRegion_renameLabels, ih env he]

theorem extended_same {Γ L : List (Ty α)} {r s : Region Φ}
    (unmarked : observation.boundUnaryLet = false)
    (h : Paper.Extension.Eqv Paper.UnaryReturn.Step Γ r s L) : Same Γ r s :=
  extension_same (unary_fusion_same unmarked) h

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer
