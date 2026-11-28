module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.BranchNormalization.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Generators.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Uniformity.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Fixture

/-! # A source observation separating raw and bound effectful branches -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta (Step)
open _root_.Silmaril.Isotope.LambdaSSA.Region.CfgEta (singleCfg)

local notation "FixtureTy" => Ty Empty
local notation "U" => (Ty.unit : Ty Empty)

/-- Erase a head primitive only in literal branch position. -/
private def markArg : Tm Op → Tm Op
  | .op _ _ => .unit
  | a => a

private def mark : Region Op → Region Op
  | .br ℓ a => .br ℓ (markArg a)
  | .let₁ a r => .let₁ a (mark r)
  | .let₂ a r => .let₂ a (mark r)
  | .case a l r => .case a (mark l) (mark r)
  | .cfg e n bs => .cfg (mark e) n (fun i => mark (bs i))

variable {Γ Δ : VCtx FixtureTy} {L K : LCtx FixtureTy} {r s : Region Op} {A B : FixtureTy}

private theorem markArg_typed {a : Tm Op} (ha : Tm.HasType Γ a A) : Tm.HasType Γ (markArg a) A := by
  cases ha <;> constructor <;> assumption

private theorem mark_typed (hr : HasType Γ r L) : HasType Γ (mark r) L := by
  induction hr with
  | br hℓ ha => exact .br hℓ (markArg_typed ha)
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case ha il ir
  | cfg R _ _ ie ib => exact .cfg R ie ib

private theorem markArg_value {a : Tm Op} (ha : Tm.BranchValue Γ a A) : markArg a = a := by
  cases ha <;> rfl

private theorem mark_guarded (hr : ValueBranches Γ r L) : mark r = r := by
  induction hr with
  | br _ ha => simp only [mark, markArg_value ha]
  | let₁ _ _ ih => simp only [mark, ih]
  | let₂ _ _ ih => simp only [mark, ih]
  | case _ _ _ il ir => simp only [mark, il, ir]
  | cfg _ _ _ ie ib => simp only [mark, ie, ib]

private theorem mark_renameLabels (r : Region Op) (ρ : Nat → Nat) :
    mark (r.renameLabels ρ) = (mark r).renameLabels ρ := by
  induction r generalizing ρ <;> simp_all only [mark, renameLabels]

private theorem markArg_rename (a : Tm Op) (ρ : Nat → Nat) :
    markArg (a.rename ρ) = (markArg a).rename ρ := by
  cases a <;> rfl

private theorem mark_renameVars (r : Region Op) (ρ : Nat → Nat) :
    mark (r.renameVars ρ) = (mark r).renameVars ρ := by
  induction r generalizing ρ <;> simp_all only [mark, renameVars, markArg_rename]

private theorem markArg_subst {a : Tm Op} (ha : Tm.HasType Γ a A) {θ : Nat → Tm Op}
    (hθ : ∀ ⦃i T⦄, At Γ i T → Tm.BranchValue Δ (θ i) T) :
    markArg (a.subst θ) = (markArg a).subst θ := by
  cases ha with
  | var hi => exact markArg_value (hθ hi)
  | _ => rfl

private theorem liftValues {θ : Nat → Tm Op}
    (hθ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (θ i) A) (B : FixtureTy) :
    ∀ ⦃i A⦄, At (B :: Γ) i A → Tm.BranchValue (B :: Δ) (Tm.liftSubst θ i) A := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .var rfl
  | succ i =>
    change Tm.BranchValue (B :: Δ) ((θ i).rename Nat.succ) A
    rw [Tm.rename_eq_subst]
    exact (hθ hi).subst (fun _ _ h => .var (Ren.wk Δ B h))

private theorem mark_subst (hr : HasType Γ r L) {θ : Nat → Tm Op}
    (hθ : ∀ ⦃i T⦄, At Γ i T → Tm.BranchValue Δ (θ i) T) :
    mark (r.substVars θ) = (mark r).substVars θ := by
  induction hr generalizing Δ θ with
  | br _ ha => simp only [mark, substVars, markArg_subst ha hθ]
  | let₁ _ _ ih => simp only [mark, substVars, ih (liftValues hθ _)]
  | let₂ _ _ ih => simp only [mark, substVars, Tm.liftSubstN, ih (liftValues (liftValues hθ _) _)]
  | case _ _ _ il ir => simp only [mark, substVars, il (liftValues hθ _), ir (liftValues hθ _)]
  | cfg R _ _ ie ib =>
    simp only [mark, substVars, ie hθ, funext (fun i => ib i (liftValues hθ (R i)))]

private theorem mark_liftVars (σ : Nat → Region Op) :
    (fun i => mark (liftLSubstVars σ i)) = liftLSubstVars (fun i => mark (σ i)) :=
  funext fun i => mark_renameVars (σ i) _

private theorem mark_liftLabels (n : Nat) (σ : Nat → Region Op) :
    (fun i => mark (liftLSubstN n σ i)) = liftLSubstN n (fun i => mark (σ i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [liftLSubstN, liftLSubst, mark_renameLabels] using
        congrArg (fun f : Nat → Region Op => (f i).renameLabels Nat.succ) ih

private theorem singleValues {a : Tm Op} (ha : Tm.BranchValue Γ a A) :
    ∀ ⦃i T⦄, At (A :: Γ) i T → Tm.BranchValue Γ (Tm.singleSubst a i) T := by
  intro i T hi
  cases i with
  | zero => cases Option.some.inj hi; exact ha
  | succ i => exact .var hi

private theorem mark_lsubst (hr : ValueBranches Γ r L) {σ : Nat → Region Op}
    (hσ : LSubst.HasType Γ L K σ) :
    mark (r.lsubst σ) = r.lsubst (fun i => mark (σ i)) := by
  induction hr generalizing K σ with
  | br hℓ ha => exact mark_subst (hσ hℓ) (singleValues ha)
  | let₁ ha _ ih =>
    simp only [mark, lsubst, ih (hσ.liftVars _), mark_liftVars]
  | let₂ ha _ ih =>
    simp only [mark, lsubst, ih ((hσ.liftVars _).liftVars _), mark_liftVars]
  | case ha _ _ il ir =>
    simp only [mark, lsubst, il (hσ.liftVars _), ir (hσ.liftVars _), mark_liftVars]
  | cfg R _ _ ie ib =>
    have hlabels := hσ.append (List.ofFn R)
    simp only [List.length_ofFn] at hlabels
    simp only [mark, lsubst, ie hlabels, mark_liftLabels, mark_liftVars,
      funext (fun i => ib i (hlabels.liftVars (R i)))]

private theorem cfg_mark (h : CfgEquiv Γ r s L) : CfgEquiv Γ (mark r) (mark s) L := by
  induction h with
  | refl h => exact .refl (mark_typed h)
  | symm _ ih => exact .symm ih
  | trans _ _ il ir => exact .trans il ir
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case ha il ir
  | cfg R _ _ ie ib => exact .cfg R ie ib
  | cfgZero he _ => exact .cfgZero (mark_typed he) _
  | cfgBrExit R hℓ ha hb =>
    simpa only [mark, markArg_value ha] using
      CfgEquiv.cfgBrExit R hℓ ha (fun i => mark_typed (hb i))
  | cfgBrLocal R i ha hb =>
    simpa only [mark, markArg_value ha] using
      CfgEquiv.cfgBrLocal R i ha (fun j => mark_typed (hb j))

private theorem native_mark (h : RewriteEquiv Γ r s L) : RewriteEquiv Γ (mark r) (mark s) L := by
  induction h with
  | entry h => exact .entry (cfg_mark h)
  | symm _ ih => exact .symm ih
  | trans _ _ il ir => exact .trans il ir
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case ha il ir
  | cfg R _ _ ie ib => exact .cfg R ie ib
  | letBr ha hb hℓ =>
    simpa only [mark, markArg_value hb, markArg_value (ha.singleSubst hb)] using
      RewriteEquiv.letBr ha hb hℓ
  | caseInl ha hl hr => exact .caseInl ha (mark_typed hl) (mark_typed hr)
  | caseInr hb hl hr => exact .caseInr hb (mark_typed hl) (mark_typed hr)

private theorem replaceValues {a : Tm Op} (ha : Tm.BranchValue (B :: Γ) a A) :
    ∀ ⦃i T⦄, At (A :: Γ) i T → Tm.BranchValue (B :: Γ) (Tm.replaceNewest a i) T := by
  intro i T hi
  cases i with
  | zero => cases Option.some.inj hi; exact ha
  | succ i => exact .var hi

private theorem substEqv_mark (h : SubstitutionEquiv Γ r s L) : SubstitutionEquiv Γ (mark r) (mark s) L := by
  induction h with
  | base h => exact .base (native_mark h)
  | symm _ ih => exact .symm ih
  | trans _ _ il ir => exact .trans il ir
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case ha il ir
  | cfg R _ _ ie ib => exact .cfg R ie ib
  | letValue ha hr =>
    rw [mark_subst hr (singleValues ha)]
    exact .letValue ha (mark_typed hr)
  | @caseValue Γ a A B r L ha hr =>
    have hl : Tm.BranchValue (A :: Γ) (.inl (.var 0) : Tm Op) (coprod A B) := .inl (.var rfl)
    have hb : Tm.BranchValue (B :: Γ) (.inr (.var 0) : Tm Op) (coprod A B) := .inr (.var rfl)
    rw [mark_subst hr (singleValues ha)]
    simp only [mark, mark_subst hr (replaceValues hl), mark_subst hr (replaceValues hb)]
    exact .caseValue ha (mark_typed hr)
  | @caseCfg Γ e A B l L r he hl hr =>
    have arms (i : Fin 2) : mark (Fin.cases l (fun _ => r) i) = Fin.cases (mark l) (fun _ => mark r) i := by
      refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
    simpa only [caseCfg, mark, markArg, mark_renameLabels, arms] using
      SubstitutionEquiv.caseCfg he (mark_typed hl) (mark_typed hr)
  | initial ha hr hs => exact .initial ha (mark_typed hr) (mark_typed hs)
  | cfgOutward R hr hb =>
    simpa only [mark, mark_renameLabels] using
      SubstitutionEquiv.cfgOutward R (mark_typed hr) (fun i => mark_typed (hb i))

private theorem singleCfg_values {e p : Region Op} (he : ValueBranches Γ e (A :: L))
    (hp : ValueBranches (A :: Γ) p (A :: L)) : ValueBranches Γ (singleCfg e p) L :=
  .cfg (fun _ : Fin 1 => A) he (fun _ => hp)

private theorem reentry_values {b : Region Op} (hb : ValueBranches (A :: Γ) b (A :: L)) :
    LSubst.ValueFamily Γ (A :: L) L (CfgEta.reentry b) := by
  intro i D hi
  exact .cfg (fun _ : Fin 1 => A) (.br hi (.var (i := 0) rfl))
    (fun _ => hb.renameVars ((Ren.wk Γ D).lift A))

private theorem cfgEta_mark (h : CfgEta.Eqv Γ r s L) : CfgEta.Eqv Γ (mark r) (mark s) L := by
  induction h with
  | native h => exact .native (substEqv_mark h)
  | symm _ ih => exact .symm ih
  | trans _ _ il ir => exact .trans il ir
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case ha il ir
  | cfg R _ _ ie ib => exact .cfg R ie ib
  | etaPost he hb hσ =>
    rw [mark_lsubst (singleCfg_values he hb) hσ,
      mark_lsubst (he.lsubst (reentry_values hb)) hσ]
    exact .etaPost he hb (fun _ _ hi => mark_typed (hσ hi))

private theorem consValues {a b : Tm Op} (ha : Tm.BranchValue Γ a A) (hb : Tm.BranchValue Γ b B) :
    ∀ ⦃i T⦄, At (B :: A :: Γ) i T → Tm.BranchValue Γ (Tm.consSubst b (Tm.singleSubst a) i) T := by
  intro i T hi
  cases i with
  | zero => cases Option.some.inj hi; exact hb
  | succ i => exact singleValues ha hi

private theorem uniform_mark {A D : FixtureTy} {entry p q : Region Op} {a : Tm Op}
    (he : ValueBranches Γ entry (A :: L)) (hp : ValueBranches (A :: Γ) p (A :: L))
    (hq : HasType (D :: Γ) q (D :: L)) (ha : Tm.BranchValue (A :: Γ) a D)
    (square : Paper.Eqv (A :: Γ)
      (mark (p.lsubst (liftLSubstVars (CfgEta.Uniformity.localMap a))))
      (mark ((Region.br 0 a).lsubst (liftLSubstVars (fun _ => q)))) (D :: L)) :
    Paper.Eqv Γ (mark (singleCfg entry p))
      (mark (singleCfg (entry.lsubst (CfgEta.Uniformity.localMap a)) q)) L := by
  have hm : LSubst.HasType Γ (A :: L) (D :: L) (CfgEta.Uniformity.localMap a) :=
    CfgEta.Uniformity.localMap_typed ha.hasType
  have sameMap : (fun i => mark (CfgEta.Uniformity.localMap a i)) = CfgEta.Uniformity.localMap a := by
    funext i
    cases i with
    | zero => simp only [CfgEta.Uniformity.localMap, mark, markArg_value ha]
    | succ i => rfl
  have hbr : ValueBranches (A :: Γ) (.br 0 a) [D] := .br (ℓ := 0) rfl ha
  have hqFamily : LSubst.HasType Γ [D] (D :: L) (fun _ => q) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ hq
  rw [mark_lsubst hp (hm.liftVars A), mark_liftVars, sameMap,
    mark_lsubst hbr (hqFamily.liftVars A), mark_liftVars] at square
  simpa only [singleCfg, mark, mark_guarded he, mark_guarded hp, mark_lsubst he hm, sameMap] using
    Paper.Eqv.uniform he hp (mark_typed hq) ha square

private theorem paper_mark (h : Paper.Eqv Γ r s L) : Paper.Eqv Γ (mark r) (mark s) L := by
  induction h with
  | cfgEta h => exact .cfgEta (cfgEta_mark h)
  | productBeta h =>
    cases h with
    | let₂Beta ha hb hr =>
      rw [mark_subst hr (consValues ha hb)]
      exact .productBeta (.let₂Beta ha hb (mark_typed hr))
  | productEta h =>
    cases h with
    | let₂Eta hi hℓ => exact .productEta (.let₂Eta hi hℓ)
  | symm _ ih => exact .symm ih
  | trans _ _ il ir => exact .trans il ir
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case ha il ir
  | cfg R _ _ ie ib => exact .cfg R ie ib
  | lsubstCongr hp h ih =>
    rw [mark_lsubst hp (fun _ _ hi => (h hi).typed.1), mark_lsubst hp (fun _ _ hi => (h hi).typed.2)]
    exact .lsubstCongr hp ih
  | lsubstPost h hr hs hσ _ =>
    rw [mark_lsubst hr hσ, mark_lsubst hs hσ]
    exact .lsubstPost h hr hs (fun _ _ hi => mark_typed (hσ hi))
  | substVars h hθ ih =>
    rw [mark_subst h.typed.1 hθ, mark_subst h.typed.2 hθ]
    exact .substVars ih hθ
  | renameLabels h hρ ih =>
    simp only [mark_renameLabels]
    exact .renameLabels ih hρ
  | @collapsePost Γ e A L p K σ he hp hσ =>
    have hl : ValueBranches Γ (CfgEta.Codiagonal.nested e p) L :=
      singleCfg_values he (singleCfg_values (.br (ℓ := 0) rfl (.var (i := 0) rfl))
        (hp.renameVars ((Ren.wk Γ A).lift A)))
    have hr : ValueBranches Γ (CfgEta.Codiagonal.flattened e p) L := by
      apply singleCfg_values he
      rw [renameLabels_eq_lsubst]
      exact hp.lsubst (fun i _ hi => .br (ℓ := i.pred) (CfgEta.Codiagonal.mergeLabels A L hi) (.var rfl))
    rw [mark_lsubst hl hσ, mark_lsubst hr hσ]
    exact .collapsePost he hp (fun _ _ hi => mark_typed (hσ hi))
  | uniform he hp hq ha _ ih => exact uniform_mark he hp hq ha ih

variable {Seed : VCtx FixtureTy → Region Op → Region Op → LCtx FixtureTy → Prop}

private theorem extension_mark_map (mapSeed : ∀ {Γ r s L}, Seed Γ r s L → Seed Γ (mark r) (mark s) L)
    (h : Paper.Extension.Eqv Seed Γ r s L) : Paper.Extension.Eqv Seed Γ (mark r) (mark s) L := by
  induction h with
  | paper h => exact .paper (paper_mark h)
  | extra hr hs h => exact .extra (mark_typed hr) (mark_typed hs) (mapSeed h)
  | symm _ ih => exact .symm ih
  | trans _ _ il ir => exact .trans il ir
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case ha il ir
  | cfg R _ _ ie ib => exact .cfg R ie ib
  | lsubstCongr hp h ih =>
    rw [mark_lsubst hp (fun _ _ hi => (h hi).typed.1), mark_lsubst hp (fun _ _ hi => (h hi).typed.2)]
    exact .lsubstCongr hp ih
  | lsubstPost h hr hs hσ _ =>
    rw [mark_lsubst hr hσ, mark_lsubst hs hσ]
    exact .lsubstPost h hr hs (fun _ _ hi => mark_typed (hσ hi))
  | substVars h hθ ih =>
    rw [mark_subst h.typed.1 hθ, mark_subst h.typed.2 hθ]
    exact .substVars ih hθ
  | renameLabels h hρ ih =>
    simp only [mark_renameLabels]
    exact .renameLabels ih hρ

private theorem extension_mark (guarded : ∀ {Γ r s L}, Seed Γ r s L → ValueBranches Γ r L ∧ ValueBranches Γ s L)
    (h : Paper.Extension.Eqv Seed Γ r s L) : Paper.Extension.Eqv Seed Γ (mark r) (mark s) L :=
  extension_mark_map (fun h => by
    obtain ⟨hl, hr⟩ := guarded h
    rw [mark_guarded hl, mark_guarded hr]
    exact h) h

section Observer

open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
  (Env EnvTy Result)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing
  (joined_same)

open scoped Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer.CanonicalUnit
open scoped Paper.BoundSimulation.Obstruction

theorem rawBranch_separation :
    ¬ Paper.Extension.Eqv Step [] rawBranch rawBranch.bindBranchArguments [U] := by
  intro h
  have checked := extension_mark (fun h => h.elim Paper.WithProjectionReturns.Step.valueBranches
    (fun h => by cases h; exact ⟨.br rfl .unit, .br rfl (.var rfl)⟩)) h
  let env : Env := fun _ => .unit
  have envTy : EnvTy ([] : List FixtureTy) env := by intro i A hi; simp [At] at hi
  have eq := joined_same (observation := {}) checked env envTy
  change Result.jump 0 .unit = .fault at eq
  cases eq

open Paper.WithBoundEntryEta.Generators (Candidate weakenRows)

private theorem candidate_mark (h : Candidate Γ r s L) :
    Candidate Γ (mark r) (mark s) L := by
  rcases h with h | h
  · cases h with
    | unary R ha hr hb =>
      simpa only [mark, weakenRows, mark_renameVars] using
        (Or.inl (.unary R ha (mark_typed hr) (fun j => mark_typed (hb j))) :
          Candidate _ _ _ _)
    | binary R ha hr hb =>
      simpa only [mark, weakenRows, mark_renameVars] using
        (Or.inl (.binary R ha (mark_typed hr) (fun j => mark_typed (hb j))) :
          Candidate _ _ _ _)
  · obtain ⟨hl, hr⟩ := h.valueBranches
    rw [mark_guarded hl, mark_guarded hr]
    exact .inr h

open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open Silmaril.DeBruijn (lift)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
  (Val cfgRun_fault)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer
  (TermObservation SameWith evalTermWith evalRegionWith evalRegion_renameVars extension_same)

local notation "obs" => ({} : TermObservation (α := Empty) Op)

private theorem eval_weaken (r : Region Op) (env : Env) (v w : Val) :
    evalRegionWith obs (r.renameVars (lift Nat.succ)) (extend (extend env v) w) =
      evalRegionWith obs r (extend env w) :=
  evalRegion_renameVars r (fun i => by cases i <;> rfl)

private theorem candidate_same (h : Candidate Γ r s L) : SameWith obs Γ r s := by
  intro env _
  rcases h with h | h
  · cases h with
    | @unary n Γ L A a body bs R ha hr hb =>
      simp only [evalRegionWith, Bool.and_false, Bool.false_eq_true, ite_false]
      cases hv : evalTermWith obs a env with
      | none => exact cfgRun_fault n _
      | some v =>
        congr 1
        funext j w
        exact (eval_weaken (bs j) env v w).symm
    | @binary n Γ L A B a body bs R ha hr hb =>
      simp only [evalRegionWith]
      cases hv : evalTermWith obs a env with
      | none => exact cfgRun_fault n _
      | some v =>
        cases v <;> try exact cfgRun_fault n _
        case pair v w =>
          congr 1
          funext j p
          rw [eval_weaken _ (extend env v) w p, eval_weaken _ env v p]
  · cases h with
    | @bind L A B a left right ha hl hr =>
      simp only [Paper.RetainedCase.boundCase, evalRegionWith, Bool.and_false, Bool.false_eq_true, ite_false]
      cases hv : evalTermWith obs a env with
      | none => rfl
      | some v =>
        cases v <;> try rfl
        case inl p => exact (eval_weaken left env (.inl p) p).symm
        case inr p => exact (eval_weaken right env (.inr p) p).symm

/-- Exact unary and binary entry sequencing and guarded discriminator
binding still preserve branch-position erasure. -/
theorem candidate_branch_separation :
    ¬ Paper.Extension.Eqv Candidate [] rawBranch rawBranch.bindBranchArguments [U] := by
  intro h
  let env : Env := fun _ => .unit
  have envTy : EnvTy ([] : List FixtureTy) env := by intro i A hi; simp [At] at hi
  have eq := extension_same (Seed := Candidate) (fun e => candidate_same e)
    (extension_mark_map (Seed := Candidate) (fun e => candidate_mark e) h) env envTy
  change Result.jump 0 .unit = .fault at eq
  cases eq

theorem candidate_zero_arity_ne :
    let bs : Fin 0 → Region Op := Fin.elim0
    ¬ Paper.Extension.Eqv Candidate [] (.cfg rawBranch 0 bs)
      (rawBranch.bindBranchArguments.lsubst (cfgEntryContinuations bs)) [U] := by
  intro bs h
  have left : Paper.Extension.Eqv Candidate [] (.cfg rawBranch 0 bs) rawBranch [U] :=
    .paper (.cfgEta (.native (.base (.entry (.cfgZero rawBranch_typed bs)))))
  have right : Paper.Extension.Eqv Candidate [U]
      (.cfg (.br 0 (.var 0)) 0 (fun j => (bs j).renameVars (lift Nat.succ))) (.br 0 (.var 0)) [U] :=
    .paper (.cfgEta (.native (.base (.entry (.cfgZero (.br (ℓ := 0) rfl (.var rfl)) _)))))
  simp only [rawBranch, lsubst_bindBranchArguments_br] at h
  change Paper.Extension.Eqv Candidate [] (.cfg rawBranch 0 bs)
    (.let₁ (.op .call .unit) (.cfg (.br 0 (.var 0)) 0
      (fun j => (bs j).renameVars (lift Nat.succ)))) [U] at h
  exact candidate_branch_separation (left.symm.trans (h.trans (.let₁ (.op .unit) right)))

open Paper.WithProjectionReturnsAndUnitEta.BranchNormalization
  (toRaw normalize rawClass toRaw_normalize_mk_iff)

theorem reverse_roundTrip_fails :
    toRaw (normalize (rawClass rawBranch_typed)) ≠ rawClass rawBranch_typed :=
  fun h => rawBranch_separation ((toRaw_normalize_mk_iff rawBranch_typed).mp h).symm

open Silmaril.Elgot.ITree
open Silmaril.Isotope.LambdaSSA.Semantics.Interaction (Primitive region term)

/-- The ordinary weak-tree evaluator makes the same single visible request on both forms. -/
theorem one_request :
    region visiblePrim (fun _ => .unit) rawBranch =
        vis .request (fun _ => pure (0, .unit)) ∧
      region visiblePrim (fun _ => .unit) rawBranch.bindBranchArguments =
        vis .request (fun _ => pure (0, .unit)) := by
  constructor
  · simp only [region, term, visiblePrim, pure_bind, vis_bind]
  · simp only [bindBranchArguments, region, term, visiblePrim,
      Silmaril.Isotope.LambdaSSA.Semantics.extend, pure_bind, vis_bind]

end Observer
end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch
