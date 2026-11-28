module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Fixture
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Values.Discard.Coproducts.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Retained.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedCase.Distributor.Thms

/-! # Term-case observation of guarded value copairs -/

public section

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open scoped Paper.BoundSimulation.Obstruction
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer
  (Env EnvTy Result Val mapOut)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing
  (joined_same)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer
open scoped Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer.CanonicalUnit
open CfgEta.TypeCategory (returnRegion returnRegion_typed caseValueBranches)

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Copair

local notation "U" => (Ty.unit : Ty Empty)
local notation "Bit" => (Ty.coprod U U)
local notation "Seed" => Paper.WithProjectionReturnsAndUnitEta.Step (τ := Ty Empty) (Φ := Empty)
private abbrev caseObservation : TermObservation (α := Empty) Empty := { caseTerm := true }
local notation "observeTerm" => evalTermWith caseObservation
local notation "observeRegion" => evalRegionWith caseObservation

universe w
variable {ε : Type w} [HasEff Empty ε] (pe : ε)

private def leftEnv : Env := extend (fun _ => .unit) (.inl .unit)
private def rightEnv : Env := extend (fun _ => .unit) (.inr .unit)

private theorem leftEnv_typed : EnvTy [Bit] leftEnv := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .inl .unit
  | succ i => simp [At] at hi

private theorem rightEnv_typed : EnvTy [Bit] rightEnv := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .inr .unit
  | succ i => simp [At] at hi

theorem joined_caseReturnAgreement_fails :
    ¬ Paper.Extension.Singleton.ValueCoproducts.CaseReturnAgreement Seed pe := by
  intro h
  have e := h (A := U) (B := U) (D := U) (.unit : Tm.HasType [U] (.unit : Tm Empty) U)
    (.unit : Tm.HasType [U] (.unit : Tm Empty) U) .unit .unit
  have he := joined_same (observation := { caseTerm := true }) e leftEnv leftEnv_typed
  change Result.fault = Result.jump 0 .unit at he
  cases he

/-- The same constructors may wrap both values. At the varying input, the
relation has the direction from left unit to right unit. -/
private inductive Related : Val → Val → Prop where
  | unit : Related .unit .unit
  | input : Related (.inl .unit) (.inr .unit)
  | pair {a b c d : Val} : Related a c → Related b d → Related (.pair a b) (.pair c d)
  | inl {a b : Val} : Related a b → Related (.inl a) (.inl b)
  | inr {a b : Val} : Related a b → Related (.inr a) (.inr b)

private inductive Outcome : Option Val → Option Val → Prop where
  | none : Outcome none none
  | some {a b : Val} : Related a b → Outcome (some a) (some b)

private theorem Outcome.bind {x y : Option Val} (h : Outcome x y) (f g : Val → Option Val)
    (hg : ∀ {v w}, Related v w → Outcome (f v) (g w)) :
    Outcome (x.bind f) (y.bind g) := by
  cases h with
  | none => exact .none
  | some h => exact hg h

private theorem Outcome.map {x y : Option Val} (h : Outcome x y) (f : Val → Val)
    (hf : ∀ {v w}, Related v w → Related (f v) (f w)) :
    Outcome (x.map f) (y.map f) := by
  cases h with
  | none => exact .none
  | some h => exact .some (hf h)

private theorem extend_related {a b : Env} {u v : Val}
    (h : ∀ i, Related (a i) (b i)) (h' : Related u v) :
    ∀ i, Related (extend a u i) (extend b v i)
  | 0 => h'
  | i + 1 => h i

private theorem evalTerm_related (t : Tm Empty) {a b : Env}
    (h : ∀ i, Related (a i) (b i)) : Outcome (observeTerm t a) (observeTerm t b) := by
  induction t generalizing a b with
  | var i => exact .some (h i)
  | op f _ _ => exact f.elim
  | unit => exact .some .unit
  | pair _ _ il ir =>
    exact (il h).bind _ _ (fun l => (ir h).bind _ _ (fun r => .some (.pair l r)))
  | let₁ _ _ il ir =>
    simp only [evalTermWith]
    exact (il h).bind _ _ (fun h' => ir (extend_related h h'))
  | let₂ _ _ il ir =>
    simp only [evalTermWith]
    refine (il h).bind _ _ (fun h' => ?_)
    cases h' with
    | pair hx hy => exact ir (extend_related (extend_related h hx) hy)
    | _ => exact .none
  | inl _ ih =>
    simpa only [evalTermWith, Bool.and_false, Bool.false_eq_true, ite_false] using (ih h).map _ .inl
  | inr _ ih =>
    simpa only [evalTermWith, Bool.and_false, Bool.false_eq_true, ite_false] using (ih h).map _ .inr
  | case _ _ _ _ _ _ => exact .none
  | abort _ _ => exact .none

private theorem leftRightRelated : ∀ i, Related (leftEnv i) (rightEnv i)
  | 0 => .input
  | _ + 1 => .unit

private theorem some_of_jump {x : Option Val} {v : Val}
    (h : (match x with | none => Result.fault | some w => Result.jump 0 w) = Result.jump 0 v) :
    x = some v := by
  cases x <;> cases h
  rfl

private theorem return_results_related {A B : Ty Empty} {t : Tm Empty} (ht : Tm.HasType [A] t B)
    {env env' : Env} (he : EnvTy [A] env) (he' : EnvTy [A] env')
    (rel : ∀ i, Related (env i) (env' i)) {v w : Val}
    (hl : observeRegion (returnRegion t) env = .jump 0 v)
    (hr : observeRegion (returnRegion t) env' = .jump 0 w) : Related v w := by
  have h := evalTerm_related t rel
  rw [evalReturnRegion (observation := caseObservation) ht he] at hl
  rw [evalReturnRegion (observation := caseObservation) ht he'] at hr
  rw [some_of_jump hl, some_of_jump hr] at h
  cases h with
  | some hv => exact hv

open Paper.Extension.Singleton (ProjectedPureReturn DiscardPreservingReturn)
open Paper.Extension.Singleton.ValueCoproducts (CopairPure exactCopair)
open Paper.RetainedCase (case_ofRegion_inl case_ofRegion_inr)
open CfgEta.TypeCategory.Retained (distributorRegion_typed)

local notation "P" => Paper.WithProjectionReturnsAndUnitEta.projection (τ := Ty Empty) (Φ := Empty)
local notation "Obj" => Paper.Extension.Singleton.ofType Seed
local notation "Lit" => Paper.Extension.Singleton.ofRegion Seed

set_option backward.isDefEq.respectTransparency false in
private theorem noProjectedReturn {A B : Ty Empty} {r : Region Empty}
    (ht : ValueBranches [A] r [B]) {env env' : Env}
    (he : EnvTy [A] env) (he' : EnvTy [A] env') (rel : ∀ i, Related (env i) (env' i))
    {v w : Val} (hl : observeRegion r env = .jump 0 v) (hr : observeRegion r env' = .jump 0 w)
    (separated : ¬ Related v w) : ¬ ProjectedPureReturn Seed pe (Lit ht) := by
  rintro ⟨f, ⟨t, h, _, rfl⟩, e⟩
  have eq := (Paper.Extension.Singleton.ofRegion_eq_iff Seed (returnRegion_typed h) ht).1 e
  exact separated (return_results_related h he he' rel
    ((joined_same (observation := caseObservation) eq env he).trans hl)
    ((joined_same (observation := caseObservation) eq env' he').trans hr))

private theorem swapLeft_typed : ValueBranches [U] (.br 0 (.inr (.var 0)) : Region Empty) [Bit] :=
  .br rfl (.inr (.var rfl))

private theorem swapRight_typed : ValueBranches [U] (.br 0 (.inl (.var 0)) : Region Empty) [Bit] :=
  .br rfl (.inl (.var rfl))

private theorem swap_typed :
    ValueBranches [Bit] (.case (.var 0) (.br 0 (.inr (.var 0))) (.br 0 (.inl (.var 0))) : Region Empty) [Bit] :=
  caseValueBranches swapLeft_typed swapRight_typed

private theorem branch_mem {A D : Ty Empty} {a : Tm Empty} (ha : Tm.BranchValue [A] a D) :
    DiscardPreservingReturn Seed pe (Lit (.br (ℓ := 0) rfl ha)) :=
  ⟨Paper.Extension.Singleton.projected_branchValue_mem Seed pe ha,
    (Functor.map_comp P _ _).symm.trans (congrArg (P).map (Paper.TypeCategory.discard_comp_branchValue ha))⟩

set_option backward.isDefEq.respectTransparency false in
private theorem exactCopair_swap :
    exactCopair Seed (Lit swapLeft_typed) (Lit swapRight_typed) = Lit swap_typed := by
  apply BinaryCofan.IsColimit.hom_ext (Paper.Extension.Singleton.sumCofanIsColimit Seed U U)
  · have hl := (Paper.Extension.Singleton.sumCofanIsColimit Seed U U).fac
      (BinaryCofan.mk (Lit swapLeft_typed) (Lit swapRight_typed)) ⟨WalkingPair.left⟩
    refine hl.trans ?_
    change _ = (P).map (Paper.TypeCategory.sumCofan U U).inl ≫ (P).map (Paper.TypeCategory.ofRegion (τ := Ty Empty) swap_typed)
    rw [← Functor.map_comp]
    exact congrArg (P).map (case_ofRegion_inl swapLeft_typed swapRight_typed).symm
  · have hr := (Paper.Extension.Singleton.sumCofanIsColimit Seed U U).fac
      (BinaryCofan.mk (Lit swapLeft_typed) (Lit swapRight_typed)) ⟨WalkingPair.right⟩
    refine hr.trans ?_
    change _ = (P).map (Paper.TypeCategory.sumCofan U U).inr ≫ (P).map (Paper.TypeCategory.ofRegion (τ := Ty Empty) swap_typed)
    rw [← Functor.map_comp]
    exact congrArg (P).map (case_ofRegion_inr swapLeft_typed swapRight_typed).symm

theorem joined_copairPure_fails : ¬ CopairPure Seed pe := by
  intro cp
  have h := cp (A := U) (B := U) (D := Obj Bit)
    (branch_mem pe (A := U) (D := Bit) (.inr (.var (i := 0) rfl)))
    (branch_mem pe (A := U) (D := Bit) (.inl (.var (i := 0) rfl)))
  rw [exactCopair_swap] at h
  exact noProjectedReturn pe swap_typed leftEnv_typed rightEnv_typed leftRightRelated
    (v := .inr .unit) (w := .inl .unit) rfl rfl (by intro e; cases e) h

private def leftProductEnv : Env := extend (fun _ => .unit) (.pair .unit (.inl .unit))
private def rightProductEnv : Env := extend (fun _ => .unit) (.pair .unit (.inr .unit))

private theorem leftProductEnv_typed : EnvTy [Ty.product U Bit] leftProductEnv := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .pair .unit (.inl .unit)
  | succ i => simp [At] at hi

private theorem rightProductEnv_typed : EnvTy [Ty.product U Bit] rightProductEnv := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .pair .unit (.inr .unit)
  | succ i => simp [At] at hi

private theorem productEnvsRelated : ∀ i, Related (leftProductEnv i) (rightProductEnv i)
  | 0 => .pair .unit .input
  | _ + 1 => .unit

theorem joined_guardedDistributor_not_projectedPureReturn :
    ¬ ProjectedPureReturn Seed pe (Lit (distributorRegion_typed U U U)) :=
  noProjectedReturn pe (distributorRegion_typed U U U) leftProductEnv_typed rightProductEnv_typed
    productEnvsRelated (v := .inl (.pair .unit .unit)) (w := .inr (.pair .unit .unit))
    rfl rfl (by intro e; cases e)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Copair
