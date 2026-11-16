module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Operational.Defs
public import Silmaril.Logic.TypeTheory.CIC.Reduction.Contexts.Thms
public import Silmaril.Logic.TypeTheory.CIC.Semantics.ConstructorValues.Tags.Thms
public import Silmaril.Logic.TypeTheory.CIC.Semantics.Constructors.Thms
import Mathlib.Tactic

public section

namespace Silmaril.Proofs.Logic.TypeTheory.CIC.OperationalEvaluationLaws

open Silmaril.Logic.TypeTheory.CIC
open Silmaril.Logic.TypeTheory.CIC.SetSemantics

universe u

/-- Inversion exposes the exact missing syntax rule in the original kernel. -/
theorem evaluates_fix_impossible {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {definitions : List (FixDef Expr)} {index : ℕ} {value : Value.{u}} :
    ¬ Evaluates ρ universes globals values (.fix definitions index) value := by
  intro h
  cases h

theorem evaluates_fix_application_impossible {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {definitions : List (FixDef Expr)} {index : ℕ} {argument : Expr} {value : Value.{u}} :
    ¬ Evaluates ρ universes globals values (.app (.fix definitions index) argument) value := by
  intro h
  cases h with
  | application hf _ => exact evaluates_fix_impossible hf

/-- The unary operational rule is backed by the actual constructor-restricted source fix and beta steps. -/
theorem fixBeta_steps (env : GlobalEnv) (Γ : Context) {definitions : List (FixDef Expr)} {index : ℕ}
    {na : Binder} {domain body argument : Expr}
    (hunfold : unfoldFix definitions index = some (0, .lam na domain body)) (hconstructor : argument.IsConstructorApplication) :
    Steps env Γ (.app (.fix definitions index) argument) (body.subst [argument] 0) :=
  (Relation.ReflTransGen.single (Step.fixUnfold (args := [argument]) hunfold rfl hconstructor)).trans
    (Relation.ReflTransGen.single Step.beta)

private theorem extendedSubst_evaluates {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {Γ : Context} (hnone : ∀ d ∈ Γ, d.value = none) (pre fields suffix : LocalValues.{u}) (hlen : fields.length = Γ.length) :
    List.Forall₂ (Evaluates ρ universes globals (pre ++ fields ++ suffix)) (Γ.extendedSubst pre.length) fields :=
  evaluates_extendedSubst hnone pre fields suffix hlen

/-- Without definitions, actual context expansion preserves a kernel body value in its genuine field context. -/
theorem evaluates_expandLets_noDefinitions {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {Γ : Context} {fields values : LocalValues.{u}} {body : Expr} {value : Value.{u}}
    (hnone : ∀ d ∈ Γ, d.value = none) (hlen : fields.length = Γ.length)
    (hbody : Evaluates ρ universes globals (fields ++ values) body value) :
    Evaluates ρ universes globals (fields ++ values) (Γ.expandLets body) value := by
  have hlift : Evaluates ρ universes globals (fields ++ fields ++ values) (body.lift fields.length fields.length) value := by
    simpa only [List.append_assoc] using evaluates_lift fields hbody fields values rfl
  have hreplacements : List.Forall₂ (Evaluates ρ universes globals (fields ++ values)) (Γ.extendedSubst 0) fields := by
    simpa only [List.nil_append, List.length_nil] using extendedSubst_evaluates hnone [] fields values hlen
  have hsubst := evaluates_subst hlift (Γ.extendedSubst 0) fields [] (fields ++ values) (by simp only [List.nil_append, List.append_assoc]) hreplacements
  simpa only [Context.expandLets, Context.assumptionCount_eq_length hnone, ← hlen, List.nil_append, List.length_nil] using hsubst

/-- Kernel case evaluation reaches the actual source iota reduct with the same value. -/
theorem evaluates_iota_reduct {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {ci : CaseInfo} {p : Predicate Expr LevelName} {scrutinee : Expr}
    {branches : List (Branch Expr)} {index : ℕ} {arguments : List Expr} {argumentValues : LocalValues.{u}}
    {branch : Branch Expr} {value : Value.{u}}
    (hlookup : branches[index]? = some branch) (hnone : ∀ d ∈ branch.context, d.value = none)
    (hargs : List.Forall₂ (Evaluates ρ universes globals values) arguments argumentValues)
    (hs : Evaluates ρ universes globals values scrutinee (constructorValue index argumentValues))
    (hcase : Evaluates ρ universes globals values (.caseOf ci p scrutinee branches) value) :
    Evaluates ρ universes globals values (iotaReduce ci.parameterCount p arguments branch) value := by
  cases hcase with
  | caseOf hs' hlookup' hnone' hlength hbody =>
      have htags := constructorValue_inj.mp (evaluates_deterministic hs hs')
      cases htags.1
      cases htags.2
      have hb := Option.some.inj (hlookup.symm.trans hlookup')
      cases hb
      have hfields : (argumentValues.drop ci.parameterCount).reverse.length = (Context.instantiateCase p branch.context).length := by
        simp only [List.length_reverse, List.length_drop, Context.instantiateCase, Context.subst_length, Context.instantiate_length]
        omega
      have hexpand := evaluates_expandLets_noDefinitions (Context.instantiateCase_noDefinitions hnone p) hfields hbody
      have hreplacements := List.forall₂_reverse_iff.mpr (List.forall₂_drop ci.parameterCount hargs)
      simpa only [iotaReduce, List.nil_append, List.length_nil] using
        evaluates_subst hexpand (arguments.drop ci.parameterCount).reverse
          (argumentValues.drop ci.parameterCount).reverse [] values rfl hreplacements

/-- The staged relation still assigns no value to a bare fixpoint. -/
theorem operationalEvaluates_fix_impossible {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {definitions : List (FixDef Expr)} {index : ℕ} {value : Value.{u}} :
    ¬ OperationalEvaluates ρ universes globals values (.fix definitions index) value := by
  intro h
  cases h with
  | kernel h => exact evaluates_fix_impossible h

/-- Every existing kernel evaluation agrees with all staged evaluations of the same source term. -/
theorem operationalEvaluates_kernel_compatible {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {term : Expr} {value other : Value.{u}}
    (h : OperationalEvaluates ρ universes globals values term value)
    (hold : Evaluates ρ universes globals values term other) : value = other := by
  induction h generalizing other with
  | kernel h => exact evaluates_deterministic h hold
  | application hf ha ihf iha =>
      cases hold with
      | application hf' ha' => exact congrArg₂ traceApply (ihf hf') (iha ha')
  | fixBeta _ _ _ _ => exact False.elim (evaluates_fix_application_impossible hold)
  | iota _ hlookup hnone _ hargs hs _ ih =>
      exact ih (evaluates_iota_reduct hlookup hnone hargs hs hold)

private def applicationArguments : Expr → List Expr
  | .app f a => applicationArguments f ++ [a]
  | _ => []

private theorem head_mkApps (t : Expr) (args : List Expr) : Expr.head (Expr.mkApps t args) = Expr.head t := by
  induction args generalizing t with
  | nil => rfl
  | cons a args ih => simpa only [Expr.mkApps, List.foldl_cons, Expr.head] using ih (.app t a)

private theorem arguments_mkApps (t : Expr) (args : List Expr) :
    applicationArguments (Expr.mkApps t args) = applicationArguments t ++ args := by
  induction args generalizing t with
  | nil => simp only [Expr.mkApps, List.foldl_nil, List.append_nil]
  | cons a args ih =>
      simpa only [Expr.mkApps, List.foldl_cons, applicationArguments, List.append_assoc, List.singleton_append] using ih (.app t a)

theorem constructor_spine_injective {reference reference' : InductiveRef} {index index' : ℕ}
    {ui ui' : List Universe} {args args' : List Expr}
    (h : Expr.mkApps (.constructor reference index ui) args = Expr.mkApps (.constructor reference' index' ui') args') :
    reference = reference' ∧ index = index' ∧ ui = ui' ∧ args = args' := by
  have hh : Term.constructor reference index ui = Term.constructor reference' index' ui' := by
    simpa only [head_mkApps, Expr.head] using congrArg Expr.head h
  have ha : args = args' := by
    simpa only [arguments_mkApps, applicationArguments, List.nil_append] using congrArg applicationArguments h
  obtain ⟨hr, hi, hu⟩ := Term.constructor.inj hh
  exact ⟨hr, hi, hu, ha⟩

private theorem unfolded_body_eq {definitions : List (FixDef Expr)} {index : ℕ}
    {na na' : Binder} {domain domain' body body' : Expr}
    (h : unfoldFix definitions index = some (0, .lam na domain body))
    (h' : unfoldFix definitions index = some (0, .lam na' domain' body')) : body = body' :=
  (Term.lam.inj (Prod.mk.inj (Option.some.inj (h.symm.trans h'))).2).2.2

theorem iota_reduct_eq {ci : CaseInfo} {p : Predicate Expr LevelName} {scrutinee : Expr}
    {branches : List (Branch Expr)} {index index' : ℕ} {ui ui' : List Universe}
    {arguments arguments' : List Expr} {branch branch' : Branch Expr}
    (hs : scrutinee = Expr.mkApps (.constructor ci.inductiveRef index ui) arguments)
    (hs' : scrutinee = Expr.mkApps (.constructor ci.inductiveRef index' ui') arguments')
    (hb : branches[index]? = some branch) (hb' : branches[index']? = some branch') :
    iotaReduce ci.parameterCount p arguments branch = iotaReduce ci.parameterCount p arguments' branch' := by
  obtain ⟨_, rfl, rfl, rfl⟩ := constructor_spine_injective (hs.symm.trans hs')
  exact congrArg (iotaReduce ci.parameterCount p arguments) (Option.some.inj (hb.symm.trans hb'))

/-- The general staged operational fragment is deterministic and preserves all old kernel values. -/
theorem operationalEvaluates_deterministic {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {term : Expr} {value other : Value.{u}}
    (h : OperationalEvaluates ρ universes globals values term value)
    (hother : OperationalEvaluates ρ universes globals values term other) : value = other := by
  induction h generalizing other with
  | kernel h => exact (operationalEvaluates_kernel_compatible hother h).symm
  | application hf ha ihf iha =>
      cases hother with
      | kernel h => exact operationalEvaluates_kernel_compatible (.application hf ha) h
      | application hf' ha' => exact congrArg₂ traceApply (ihf hf') (iha ha')
      | fixBeta _ _ _ => exact False.elim (operationalEvaluates_fix_impossible hf)
  | fixBeta hunfold hconstructor hbody ih =>
      cases hother with
      | kernel h => exact False.elim (evaluates_fix_application_impossible h)
      | application hf ha => exact False.elim (operationalEvaluates_fix_impossible hf)
      | fixBeta hunfold' hconstructor' hbody' =>
          exact ih ((unfolded_body_eq hunfold hunfold').symm ▸ hbody')
  | iota hspine hlookup hnone hlength hargs hs hbody ih =>
      cases hother with
      | kernel h => exact operationalEvaluates_kernel_compatible (.iota hspine hlookup hnone hlength hargs hs hbody) h
      | iota hspine' hlookup' hnone' hlength' hargs' hs' hbody' =>
          exact ih ((iota_reduct_eq hspine hspine' hlookup hlookup').symm ▸ hbody')

/-- The tagged operational rule is an actual source iota step, with its real context expansion. -/
theorem operational_iota_step (env : GlobalEnv) (Γ : Context)
    {ci : CaseInfo} {p : Predicate Expr LevelName} {scrutinee : Expr} {branches : List (Branch Expr)}
    {index : ℕ} {ui : List Universe} {arguments : List Expr} {branch : Branch Expr}
    (hspine : scrutinee = Expr.mkApps (.constructor ci.inductiveRef index ui) arguments)
    (hlookup : branches[index]? = some branch) (hnone : ∀ d ∈ branch.context, d.value = none)
    (hlength : arguments.length = ci.parameterCount + branch.context.length) :
    Step env Γ (.caseOf ci p scrutinee branches) (iotaReduce ci.parameterCount p arguments branch) := by
  rw [hspine]
  exact Step.iota hlookup (by simpa only [Context.assumptionCount_eq_length hnone] using hlength)

/-- Every staged evaluation derives an actual finite source reduction to a same-valued old-kernel expression. -/
theorem operationalEvaluates_source_bridge {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {term : Expr} {value : Value.{u}}
    (h : OperationalEvaluates ρ universes globals values term value) (env : GlobalEnv) (Γ : Context) :
    ∃ result, Steps env Γ term result ∧ Evaluates ρ universes globals values result value := by
  induction h with
  | kernel h => exact ⟨_, .refl, h⟩
  | @application function argument fv av hf ha ihf iha =>
      obtain ⟨f, hfs, hfv⟩ := ihf
      obtain ⟨a, has, hav⟩ := iha
      have hfunction : Steps env Γ (.app function argument) (.app f argument) := Relation.ReflTransGen.lift (r := Step env Γ) (p := Step env Γ)
        (fun term : Expr => Term.app term argument) (fun _ _ h => Step.appFunction h) _ _ hfs
      have hargument : Steps env Γ (.app f argument) (.app f a) := Relation.ReflTransGen.lift (r := Step env Γ) (p := Step env Γ)
        (fun a => Term.app f a) (fun _ _ h => Step.appArgument h) _ _ has
      exact ⟨.app f a, hfunction.trans hargument, Evaluates.application hfv hav⟩
  | fixBeta hunfold hconstructor hbody ih =>
      obtain ⟨result, hsteps, hvalue⟩ := ih
      exact ⟨result, (fixBeta_steps env Γ hunfold hconstructor).trans hsteps, hvalue⟩
  | iota hspine hlookup hnone hlength hargs hs hbody ih =>
      obtain ⟨result, hsteps, hvalue⟩ := ih
      exact ⟨result, (Relation.ReflTransGen.single (operational_iota_step env Γ hspine hlookup hnone hlength)).trans hsteps, hvalue⟩

end Silmaril.Proofs.Logic.TypeTheory.CIC.OperationalEvaluationLaws
