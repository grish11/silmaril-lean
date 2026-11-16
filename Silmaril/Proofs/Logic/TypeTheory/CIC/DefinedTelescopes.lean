module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Constructors.Definitions.Defs
import Mathlib.Tactic

public section

namespace Silmaril.Proofs.Logic.TypeTheory.CIC.DefinedTelescopeLaws

open Silmaril.Logic.TypeTheory.CIC
open Silmaril.Logic.TypeTheory.CIC.SetSemantics

universe u

private theorem substTelescope_cons (terms : List Expr) (cutoff : ℕ)
    (declaration : ContextDecl Expr) (declarations : Context) :
    Context.substTelescope terms cutoff (declaration :: declarations) =
      declaration.mapTerms (Term.subst terms cutoff) ::
        Context.substTelescope terms (cutoff + 1) declarations := by
  simp only [Context.substTelescope, List.mapIdx_cons, Nat.add_zero]
  apply congrArg (List.cons _)
  apply congrArg (fun f : ℕ → ContextDecl Expr → ContextDecl Expr => List.mapIdx f declarations)
  funext i d
  have hindex : cutoff + (i + 1) = cutoff + 1 + i := by omega
  rw [hindex]

private theorem subst_reverse (terms : List Expr) (cutoff : ℕ) (declarations : Context) :
    (Context.subst terms cutoff declarations).reverse =
      Context.substTelescope terms cutoff declarations.reverse := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < declarations.length
  · rw [List.getElem?_reverse (by simpa [Context.subst, Context.mapAt] using hi)]
    simp only [Context.subst, Context.mapAt, Context.substTelescope, List.getElem?_mapIdx,
      List.length_mapIdx]
    rw [List.getElem?_reverse hi]
    have hindex : declarations.length - 1 - (declarations.length - 1 - i) + cutoff = cutoff + i := by omega
    simp only [hindex]
  · have hleft : ¬ i < (Context.subst terms cutoff declarations).reverse.length := by
      simpa only [Context.subst, Context.mapAt, List.length_reverse, List.length_mapIdx] using hi
    have hright : ¬ i < (Context.substTelescope terms cutoff declarations.reverse).length := by
      simpa only [Context.substTelescope, List.length_mapIdx, List.length_reverse] using hi
    simp only [List.getElem?_eq_none (Nat.le_of_not_gt hleft),
      List.getElem?_eq_none (Nat.le_of_not_gt hright)]

private theorem smash_append (acc Γ Δ : Context) :
    Context.smash acc (Γ ++ Δ) = Context.smash (Context.smash acc Γ) Δ := by
  induction Γ generalizing acc with
  | nil => rfl
  | cons d Γ ih => cases hd : d.value <;> simp only [List.cons_append, Context.smash, hd, ih]

/-- Actual substitution transports every domain of a dependent source telescope. -/
theorem interpretsTelescope_subst {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} {values : LocalValues.{u}} {declarations : Context} {T : ValueTelescope.{u}}
    (h : InterpretsTelescope ρ universes globals values declarations T)
    (terms : List Expr) (replacementValues pre suffix : LocalValues.{u})
    (hvalues : values = pre ++ replacementValues ++ suffix)
    (hterms : List.Forall₂ (Evaluates ρ universes globals suffix) terms replacementValues) :
    InterpretsTelescope ρ universes globals (pre ++ suffix)
      (Context.substTelescope terms pre.length declarations) T := by
  induction h generalizing pre with
  | nil => exact .nil
  | @assumption values na type declarations A rest htype hrest ih =>
      rw [substTelescope_cons]
      apply InterpretsTelescope.assumption
      · exact evaluates_subst htype terms replacementValues pre suffix hvalues hterms
      · intro x
        simpa only [List.length_cons, List.cons_append] using
          ih x (x.val :: pre) (by simp only [hvalues, List.cons_append])

/-- The actual source definitions are eliminated by the exact cache smash operation. -/
theorem SourceTelescopeData.interpretsSmash {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} {values : LocalValues.{u}} {declarations : Context}
    (data : SourceTelescopeData ρ universes globals values declarations) :
    InterpretsTelescope ρ universes globals values
      (Context.smash [] declarations.reverse).reverse data.telescope := by
  induction data with
  | nil => exact .nil
  | @assumption values na type declarations A htype rest ih =>
      simpa only [List.reverse_cons, smash_append, Context.smash, List.nil_append,
        List.reverse_append, List.reverse_singleton, List.reverse_nil, List.nil_append,
        List.singleton_append, SourceTelescopeData.telescope] using
        InterpretsTelescope.assumption htype ih
  | @definition values na value type declarations A a htype hvalue hmember rest ih =>
      have hsubst := interpretsTelescope_subst ih [value] [a] [] values rfl (.cons hvalue .nil)
      simpa only [List.reverse_cons, smash_append, Context.smash, List.nil_append,
        subst_reverse, List.length_nil, SourceTelescopeData.telescope] using hsubst

/-- Runtime tuples count assumptions, including when arbitrary source definitions occur. -/
theorem SourceTelescopeData.arguments_length {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} {values : LocalValues.{u}} {declarations : Context}
    (data : SourceTelescopeData ρ universes globals values declarations) (xs : data.telescope.Points) :
    (data.telescope.arguments xs).length = declarations.assumptionCount := by
  induction data with
  | nil => rfl
  | assumption A htype rest ih =>
      rcases xs with ⟨x, xs⟩
      simpa only [SourceTelescopeData.telescope, ValueTelescope.arguments, List.length_cons,
        Context.assumptionCount, Option.isNone_none, Bool.true_eq, ite_true,
        Nat.succ_eq_add_one, Nat.add_comm] using congrArg Nat.succ (ih x xs)
  | definition A a htype hvalue hmember rest ih =>
      simpa only [SourceTelescopeData.telescope, Context.assumptionCount, Option.isNone_some,
        Bool.false_eq_true, ite_false, Nat.zero_add] using ih xs

/-- Every source binder, including a definition, has its actual semantic local value. -/
theorem SourceTelescopeData.sourceValues_length {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} {values : LocalValues.{u}} {declarations : Context}
    (data : SourceTelescopeData ρ universes globals values declarations) (xs : data.telescope.Points) :
    (data.sourceValues xs).length = declarations.length := by
  induction data with
  | nil => rfl
  | assumption A htype rest ih => exact congrArg Nat.succ (ih xs.1 xs.2)
  | definition A a htype hvalue hmember rest ih => exact congrArg Nat.succ (ih xs)

/-- Computed tuples realize the original source context, with definitions retained. -/
theorem SourceTelescopeData.interpretsLocal {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} {values : LocalValues.{u}} {declarations Γ : Context}
    (data : SourceTelescopeData ρ universes globals values declarations)
    (hΓ : InterpretsLocal ρ universes globals Γ values) (xs : data.telescope.Points) :
    InterpretsLocal ρ universes globals (declarations.reverse ++ Γ) ((data.sourceValues xs).reverse ++ values) := by
  induction data generalizing Γ with
  | nil => exact hΓ
  | @assumption values na type declarations A htype rest ih =>
      have hx := InterpretsLocal.assumption (na := na) hΓ htype xs.1.property
      simpa only [SourceTelescopeData.sourceValues, List.reverse_cons,
        List.append_assoc, List.singleton_append] using ih xs.1 hx xs.2
  | @definition values na value type declarations A a htype hvalue hmember rest ih =>
      have ha := InterpretsLocal.definition (na := na) hΓ htype hvalue hmember
      simpa only [SourceTelescopeData.sourceValues, List.reverse_cons,
        List.append_assoc, List.singleton_append] using ih ha xs

/-- Original source products keep local definitions as actual lets, while only
assumptions contribute to the dependent runtime product. -/
theorem SourceTelescopeData.evaluatesProducts {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} {values : LocalValues.{u}} {declarations : Context} {result : Expr}
    (data : SourceTelescopeData ρ universes globals values declarations)
    (B : data.telescope.Points → Value.{u})
    (hresult : ∀ xs, Evaluates ρ universes globals ((data.sourceValues xs).reverse ++ values) result (B xs)) :
    Evaluates ρ universes globals values (Context.abstractProducts declarations.reverse result)
      (data.telescope.pi B) := by
  induction data with
  | nil => exact hresult PUnit.unit
  | @assumption values na type declarations A htype rest ih =>
      simp only [List.reverse_cons, Context.abstractProducts, List.foldl_append, List.foldl_cons, List.foldl_nil]
      apply Evaluates.product htype
      intro x
      apply ih x (fun xs => B ⟨x, xs⟩)
      intro xs
      simpa only [SourceTelescopeData.sourceValues, List.reverse_cons,
        List.append_assoc, List.singleton_append] using hresult ⟨x, xs⟩
  | @definition values na value type declarations A a htype hvalue hmember rest ih =>
      simp only [List.reverse_cons, Context.abstractProducts, List.foldl_append, List.foldl_cons, List.foldl_nil]
      apply Evaluates.letIn hvalue
      apply ih B
      intro xs
      simpa only [SourceTelescopeData.sourceValues, List.reverse_cons,
        List.append_assoc, List.singleton_append] using hresult xs

/-- Original source lambda abstraction evaluates each definition at its source
scope and produces the runtime trace over assumptions alone. -/
theorem SourceTelescopeData.evaluatesLambdas {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} {values : LocalValues.{u}} {declarations : Context} {body : Expr}
    (data : SourceTelescopeData ρ universes globals values declarations)
    (f : data.telescope.Points → Value.{u})
    (hbody : ∀ xs, Evaluates ρ universes globals ((data.sourceValues xs).reverse ++ values) body (f xs)) :
    Evaluates ρ universes globals values (Context.abstractLambdas declarations.reverse body)
      (data.telescope.trace f) := by
  induction data with
  | nil => exact hbody PUnit.unit
  | @assumption values na type declarations A htype rest ih =>
      simp only [List.reverse_cons, Context.abstractLambdas, List.foldl_append, List.foldl_cons, List.foldl_nil]
      apply Evaluates.lambda htype
      intro x
      apply ih x (fun xs => f ⟨x, xs⟩)
      intro xs
      simpa only [SourceTelescopeData.sourceValues, List.reverse_cons,
        List.append_assoc, List.singleton_append] using hbody ⟨x, xs⟩
  | @definition values na value type declarations A a htype hvalue hmember rest ih =>
      simp only [List.reverse_cons, Context.abstractLambdas, List.foldl_append, List.foldl_cons, List.foldl_nil]
      apply Evaluates.letIn hvalue
      apply ih f
      intro xs
      simpa only [SourceTelescopeData.sourceValues, List.reverse_cons,
        List.append_assoc, List.singleton_append] using hbody xs

/-- Assumption counts add independently of source definition binders. -/
theorem assumptionCount_append (Γ Δ : Context) : (Γ ++ Δ).assumptionCount = Γ.assumptionCount + Δ.assumptionCount := by
  induction Γ with
  | nil => simp only [List.nil_append, Context.assumptionCount, Nat.zero_add]
  | cons d Γ ih => simp only [List.cons_append, Context.assumptionCount, ih, Nat.add_assoc]

/-- Reversing a source telescope does not change the number of runtime arguments. -/
theorem assumptionCount_reverse (Γ : Context) : Context.assumptionCount Γ.reverse = Γ.assumptionCount := by
  induction Γ with
  | nil => rfl
  | cons d Γ ih =>
      simp only [List.reverse_cons, assumptionCount_append, Context.assumptionCount, ih, Nat.add_zero]
      omega

end Silmaril.Proofs.Logic.TypeTheory.CIC.DefinedTelescopeLaws
