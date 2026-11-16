module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Coherence.Thms
import Mathlib.Tactic

public section

namespace Silmaril.Proofs.Logic.TypeTheory.CIC.LocalSemanticsLaws

open Silmaril.Logic.TypeTheory.CIC
open Silmaril.Logic.TypeTheory.CIC.SetSemantics

universe u

private theorem local_lookup_tail {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}}
    {globals : GlobalValues.{u}} {Γ : Context} {values : LocalValues.{u}}
    (hΓ : InterpretsLocal ρ universes globals Γ values) {index : ℕ} {decl : ContextDecl Expr}
    (hlookup : Γ[index]? = some decl) :
    ∃ (pre : LocalValues.{u}) (a : Value.{u}) (tailValues : LocalValues.{u}) (A : Value.{u}),
      values = pre ++ a :: tailValues ∧ pre.length = index ∧
      Evaluates ρ universes globals tailValues decl.type A ∧ a ∈ A ∧
      ∀ body, decl.value = some body → Evaluates ρ universes globals tailValues body a := by
  induction hΓ generalizing index with
  | nil => simp at hlookup
  | @assumption Γ values na type A a hΓ htype hmember ih =>
      show ∃ (pre : LocalValues.{u}) (b : Value.{u}) (tailValues : LocalValues.{u}) (B : Value.{u}),
        a :: values = pre ++ b :: tailValues ∧ pre.length = index ∧
        Evaluates ρ universes globals tailValues decl.type B ∧ b ∈ B ∧
        ∀ body, decl.value = some body → Evaluates ρ universes globals tailValues body b
      cases index with
      | zero =>
          have hdecl : ({ binder := na, type := type } : ContextDecl Expr) = decl := Option.some.inj hlookup
          cases hdecl
          refine ⟨[], a, values, A, rfl, rfl, htype, hmember, ?_⟩
          intro body hbody
          cases hbody
      | succ index =>
          obtain ⟨pre, b, tailValues, B, hvalues, hindex, hB, hb, hbody⟩ := ih hlookup
          exact ⟨a :: pre, b, tailValues, B, congrArg (List.cons a) hvalues,
            congrArg Nat.succ hindex, hB, hb, hbody⟩
  | @definition Γ values na term type A a hΓ htype hterm hmember ih =>
      show ∃ (pre : LocalValues.{u}) (b : Value.{u}) (tailValues : LocalValues.{u}) (B : Value.{u}),
        a :: values = pre ++ b :: tailValues ∧ pre.length = index ∧
        Evaluates ρ universes globals tailValues decl.type B ∧ b ∈ B ∧
        ∀ body, decl.value = some body → Evaluates ρ universes globals tailValues body b
      cases index with
      | zero =>
          have hdecl : ({ binder := na, type := type, value := some term } : ContextDecl Expr) = decl := Option.some.inj hlookup
          cases hdecl
          refine ⟨[], a, values, A, rfl, rfl, htype, hmember, ?_⟩
          intro body hbody
          have heq : term = body := Option.some.inj hbody
          simpa only [← heq] using hterm
      | succ index =>
          obtain ⟨pre, b, tailValues, B, hvalues, hindex, hB, hb, hbody⟩ := ih hlookup
          exact ⟨a :: pre, b, tailValues, B, congrArg (List.cons a) hvalues,
            congrArg Nat.succ hindex, hB, hb, hbody⟩

/-- An interpreted local declaration denotes its actual lifted type and, for definitions, its lifted body. -/
theorem local_lookup {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {Γ : Context} {values : LocalValues.{u}} (hΓ : InterpretsLocal ρ universes globals Γ values)
    {index : ℕ} {decl : ContextDecl Expr} (hlookup : Γ[index]? = some decl) :
    ∃ a A, values[index]? = some a ∧
      Evaluates ρ universes globals values (decl.type.lift (index + 1) 0) A ∧ a ∈ A ∧
      ∀ body, decl.value = some body →
        Evaluates ρ universes globals values (body.lift (index + 1) 0) a := by
  obtain ⟨pre, a, tailValues, A, hvalues, hindex, hA, ha, hbody⟩ := local_lookup_tail hΓ hlookup
  have hlocal : values[index]? = some a := by
    rw [hvalues, ← hindex, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have htype : Evaluates ρ universes globals values (decl.type.lift (index + 1) 0) A := by
    simpa only [List.nil_append, List.length_nil, List.length_append, List.length_singleton,
      hindex, List.append_assoc, List.singleton_append, ← hvalues] using
      evaluates_lift (pre ++ [a]) hA [] tailValues rfl
  refine ⟨a, A, hlocal, htype, ha, ?_⟩
  intro body hdefinition
  simpa only [List.nil_append, List.length_nil, List.length_append, List.length_singleton,
    hindex, List.append_assoc, List.singleton_append, ← hvalues] using
    evaluates_lift (pre ++ [a]) (hbody body hdefinition) [] tailValues rfl

/-- The actual CIC local-variable rule is realized in every interpreted local context. -/
theorem local_rule {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {Γ : Context} {values : LocalValues.{u}} (hΓ : InterpretsLocal ρ universes globals Γ values)
    {index : ℕ} {decl : ContextDecl Expr} (hlookup : Γ[index]? = some decl) :
    HasValueAt ρ universes globals values (.rel index) (decl.type.lift (index + 1) 0) := by
  obtain ⟨a, A, hlocal, htype, ha, hbody⟩ := local_lookup hΓ hlookup
  exact ⟨a, A, Evaluates.rel hlocal, htype, ha⟩

/-- Local delta's actual source and lifted target denote the same value. -/
theorem local_delta_step_values {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    (env : GlobalEnv) {Γ : Context} {values : LocalValues.{u}}
    (hΓ : InterpretsLocal ρ universes globals Γ values)
    {index : ℕ} {decl : ContextDecl Expr} {body : Expr}
    (hlookup : Γ[index]? = some decl) (hbody : decl.value = some body) :
    Step env Γ (.rel index) (body.lift (index + 1) 0) ∧
      ∃ a, Evaluates ρ universes globals values (.rel index) a ∧
        Evaluates ρ universes globals values (body.lift (index + 1) 0) a := by
  obtain ⟨a, A, hlocal, htype, ha, hdefinition⟩ := local_lookup hΓ hlookup
  exact ⟨Step.localDelta hlookup hbody, a, Evaluates.rel hlocal, hdefinition body hbody⟩

/-- Appending older local values preserves every existing lookup and the exact evaluation value. -/
theorem evaluates_append {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {term : Expr} {value : Value.{u}}
    (h : Evaluates ρ universes globals values term value) (older : LocalValues.{u}) :
    Evaluates ρ universes globals (values ++ older) term value := by
  induction h with
  | @rel values index value hlookup =>
      apply Evaluates.rel
      have hbound : index < values.length := (List.getElem?_eq_some_iff.mp hlookup).1
      rwa [List.getElem?_append_left hbound]
  | sort => exact Evaluates.sort
  | product hA hB ihA ihB =>
      apply Evaluates.product ihA
      intro x
      simpa only [List.cons_append] using ihB x
  | lambda hA hf ihA ihf =>
      apply Evaluates.lambda ihA
      intro x
      simpa only [List.cons_append] using ihf x
  | application hf ha ihf iha => exact Evaluates.application ihf iha
  | letIn ha hb iha ihb =>
      apply Evaluates.letIn iha
      simpa only [List.cons_append] using ihb
  | constant hlookup => exact Evaluates.constant hlookup
  | inductiveType hlookup => exact Evaluates.inductiveType hlookup
  | constructor hlookup => exact Evaluates.constructor hlookup
  | caseOf hs hlookup hnone hlength hb ihs ihb =>
      apply Evaluates.caseOf ihs hlookup hnone hlength
      simpa only [List.append_assoc] using ihb

  | projection hs hlookup ihs => exact Evaluates.projection ihs hlookup

/-- A closed declaration interpretation extends to every local environment with its actual declared type. -/
theorem constant_local_rule {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {sig : GlobalContext} (hglobals : InterpretsConstants ρ universes globals sig)
    (values : LocalValues.{u}) {name : String} {ui : List Universe} {declaration : ConstantBody}
    (hlookup : sig.environment.lookupConstant name = some declaration)
    (hinstance : sig.ValidInstance declaration.universes ui) :
    HasValueAt ρ universes globals values (.constant name ui) (Expr.instantiate ui declaration.type) := by
  obtain ⟨A, a, hvalue, htype, ha, hbody⟩ := hglobals.declarations name ui declaration hlookup hinstance
  have hlocaltype : Evaluates ρ universes globals values (Expr.instantiate ui declaration.type) A := by
    simpa only [List.nil_append] using evaluates_append htype values
  exact ⟨a, A, Evaluates.constant hvalue, hlocaltype, ha⟩

/-- The actual CIC let rule uses an interpreted local definition and evaluates its let-shaped type. -/
theorem let_rule {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {Γ : Context} {values : LocalValues.{u}} {na : Binder} {term type body codomain : Expr}
    {A a : Value.{u}} (hΓ : InterpretsLocal ρ universes globals Γ values)
    (htype : Evaluates ρ universes globals values type A)
    (hterm : Evaluates ρ universes globals values term a) (ha : a ∈ A)
    (hbody : InterpretsLocal ρ universes globals ({ binder := na, type := type, value := some term } :: Γ)
      (a :: values) → HasValueAt ρ universes globals (a :: values) body codomain) :
    HasValueAt ρ universes globals values (.letIn na term type body) (.letIn na term type codomain) := by
  have hextended : InterpretsLocal ρ universes globals
      ({ binder := na, type := type, value := some term } :: Γ) (a :: values) :=
    InterpretsLocal.definition hΓ htype hterm ha
  obtain ⟨b, B, hb, hB, hmember⟩ := hbody hextended
  exact ⟨b, B, Evaluates.letIn hterm hb, Evaluates.letIn hterm hB, hmember⟩

/-- Both endpoints of actual global delta denote the genuinely assigned constant value. -/
theorem global_delta_step_values {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {sig : GlobalContext} (hglobals : InterpretsConstants ρ universes globals sig)
    (Γ : Context) (values : LocalValues.{u}) {name : String} {ui : List Universe}
    {declaration : ConstantBody} {body : Expr}
    (hlookup : sig.environment.lookupConstant name = some declaration)
    (hinstance : sig.ValidInstance declaration.universes ui) (hbody : declaration.body = some body) :
    Step sig.environment Γ (.constant name ui) (Expr.instantiate ui body) ∧
      ∃ a, Evaluates ρ universes globals values (.constant name ui) a ∧
        Evaluates ρ universes globals values (Expr.instantiate ui body) a := by
  obtain ⟨A, a, hvalue, htype, ha, hdefinition⟩ := hglobals.declarations name ui declaration hlookup hinstance
  refine ⟨Step.globalDelta hlookup hbody, a, Evaluates.constant hvalue, ?_⟩
  simpa only [List.nil_append] using evaluates_append (hdefinition body hbody) values

end Silmaril.Proofs.Logic.TypeTheory.CIC.LocalSemanticsLaws
