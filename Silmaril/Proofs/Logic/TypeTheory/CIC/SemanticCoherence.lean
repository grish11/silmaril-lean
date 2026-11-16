module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Thms
public import Silmaril.Logic.TypeTheory.CIC.Semantics.ConstructorValues.Tags.Thms
import Mathlib.Tactic

public section

namespace Silmaril.Proofs.Logic.TypeTheory.CIC.SemanticCoherenceLaws

open Silmaril.Logic.TypeTheory.CIC
open Silmaril.Logic.TypeTheory.CIC.SetSemantics

universe u

theorem evaluates_deterministic {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {term : Expr} {value other : Value.{u}}
    (h : Evaluates ρ universes globals values term value) (hother : Evaluates ρ universes globals values term other) :
    value = other := by
  induction h generalizing other with
  | rel hlookup =>
      cases hother with
      | rel hlookup' => exact Option.some.inj (hlookup.symm.trans hlookup')
  | sort => cases hother; rfl
  | @product values na domain codomain A B hA hB ihA ihB =>
      cases hother with
      | @product _ _ _ _ A' B' hA' hB' =>
          have hdomain : A = A' := ihA hA'
          cases hdomain
          have hcodomain : B = B' := funext fun x => ihB x (hB' x)
          cases hcodomain
          rfl
  | @lambda values na domain body A f hA hf ihA ihf =>
      cases hother with
      | @lambda _ _ _ _ A' f' hA' hf' =>
          have hdomain : A = A' := ihA hA'
          cases hdomain
          have hvalues : f = f' := funext fun x => ihf x (hf' x)
          cases hvalues
          rfl
  | application hf ha ihf iha =>
      cases hother with
      | application hf' ha' =>
          exact congrArg₂ traceApply (ihf hf') (iha ha')
  | letIn ha hb iha ihb =>
      cases hother with
      | letIn ha' hb' =>
          have hvalue := iha ha'
          cases hvalue
          exact ihb hb'
  | constant hlookup =>
      cases hother with
      | constant hlookup' => exact Option.some.inj (hlookup.symm.trans hlookup')
  | inductiveType hlookup =>
      cases hother with
      | inductiveType hlookup' => exact Option.some.inj (hlookup.symm.trans hlookup')
  | constructor hlookup =>
      cases hother with
      | constructor hlookup' => exact Option.some.inj (hlookup.symm.trans hlookup')
  | caseOf hscrutinee hlookup hnodefinitions hlength hbody ihscrutinee ihbody =>
      show _ = other
      cases hother with
      | caseOf hscrutinee' hlookup' hnodefinitions' hlength' hbody' =>
          have htags := constructorValue_inj.mp (ihscrutinee hscrutinee')
          cases htags.1
          cases htags.2
          have hbranch := Option.some.inj (hlookup.symm.trans hlookup')
          cases hbranch
          exact ihbody hbody'

  | projection hscrutinee hlookup ihscrutinee =>
      cases hother with
      | projection hscrutinee' hlookup' =>
          have harguments := (constructorValue_inj.mp (ihscrutinee hscrutinee')).2
          cases harguments
          exact Option.some.inj (hlookup.symm.trans hlookup')

theorem missing_constant_rejected {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {name : String} {ui : List Universe} {value : Value.{u}}
    (hmissing : globals.constant name ui = none) : ¬ Evaluates ρ universes globals values (.constant name ui) value := by
  intro h
  cases h with
  | constant hlookup =>
      have hfalse : none = some value := hmissing.symm.trans hlookup
      cases hfalse

private theorem lookup_insert {α : Type*} (pre inserted suffix : List α) (index : ℕ) :
    (pre ++ inserted ++ suffix)[if pre.length ≤ index then index + inserted.length else index]? =
      (pre ++ suffix)[index]? := by
  by_cases h : pre.length ≤ index
  · rw [ite_eq_left h]
    have hshift : (pre ++ inserted).length ≤ index + inserted.length := by
      simp only [List.length_append]
      omega
    rw [List.getElem?_append_right hshift, List.getElem?_append_right h]
    simp only [List.length_append, Nat.add_sub_add_right]
  · have hlt : index < pre.length := Nat.lt_of_not_ge h
    have hprefix : index < (pre ++ inserted).length := by
      simp only [List.length_append]
      omega
    rw [ite_eq_right h, List.getElem?_append_left hprefix, List.getElem?_append_left hlt,
      List.getElem?_append_left hlt]

/-- Inserting arbitrary local values agrees with CIC's actual de Bruijn lifting operation. -/
theorem evaluates_lift {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    (inserted : LocalValues.{u}) {values : LocalValues.{u}} {term : Expr} {value : Value.{u}}
    (h : Evaluates ρ universes globals values term value) :
    ∀ pre suffix, values = pre ++ suffix →
      Evaluates ρ universes globals (pre ++ inserted ++ suffix) (term.lift inserted.length pre.length) value := by
  induction h with
  | rel hlookup =>
      intro pre suffix hvalues
      simp only [Term.lift]
      apply Evaluates.rel
      rw [lookup_insert]
      simpa only [hvalues] using hlookup
  | sort => intro pre suffix hvalues; simpa only [Term.lift] using (Evaluates.sort (values := pre ++ inserted ++ suffix))
  | @product values na domain codomain A B hA hB ihA ihB =>
      intro pre suffix hvalues
      simp only [Term.lift]
      apply Evaluates.product (A := A) (B := B) (ihA pre suffix hvalues)
      intro x
      simpa only [List.cons_append, List.length_cons] using
        ihB x (x :: pre) suffix (congrArg (List.cons (x : Value.{u})) hvalues)
  | @lambda values na domain body A f hA hf ihA ihf =>
      intro pre suffix hvalues
      simp only [Term.lift]
      apply Evaluates.lambda (A := A) (f := f) (ihA pre suffix hvalues)
      intro x
      simpa only [List.cons_append, List.length_cons] using
        ihf x (x :: pre) suffix (congrArg (List.cons (x : Value.{u})) hvalues)
  | application hf ha ihf iha =>
      intro pre suffix hvalues
      simpa only [Term.lift] using Evaluates.application (ihf pre suffix hvalues) (iha pre suffix hvalues)
  | @letIn values na term type body a b ha hb iha ihb =>
      intro pre suffix hvalues
      simp only [Term.lift]
      apply Evaluates.letIn (iha pre suffix hvalues)
      simpa only [List.cons_append, List.length_cons] using
        ihb (a :: pre) suffix (congrArg (List.cons a) hvalues)
  | constant hlookup => intro pre suffix hvalues; simpa only [Term.lift] using (Evaluates.constant (values := pre ++ inserted ++ suffix) hlookup)
  | inductiveType hlookup => intro pre suffix hvalues; simpa only [Term.lift] using (Evaluates.inductiveType (values := pre ++ inserted ++ suffix) hlookup)
  | constructor hlookup => intro pre suffix hvalues; simpa only [Term.lift] using (Evaluates.constructor (values := pre ++ inserted ++ suffix) hlookup)


  | @caseOf values ci p scrutinee branches index arguments branch value hs hlookup hnone hlength hb ihs ihb =>
      show ∀ pre suffix, values = pre ++ suffix →
        Evaluates ρ universes globals (pre ++ inserted ++ suffix)
          ((Term.caseOf ci p scrutinee branches).lift inserted.length pre.length) value
      intro pre suffix hvalues
      simp only [Term.lift]
      let shifted : Branch Expr := { branch with body := branch.body.lift inserted.length (branch.context.length + pre.length) }
      have hselected : (branches.map (fun b =>
          { b with body := b.body.lift inserted.length (b.context.length + pre.length) }))[index]? = some shifted := by
        simp only [List.getElem?_map, hlookup, Option.map_some]
        rfl
      have hlocals : (arguments.drop ci.parameterCount).reverse.length = branch.context.length := by
        simp only [List.length_reverse, List.length_drop]
        omega
      apply Evaluates.caseOf (branch := shifted) (ihs pre suffix hvalues) hselected hnone hlength
      have hbodyvalues : (arguments.drop ci.parameterCount).reverse ++ values =
          ((arguments.drop ci.parameterCount).reverse ++ pre) ++ suffix := by
        rw [hvalues, List.append_assoc]
      simpa only [List.length_append, hlocals, List.append_assoc] using
        ihb ((arguments.drop ci.parameterCount).reverse ++ pre) suffix hbodyvalues

  | projection hs hlookup ihs =>
      intro pre suffix hvalues
      simpa only [Term.lift] using Evaluates.projection (ihs pre suffix hvalues) hlookup

private theorem forall₂_lookup {α β : Type*} {R : α → β → Prop} {terms : List α} {values : List β}
    (h : List.Forall₂ R terms values) {index : ℕ} {term : α} (hterm : terms[index]? = some term) :
    ∃ value, values[index]? = some value ∧ R term value := by
  induction h generalizing index with
  | nil => simp at hterm
  | @cons head value terms values hhead htail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hterm
          cases hterm
          exact ⟨value, rfl, hhead⟩
      | succ index => exact ih hterm

private theorem evaluates_subst_rel {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {replacements : List Expr} {replacementValues pre suffix : LocalValues.{u}}
    (hreplacements : List.Forall₂ (Evaluates ρ universes globals suffix) replacements replacementValues)
    {index : ℕ} {value : Value.{u}} (hlookup : (pre ++ replacementValues ++ suffix)[index]? = some value) :
    Evaluates ρ universes globals (pre ++ suffix) ((Term.rel index).subst replacements pre.length) value := by
  simp only [Term.subst]
  by_cases hsmall : index < pre.length
  · show Evaluates ρ universes globals (pre ++ suffix) _ value
    rw [ite_eq_left hsmall]
    apply Evaluates.rel
    have hwide : index < (pre ++ replacementValues).length := by
      simp only [List.length_append]
      omega
    rw [List.getElem?_append_left hwide, List.getElem?_append_left hsmall] at hlookup
    rwa [List.getElem?_append_left hsmall]
  · show Evaluates ρ universes globals (pre ++ suffix) _ value
    rw [ite_eq_right hsmall]
    cases hterm : replacements[index - pre.length]? with
    | some term =>
        show Evaluates ρ universes globals (pre ++ suffix) (term.lift pre.length 0) value
        obtain ⟨v, hv, heval⟩ := forall₂_lookup hreplacements hterm
        have hbound : index - pre.length < replacementValues.length :=
          (List.getElem?_eq_some_iff.mp hv).1
        have hpre : pre.length ≤ index := by omega
        rw [List.append_assoc, List.getElem?_append_right hpre,
          List.getElem?_append_left hbound, hv] at hlookup
        have heq : v = value := Option.some.inj hlookup
        cases heq
        simpa only [List.nil_append, List.length_nil] using
          evaluates_lift pre heval [] suffix rfl
    | none =>
        show Evaluates ρ universes globals (pre ++ suffix) (.rel (index - replacements.length)) value
        have hlength : replacements.length = replacementValues.length := hreplacements.length_eq
        have hmissing : replacements.length ≤ index - pre.length := List.getElem?_eq_none_iff.mp hterm
        have hwide : (pre ++ replacementValues).length ≤ index := by
          simp only [List.length_append]
          omega
        have hpre : pre.length ≤ index - replacements.length := by omega
        apply Evaluates.rel
        rw [List.getElem?_append_right hwide] at hlookup
        rw [List.getElem?_append_right hpre]
        have hindex : index - replacements.length - pre.length = index - (pre ++ replacementValues).length := by
          simp only [List.length_append]
          omega
        rwa [hindex]

/-- Simultaneous substitution preserves the exact value when each replacement is evaluated in the surviving context. -/
theorem evaluates_subst {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {term : Expr} {value : Value.{u}}
    (h : Evaluates ρ universes globals values term value) :
    ∀ (replacements : List Expr) (replacementValues pre suffix : LocalValues.{u}),
      values = pre ++ replacementValues ++ suffix →
      List.Forall₂ (Evaluates ρ universes globals suffix) replacements replacementValues →
      Evaluates ρ universes globals (pre ++ suffix) (term.subst replacements pre.length) value := by
  induction h with
  | rel hlookup =>
      intro replacements replacementValues pre suffix hvalues hreplacements
      apply evaluates_subst_rel hreplacements
      simpa only [hvalues] using hlookup
  | sort =>
      intro replacements replacementValues pre suffix hvalues hreplacements
      simpa only [Term.subst] using (Evaluates.sort (values := pre ++ suffix))
  | @product values na domain codomain A B hA hB ihA ihB =>
      intro replacements replacementValues pre suffix hvalues hreplacements
      simp only [Term.subst]
      apply Evaluates.product (A := A) (B := B) (ihA replacements replacementValues pre suffix hvalues hreplacements)
      intro x
      simpa only [List.cons_append, List.length_cons] using
        ihB x replacements replacementValues ((x : Value.{u}) :: pre) suffix
          (congrArg (List.cons (x : Value.{u})) hvalues) hreplacements
  | @lambda values na domain body A f hA hf ihA ihf =>
      intro replacements replacementValues pre suffix hvalues hreplacements
      simp only [Term.subst]
      apply Evaluates.lambda (A := A) (f := f) (ihA replacements replacementValues pre suffix hvalues hreplacements)
      intro x
      simpa only [List.cons_append, List.length_cons] using
        ihf x replacements replacementValues ((x : Value.{u}) :: pre) suffix
          (congrArg (List.cons (x : Value.{u})) hvalues) hreplacements
  | application hf ha ihf iha =>
      intro replacements replacementValues pre suffix hvalues hreplacements
      simpa only [Term.subst] using Evaluates.application
        (ihf replacements replacementValues pre suffix hvalues hreplacements)
        (iha replacements replacementValues pre suffix hvalues hreplacements)
  | @letIn values na term type body a b ha hb iha ihb =>
      intro replacements replacementValues pre suffix hvalues hreplacements
      simp only [Term.subst]
      apply Evaluates.letIn (iha replacements replacementValues pre suffix hvalues hreplacements)
      simpa only [List.cons_append, List.length_cons] using
        ihb replacements replacementValues (a :: pre) suffix (congrArg (List.cons a) hvalues) hreplacements
  | constant hlookup =>
      intro replacements replacementValues pre suffix hvalues hreplacements
      simpa only [Term.subst] using (Evaluates.constant (values := pre ++ suffix) hlookup)
  | inductiveType hlookup =>
      intro replacements replacementValues pre suffix hvalues hreplacements
      simpa only [Term.subst] using (Evaluates.inductiveType (values := pre ++ suffix) hlookup)
  | constructor hlookup =>
      intro replacements replacementValues pre suffix hvalues hreplacements
      simpa only [Term.subst] using (Evaluates.constructor (values := pre ++ suffix) hlookup)


  | @caseOf values ci p scrutinee branches index arguments branch value hs hlookup hnone hlength hb ihs ihb =>
      show ∀ (replacements : List Expr) (replacementValues pre suffix : LocalValues.{u}),
        values = pre ++ replacementValues ++ suffix →
        List.Forall₂ (Evaluates ρ universes globals suffix) replacements replacementValues →
        Evaluates ρ universes globals (pre ++ suffix)
          ((Term.caseOf ci p scrutinee branches).subst replacements pre.length) value
      intro replacements replacementValues pre suffix hvalues hreplacements
      simp only [Term.subst]
      let substituted : Branch Expr := { branch with body := branch.body.subst replacements (branch.context.length + pre.length) }
      have hselected : (branches.map (fun b =>
          { b with body := b.body.subst replacements (b.context.length + pre.length) }))[index]? = some substituted := by
        simp only [List.getElem?_map, hlookup, Option.map_some]
        rfl
      have hlocals : (arguments.drop ci.parameterCount).reverse.length = branch.context.length := by
        simp only [List.length_reverse, List.length_drop]
        omega
      apply Evaluates.caseOf (branch := substituted)
        (ihs replacements replacementValues pre suffix hvalues hreplacements) hselected hnone hlength
      have hbodyvalues : (arguments.drop ci.parameterCount).reverse ++ values =
          ((arguments.drop ci.parameterCount).reverse ++ pre) ++ replacementValues ++ suffix := by
        rw [hvalues]
        simp only [List.append_assoc]
      simpa only [List.length_append, hlocals, List.append_assoc] using
        ihb replacements replacementValues ((arguments.drop ci.parameterCount).reverse ++ pre) suffix
          hbodyvalues hreplacements

  | projection hs hlookup ihs =>
      intro replacements replacementValues pre suffix hvalues hreplacements
      simpa only [Term.subst] using Evaluates.projection
        (ihs replacements replacementValues pre suffix hvalues hreplacements) hlookup

/-- The one-binder instance uses CIC's actual parallel substitution, with no additional coherence premise. -/
theorem evaluates_subst_one {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {body argument : Expr} {a b : Value.{u}}
    (hbody : Evaluates ρ universes globals (a :: values) body b)
    (hargument : Evaluates ρ universes globals values argument a) :
    Evaluates ρ universes globals values (body.subst [argument] 0) b := by
  have hreplacements : List.Forall₂ (Evaluates ρ universes globals values) [argument] [a] :=
    .cons hargument .nil
  simpa only [List.nil_append, List.length_nil] using
    evaluates_subst hbody [argument] [a] [] values rfl hreplacements

/-- The actual dependent application rule follows from evaluation of the codomain under its binder. -/
theorem application_substitution_rule {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {function argument codomain : Expr} {A : Value.{u}} {B : A → Value.{u}}
    {f : Value.{u}} (x : A)
    (hf : Evaluates ρ universes globals values function f) (hmember : f ∈ tracePi A B)
    (hx : Evaluates ρ universes globals values argument x)
    (hcodomain : Evaluates ρ universes globals ((x : Value.{u}) :: values) codomain (B x)) :
    HasValueAt ρ universes globals values (.app function argument) (codomain.subst [argument] 0) :=
  application_rule x hf hmember hx (evaluates_subst_one hcodomain hx)

/-- Both endpoints of an actual CIC beta step have the same typed-domain trace value. -/
theorem beta_step_values {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    (env : GlobalEnv) (Γ : Context) {values : LocalValues.{u}} {na : Binder}
    {domain body argument : Expr} {A : Value.{u}} {f : A → Value.{u}}
    (hA : Evaluates ρ universes globals values domain A)
    (hf : ∀ x : A, Evaluates ρ universes globals ((x : Value.{u}) :: values) body (f x))
    (x : A) (hx : Evaluates ρ universes globals values argument x) :
    Step env Γ (.app (.lam na domain body) argument) (body.subst [argument] 0) ∧
      Evaluates ρ universes globals values (.app (.lam na domain body) argument) (f x) ∧
      Evaluates ρ universes globals values (body.subst [argument] 0) (f x) :=
  ⟨Step.beta, evaluates_beta hA hf x hx, evaluates_subst_one (hf x) hx⟩

/-- Both endpoints of an actual CIC zeta step have the same value. -/
theorem zeta_step_values {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    (env : GlobalEnv) (Γ : Context) {values : LocalValues.{u}} {na : Binder}
    {term type body : Expr} {a b : Value.{u}}
    (hterm : Evaluates ρ universes globals values term a)
    (hbody : Evaluates ρ universes globals (a :: values) body b) :
    Step env Γ (.letIn na term type body) (body.subst [term] 0) ∧
      Evaluates ρ universes globals values (.letIn na term type body) b ∧
      Evaluates ρ universes globals values (body.subst [term] 0) b :=
  ⟨Step.zeta, Evaluates.letIn hterm hbody, evaluates_subst_one hbody hterm⟩

end Silmaril.Proofs.Logic.TypeTheory.CIC.SemanticCoherenceLaws
