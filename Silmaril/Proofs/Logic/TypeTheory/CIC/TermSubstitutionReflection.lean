module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Coherence.Thms
import Mathlib.Tactic

public section

namespace Silmaril.Proofs.Logic.TypeTheory.CIC.TermSubstitutionReflectionLaws

open Silmaril.Logic.TypeTheory.CIC
open Silmaril.Logic.TypeTheory.CIC.SetSemantics

universe u

private theorem replacement_lookup {α β : Type*} {R : α → β → Prop} {terms : List α} {values : List β}
    (h : List.Forall₂ R terms values) {index : ℕ} {term : α} (hterm : terms[index]? = some term) :
    ∃ value, values[index]? = some value ∧ R term value := by
  have hindex : index < terms.length := (List.getElem?_eq_some_iff.mp hterm).1
  have hvalueindex : index < values.length := h.length_eq ▸ hindex
  refine ⟨values[index], List.getElem?_eq_getElem hvalueindex, ?_⟩
  have hrelation : R terms[index] values[index] := h.get hindex hvalueindex
  exact (List.getElem?_eq_some_iff.mp hterm).2 ▸ hrelation

private theorem evaluates_subst_rel_reflect {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {replacements : List Expr} {replacementValues pre suffix : LocalValues.{u}}
    (hreplacements : List.Forall₂ (Evaluates ρ universes globals suffix) replacements replacementValues)
    {index : ℕ} {value : Value.{u}}
    (h : Evaluates ρ universes globals (pre ++ suffix) ((Term.rel index).subst replacements pre.length) value) :
    Evaluates ρ universes globals (pre ++ replacementValues ++ suffix) (.rel index) value := by
  by_cases hsmall : index < pre.length
  · show Evaluates ρ universes globals (pre ++ replacementValues ++ suffix) (.rel index) value
    have hrel : Evaluates ρ universes globals (pre ++ suffix) (.rel index) value := by
      simpa only [Term.subst, ite_eq_left hsmall] using h
    cases hrel with
    | rel hlookup =>
        apply Evaluates.rel
        have hwide : index < (pre ++ replacementValues).length := by
          simp only [List.length_append]
          omega
        simpa only [List.getElem?_append_left hwide, List.getElem?_append_left hsmall] using hlookup
  · show Evaluates ρ universes globals (pre ++ replacementValues ++ suffix) (.rel index) value
    cases hterm : replacements[index - pre.length]? with
    | some term =>
        show Evaluates ρ universes globals (pre ++ replacementValues ++ suffix) (.rel index) value
        obtain ⟨v, hv, heval⟩ : ∃ v, replacementValues[index - pre.length]? = some v ∧
            Evaluates ρ universes globals suffix term v := replacement_lookup hreplacements hterm
        have hlift : Evaluates ρ universes globals (pre ++ suffix) (term.lift pre.length 0) v := by
          simpa only [List.nil_append, List.length_nil] using evaluates_lift pre heval [] suffix rfl
        have htarget : Evaluates ρ universes globals (pre ++ suffix) (term.lift pre.length 0) value := by
          simpa only [Term.subst, ite_eq_right hsmall, hterm] using h
        have hvalue : v = value := evaluates_deterministic hlift htarget
        have hindex : index - pre.length < replacementValues.length := (List.getElem?_eq_some_iff.mp hv).1
        have hpre : pre.length ≤ index := by omega
        apply Evaluates.rel
        simpa only [List.append_assoc, List.getElem?_append_right hpre, List.getElem?_append_left hindex, hvalue] using hv
    | none =>
        show Evaluates ρ universes globals (pre ++ replacementValues ++ suffix) (.rel index) value
        have hrel : Evaluates ρ universes globals (pre ++ suffix) (.rel (index - replacements.length)) value := by
          simpa only [Term.subst, ite_eq_right hsmall, hterm] using h
        cases hrel with
        | rel hlookup =>
            show Evaluates ρ universes globals (pre ++ replacementValues ++ suffix) (.rel index) value
            have hlength : replacements.length = replacementValues.length := hreplacements.length_eq
            have hmissing : replacements.length ≤ index - pre.length := List.getElem?_eq_none_iff.mp hterm
            have hwide : (pre ++ replacementValues).length ≤ index := by
              simp only [List.length_append]
              omega
            have hpre : pre.length ≤ index - replacements.length := by omega
            have hindex : index - replacements.length - pre.length = index - (pre ++ replacementValues).length := by
              simp only [List.length_append]
              omega
            apply Evaluates.rel
            simpa only [List.getElem?_append_right hwide, List.getElem?_append_right hpre, hindex] using hlookup

/-- Evaluation reflects through actual parallel substitution when all replacements have their stored values. -/
theorem evaluates_subst_reflect {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    (term : Expr) {value : Value.{u}} (replacements : List Expr) (replacementValues pre suffix : LocalValues.{u})
    (hreplacements : List.Forall₂ (Evaluates ρ universes globals suffix) replacements replacementValues)
    (h : Evaluates ρ universes globals (pre ++ suffix) (term.subst replacements pre.length) value) :
    Evaluates ρ universes globals (pre ++ replacementValues ++ suffix) term value := by
  cases hterm : term with
  | rel index => exact evaluates_subst_rel_reflect hreplacements (hterm ▸ h)
  | free name => simp only [hterm, Term.subst] at h; cases h
  | sort sort =>
      have hshape : Evaluates ρ universes globals (pre ++ suffix) (.sort sort) value := by
        simpa only [hterm, Term.subst] using h
      cases hshape
      exact Evaluates.sort
  | prod na domain codomain =>
      show Evaluates ρ universes globals (pre ++ replacementValues ++ suffix) (.prod na domain codomain) value
      have hshape : Evaluates ρ universes globals (pre ++ suffix)
          (.prod na (domain.subst replacements pre.length) (codomain.subst replacements (pre.length + 1))) value := by
        simpa only [hterm, Term.subst] using h
      cases hshape with
      | product hA hB =>
          exact Evaluates.product (evaluates_subst_reflect domain replacements replacementValues pre suffix hreplacements hA)
            (fun x => by simpa only [List.cons_append, List.length_cons] using
              evaluates_subst_reflect codomain replacements replacementValues (x.val :: pre) suffix hreplacements (hB x))
  | lam na domain body =>
      show Evaluates ρ universes globals (pre ++ replacementValues ++ suffix) (.lam na domain body) value
      have hshape : Evaluates ρ universes globals (pre ++ suffix)
          (.lam na (domain.subst replacements pre.length) (body.subst replacements (pre.length + 1))) value := by
        simpa only [hterm, Term.subst] using h
      cases hshape with
      | lambda hA hf =>
          exact Evaluates.lambda (evaluates_subst_reflect domain replacements replacementValues pre suffix hreplacements hA)
            (fun x => by simpa only [List.cons_append, List.length_cons] using
              evaluates_subst_reflect body replacements replacementValues (x.val :: pre) suffix hreplacements (hf x))
  | letIn na argument type body =>
      show Evaluates ρ universes globals (pre ++ replacementValues ++ suffix) (.letIn na argument type body) value
      have hshape : Evaluates ρ universes globals (pre ++ suffix)
          (.letIn na (argument.subst replacements pre.length) (type.subst replacements pre.length)
            (body.subst replacements (pre.length + 1))) value := by
        simpa only [hterm, Term.subst] using h
      cases hshape with
      | letIn ha hb =>
          exact Evaluates.letIn (evaluates_subst_reflect argument replacements replacementValues pre suffix hreplacements ha)
            (by simpa only [List.cons_append, List.length_cons] using
              evaluates_subst_reflect body replacements replacementValues (_ :: pre) suffix hreplacements hb)
  | app function argument =>
      show Evaluates ρ universes globals (pre ++ replacementValues ++ suffix) (.app function argument) value
      have hshape : Evaluates ρ universes globals (pre ++ suffix)
          (.app (function.subst replacements pre.length) (argument.subst replacements pre.length)) value := by
        simpa only [hterm, Term.subst] using h
      cases hshape with
      | application hf ha =>
          exact Evaluates.application
            (evaluates_subst_reflect function replacements replacementValues pre suffix hreplacements hf)
            (evaluates_subst_reflect argument replacements replacementValues pre suffix hreplacements ha)
  | constant name ui =>
      have hshape : Evaluates ρ universes globals (pre ++ suffix) (.constant name ui) value := by
        simpa only [hterm, Term.subst] using h
      cases hshape with
      | constant hlookup => exact Evaluates.constant hlookup
  | inductiveType reference ui =>
      have hshape : Evaluates ρ universes globals (pre ++ suffix) (.inductiveType reference ui) value := by
        simpa only [hterm, Term.subst] using h
      cases hshape with
      | inductiveType hlookup => exact Evaluates.inductiveType hlookup
  | constructor reference index ui =>
      have hshape : Evaluates ρ universes globals (pre ++ suffix) (.constructor reference index ui) value := by
        simpa only [hterm, Term.subst] using h
      cases hshape with
      | constructor hlookup => exact Evaluates.constructor hlookup
  | caseOf ci p scrutinee branches =>
      show Evaluates ρ universes globals (pre ++ replacementValues ++ suffix) (.caseOf ci p scrutinee branches) value
      have hshape : Evaluates ρ universes globals (pre ++ suffix)
          (.caseOf ci { p with
              parameters := p.parameters.map (fun a => a.subst replacements pre.length),
              returnType := p.returnType.subst replacements (p.context.length + pre.length) }
            (scrutinee.subst replacements pre.length)
            (branches.map (fun b => { b with body := b.body.subst replacements (b.context.length + pre.length) }))) value := by
        simpa only [hterm, Term.subst] using h
      cases hshape with
      | @caseOf _ _ _ _ _ index arguments selected _ hs hlookup hnone hlength hb =>
          show Evaluates ρ universes globals (pre ++ replacementValues ++ suffix) (.caseOf ci p scrutinee branches) value
          cases horiginal : branches[index]? with
          | none =>
              have hfalse : (none : Option (Branch Expr)) = some selected := by
                simpa only [List.getElem?_map, horiginal, Option.map_none] using hlookup
              cases hfalse
          | some branch =>
              show Evaluates ρ universes globals (pre ++ replacementValues ++ suffix) (.caseOf ci p scrutinee branches) value
              have hselected : { branch with body := branch.body.subst replacements (branch.context.length + pre.length) } = selected := by
                simpa only [List.getElem?_map, horiginal, Option.map_some, Option.some.injEq] using hlookup
              cases hselected
              have hlength' : arguments.length = ci.parameterCount + branch.context.length := hlength
              have hlocals : (arguments.drop ci.parameterCount).reverse.length = branch.context.length := by
                simp only [List.length_reverse, List.length_drop]
                omega
              have hbody : Evaluates ρ universes globals (((arguments.drop ci.parameterCount).reverse ++ pre) ++ suffix)
                  (branch.body.subst replacements ((arguments.drop ci.parameterCount).reverse ++ pre).length) value := by
                simpa only [List.length_append, hlocals, List.append_assoc] using hb
              apply Evaluates.caseOf
                (evaluates_subst_reflect scrutinee replacements replacementValues pre suffix hreplacements hs) horiginal hnone hlength
              simpa only [List.length_append, hlocals, List.append_assoc] using
                evaluates_subst_reflect branch.body replacements replacementValues
                  ((arguments.drop ci.parameterCount).reverse ++ pre) suffix hreplacements hbody
  | projection reference scrutinee =>
      have hshape : Evaluates ρ universes globals (pre ++ suffix)
          (.projection reference (scrutinee.subst replacements pre.length)) value := by
        simpa only [hterm, Term.subst] using h
      cases hshape with
      | projection hs hlookup =>
          exact Evaluates.projection
            (evaluates_subst_reflect scrutinee replacements replacementValues pre suffix hreplacements hs) hlookup
  | fix definitions index => simp only [hterm, Term.subst] at h; cases h
  | cofix definitions index => simp only [hterm, Term.subst] at h; cases h
termination_by sizeOf term
decreasing_by
  all_goals simp only [hterm, Term.prod.sizeOf_spec, Term.lam.sizeOf_spec, Term.letIn.sizeOf_spec,
    Term.app.sizeOf_spec, Term.caseOf.sizeOf_spec, Term.projection.sizeOf_spec]
  all_goals try omega
  have hmem : branch ∈ branches := List.mem_of_getElem? horiginal
  have hsmall := List.sizeOf_lt_of_mem hmem
  cases branch
  simp only [Branch.mk.sizeOf_spec] at hsmall ⊢
  omega

/-- Exact equivalence under parallel substitution, with the evaluated replacement list explicit. -/
theorem evaluates_subst_iff {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {term : Expr} {value : Value.{u}} {replacements : List Expr} {replacementValues pre suffix : LocalValues.{u}}
    (hreplacements : List.Forall₂ (Evaluates ρ universes globals suffix) replacements replacementValues) :
    Evaluates ρ universes globals (pre ++ suffix) (term.subst replacements pre.length) value ↔
      Evaluates ρ universes globals (pre ++ replacementValues ++ suffix) term value :=
  ⟨evaluates_subst_reflect term replacements replacementValues pre suffix hreplacements,
    fun h => evaluates_subst h replacements replacementValues pre suffix rfl hreplacements⟩

/-- Reflection through a single actual binder; the replacement may depend on the surviving locals. -/
theorem evaluates_subst_one_reflect {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} (body : Expr) {argument : Expr} {a b : Value.{u}}
    (hargument : Evaluates ρ universes globals values argument a)
    (hbody : Evaluates ρ universes globals values (body.subst [argument] 0) b) :
    Evaluates ρ universes globals (a :: values) body b := by
  simpa only [List.nil_append, List.length_nil, List.singleton_append] using
    evaluates_subst_reflect body [argument] [a] [] values (.cons hargument .nil) hbody

/-- Normalized body evaluation reconstructs the actual raw source let at the same value. -/
theorem evaluates_let_of_subst {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {na : Binder} {argument type body : Expr} {a b : Value.{u}}
    (hargument : Evaluates ρ universes globals values argument a)
    (hbody : Evaluates ρ universes globals values (body.subst [argument] 0) b) :
    Evaluates ρ universes globals values (.letIn na argument type body) b :=
  .letIn hargument (evaluates_subst_one_reflect body hargument hbody)

/-- The stored replacement values cannot be chosen independently of evaluation. -/
theorem substitution_reflection_value_mismatch {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    {values : LocalValues.{u}} {argument : Expr} {a b : Value.{u}}
    (hargument : Evaluates ρ universes globals values argument a) (hne : a ≠ b) :
    Evaluates ρ universes globals values ((Term.rel 0).subst [argument] 0) a ∧
      ¬ Evaluates ρ universes globals (b :: values) (.rel 0) a := by
  constructor
  · simpa only [Term.subst, Nat.lt_irrefl, ite_false, Nat.sub_self, List.getElem?_cons_zero, Term.lift_zero] using hargument
  · intro h
    cases h with
    | rel hlookup => exact hne (Option.some.inj hlookup).symm

/-- Normalization can discard an unevaluable let value; the reconstruction premise is essential. -/
theorem zeta_reconstruction_needs_value {ρ : LevelName → ℕ} {universes : ℕ → Value.{u}} {globals : GlobalValues.{u}}
    (values : LocalValues.{u}) :
    Evaluates ρ universes globals values ((Term.sort .prop).subst [.free "missing"] 0) (sortValue ρ universes .prop) ∧
      ¬ Evaluates ρ universes globals values (.letIn {} (.free "missing") (.sort .prop) (.sort .prop))
        (sortValue ρ universes .prop) := by
  constructor
  · simpa only [Term.subst] using (Evaluates.sort (ρ := ρ) (universes := universes) (globals := globals) (values := values) (sort := .prop))
  · intro h
    cases h with
    | letIn hvalue _ => cases hvalue

end Silmaril.Proofs.Logic.TypeTheory.CIC.TermSubstitutionReflectionLaws
