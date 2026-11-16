module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Names.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
open CategoryTheory Uflia.SExpr
open Uflia.Quantified.SExpr
variable {E F : Environment}

/-- Fresh target names and actual mapped binder types, in original source order. -/
def freshBinderTypes (f : environmentSignature E ⟶ environmentSignature F) :
    Nat → List (String × SortCode String) → List (String × SortCode String)
  | _, [] => []
  | next, (_, sort) :: rest =>
      (freshName next, f.sorts sort) :: freshBinderTypes f (next + 1) rest

/-- Every source binder emits its mapped sort atom and a fresh lexical name. -/
theorem renameBinders_success (f : NameMap E F) (bindings : List Expr)
    (parsed : List (String × SortCode String)) (decoded : binders? E bindings = some parsed)
    (next : Nat) :
    ∃ output, renameBinders? f next bindings = some (output, binderScope next parsed) ∧
      binders? F output = some (freshBinderTypes f.abstract next parsed) ∧
      output.length = bindings.length ∧ parsed.length = bindings.length := by
  induction bindings generalizing parsed next with
  | nil =>
    cases decoded
    exact ⟨[], rfl, rfl, rfl, rfl⟩
  | cons binding rest ih =>
    cases binding with
    | atom name => simp [binders?] at decoded
    | list parts =>
      cases parts with
      | nil => simp [binders?] at decoded
      | cons first parts =>
        cases first with
        | list xs => simp [binders?] at decoded
        | atom name =>
          cases parts with
          | nil => simp [binders?] at decoded
          | cons sort parts =>
            cases parts with
            | cons extra parts => simp [binders?] at decoded
            | nil =>
              have checks : simpleSymbol name = true ∧ reserved.contains name = false := by
                cases hs : simpleSymbol name <;> cases hr : reserved.contains name <;>
                  simp_all [binders?]
              simp only [binders?, checks.1, checks.2, Bool.not_true, Bool.false_or,
                Bool.false_eq_true, ↓reduceIte] at decoded
              change (E.sort? sort).bind _ = some parsed at decoded
              obtain ⟨s, hs, decoded⟩ := Option.bind_eq_some_iff.mp decoded
              change (binders? E rest).bind _ = some parsed at decoded
              obtain ⟨tail, ht, decoded⟩ := Option.bind_eq_some_iff.mp decoded
              have same : (name, s) :: tail = parsed := Option.some.inj decoded
              subst parsed
              obtain ⟨output, renamed, target, lengths, sourceLengths⟩ := ih tail ht (next + 1)
              refine ⟨.list [.atom (freshName next), sortExpr (f.abstract.sorts s)] :: output, ?_, ?_, ?_, ?_⟩
              · simp only [renameBinders?, checks.1, checks.2, Bool.not_true, Bool.false_or,
                  Bool.false_eq_true, ↓reduceIte, hs, renamed, binderScope]
                rfl
              · simp only [binders?, freshName_simple, freshName_not_reserved, Bool.not_true,
                  Bool.false_or, Bool.false_eq_true, ↓reduceIte, f.sorts sort s hs,
                  target, freshBinderTypes]
                rfl
              · simp only [List.length_cons, lengths]
              · simp only [List.length_cons, sourceLengths]

end Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
