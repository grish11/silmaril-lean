module

public import Silmaril.Proofs.Logic.Smt.Uflia.Quantified.SExpr.Renaming.Operators

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
open CategoryTheory Silmaril.Logic.Smt.Uflia.SExpr
variable {E F : Environment}

def binderScope : Nat → List (String × SortCode String) → Scope
  | _, [] => []
  | next, (name, _) :: rest => (name, freshName next) :: binderScope (next + 1) rest

def freshBinderTypes : Nat → List (String × SortCode String) → List (String × SortCode String)
  | _, [] => []
  | next, (_, sort) :: rest => (freshName next, sort) :: freshBinderTypes (next + 1) rest

/-- All original binder sorts remain admissible; only local names change. -/
theorem renameBinders_success (f : NameMap E F) (bindings : List Expr)
    (parsed : List (String × SortCode String)) (decoded : binders? E bindings = some parsed)
    (next : Nat) :
    ∃ output, renameBinders? E next bindings = some (output, binderScope next parsed) ∧
      binders? F output = some (freshBinderTypes next parsed) ∧
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
              refine ⟨.list [.atom (freshName next), sort] :: output, ?_, ?_, ?_, ?_⟩
              · simp only [renameBinders?, checks.1, checks.2, Bool.not_true, Bool.false_or,
                  Bool.false_eq_true, ↓reduceIte, hs, renamed, binderScope]
                rfl
              · simp only [binders?, freshName_simple, freshName_not_reserved, Bool.not_true,
                  Bool.false_or, Bool.false_eq_true, ↓reduceIte, f.sorts sort s hs,
                  target, freshBinderTypes]
                rfl
              · simp only [List.length_cons, lengths]
              · simp only [List.length_cons, sourceLengths]

/-- Adding a quantified variable weakens every previously captured typed value.
The fresh target key is paired with the same new index zero. -/
def pushBinder {k : Nat} {Γ : Fin k → SortCode String}
    (locals : List (Local E Γ)) (next : Nat) (name : String) (sort : SortCode String) :
    List (Local E (Fin.cases sort Γ)) :=
  ⟨name, freshName next, ⟨sort, .var 0⟩⟩ :: locals.map (weakenLocal sort)

@[simp] theorem sourceLocals_pushBinder {k : Nat} {Γ : Fin k → SortCode String}
    (locals : List (Local E Γ)) (next : Nat) (name : String) (sort : SortCode String) :
    sourceLocals (pushBinder locals next name sort) =
      (name, ⟨sort, .var 0⟩) :: (sourceLocals locals).map
        (fun entry => ((entry.1, ⟨entry.2.sort, entry.2.term.weaken sort⟩) : String × PackedTerm E _)) := by
  simp only [pushBinder, sourceLocals, List.map_cons, List.map_map, Function.comp_def, weakenLocal]

@[simp] theorem targetLocals_pushBinder {k : Nat} {Γ : Fin k → SortCode String}
    (f : E.signature ⟶ F.signature) (locals : List (Local E Γ))
    (next : Nat) (name : String) (sort : SortCode String) :
    targetLocals f (pushBinder locals next name sort) =
      (freshName next, ⟨sort, .var 0⟩) :: (targetLocals f locals).map
        (fun entry => ((entry.1, ⟨entry.2.sort, entry.2.term.weaken sort⟩) : String × PackedTerm F _)) := by
  simp only [pushBinder, targetLocals, List.map_cons, List.map_map, Function.comp_def,
    weakenLocal, mapPacked, Term.map, Term.map_weaken]

theorem pushBinder_valid {k : Nat} {Γ : Fin k → SortCode String}
    (locals : List (Local E Γ)) (next : Nat) (valid : ValidScope F next locals)
    (bound : firstFresh F ≤ next) (name : String) (sort : SortCode String) :
    ValidScope F (next + 1) (pushBinder locals next name sort) :=
  valid_fresh_cons F next _ (valid_weaken F next locals valid sort) bound name _

/-- General binder-list transport at arbitrary open contexts. One recursive
body witness is produced after every same-list binder has been introduced. -/
theorem quantify_success (f : NameMap E F) (universal : Bool)
    (source : ∀ {k : Nat} {Γ : Fin k → SortCode String},
      SExpr.Locals E Γ → Expr → Option (PackedTerm E Γ))
    (target : ∀ {k : Nat} {Γ : Fin k → SortCode String},
      SExpr.Locals F Γ → Expr → Option (PackedTerm F Γ))
    (rename : Scope → Nat → Expr → Option Expr)
    (bodySuccess : ∀ {k : Nat} {Γ : Fin k → SortCode String}
      (locals : List (Local E Γ)) (next : Nat), ValidScope F next locals → firstFresh F ≤ next →
      ∀ body value, source (sourceLocals locals) body = some value → ∃ output,
        rename (localScope locals) next body = some output ∧
          target (targetLocals f.abstract locals) output = some (mapPacked f.abstract value))
    {k : Nat} {Γ : Fin k → SortCode String} (locals : List (Local E Γ))
    (next : Nat) (valid : ValidScope F next locals) (bound : firstFresh F ≤ next)
    (bindings : List (String × SortCode String)) (body : Expr) (value : PackedTerm E Γ)
    (decoded : quantify? E universal source (sourceLocals locals) bindings body = some value) :
    ∃ output, rename ((binderScope next bindings).reverse ++ localScope locals)
        (next + bindings.length) body = some output ∧
      quantify? F universal target (targetLocals f.abstract locals)
        (freshBinderTypes next bindings) output = some (mapPacked f.abstract value) := by
  induction bindings generalizing k Γ locals next value with
  | nil =>
    simpa only [binderScope, freshBinderTypes, List.reverse_nil, List.nil_append, List.length_nil,
      Nat.add_zero, quantify?] using bodySuccess locals next valid bound body value decoded
  | cons binding bindings ih =>
    rcases binding with ⟨name, sort⟩
    change (quantify? E universal source
      ((name, ⟨sort, .var 0⟩) :: (sourceLocals locals).map
        (fun entry => (entry.1, ⟨entry.2.sort, entry.2.term.weaken sort⟩))) bindings body).bind _ = some value at decoded
    rw [← sourceLocals_pushBinder locals next name sort] at decoded
    obtain ⟨inner, decodedInner, decoded⟩ := Option.bind_eq_some_iff.mp decoded
    change (inner.expect? .bool).bind _ = some value at decoded
    obtain ⟨term, typed, decoded⟩ := Option.bind_eq_some_iff.mp decoded
    have same : (⟨.bool, if universal then .all sort term else .ex sort term⟩ : PackedTerm E Γ) = value :=
      Option.some.inj decoded
    subst value
    obtain ⟨output, renamed, mapped⟩ := ih (pushBinder locals next name sort) (next + 1)
      (pushBinder_valid locals next valid bound name sort) (by omega) inner decodedInner
    refine ⟨output, ?_, ?_⟩
    · simpa [binderScope, pushBinder, localScope, weakenLocal, Function.comp_def,
        List.reverse_cons, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using renamed
    · simp only [freshBinderTypes, quantify?]
      rw [← targetLocals_pushBinder f.abstract locals next name sort, mapped]
      change ((mapPacked f.abstract inner).expect? .bool).bind _ = _
      rw [expect_map, typed]
      cases universal <;> rfl

/-- Assemble a complete quantifier constructor from admitted original binders
and one recursive body transport. No injectivity of global names is used. -/
theorem renameQuantifier_success (f : NameMap E F) (fuel : Nat)
    (bodySuccess : ∀ {k : Nat} {Γ : Fin k → SortCode String}
      (locals : List (Local E Γ)) (next : Nat), ValidScope F next locals → firstFresh F ≤ next →
      ∀ body value, decodeScopedFuel? E fuel (sourceLocals locals) body = some value → ∃ output,
        renameScopedFuel? f fuel (localScope locals) next body = some output ∧
          decodeScopedFuel? F fuel (targetLocals f.abstract locals) output = some (mapPacked f.abstract value))
    {k : Nat} {Γ : Fin k → SortCode String} (locals : List (Local E Γ))
    (next : Nat) (valid : ValidScope F next locals) (bound : firstFresh F ≤ next)
    (universal : Bool) (head : Expr) (rest : List Expr)
    (parsed : List (String × SortCode String))
    (parsedBinders : binders? E (head :: rest) = some parsed)
    (body : Expr) (value : PackedTerm E Γ)
    (decoded : quantify? E universal (fun locals body => decodeScopedFuel? E fuel locals body)
      (sourceLocals locals) parsed body = some value) :
    ∃ output,
      renameScopedFuel? f (fuel + 1) (localScope locals) next
        (.list [.atom (if universal then "forall" else "exists"), .list (head :: rest), body]) = some output ∧
      decodeScopedFuel? F (fuel + 1) (targetLocals f.abstract locals) output =
        some (mapPacked f.abstract value) := by
  obtain ⟨bindings, renamedBinders, targetBinders, lengths, parsedLengths⟩ :=
    renameBinders_success f (head :: rest) parsed parsedBinders next
  obtain ⟨output, renamedBody, mappedBody⟩ := quantify_success f universal
    (fun locals body => decodeScopedFuel? E fuel locals body)
    (fun locals body => decodeScopedFuel? F fuel locals body)
    (renameScopedFuel? f fuel) bodySuccess locals next valid bound parsed body value decoded
  have bodyRename : renameScopedFuel? f fuel
      ((binderScope next parsed).reverse ++ localScope locals) (next + (head :: rest).length) body = some output := by
    simpa only [parsedLengths] using renamedBody
  cases bindings with
  | nil => simp at lengths
  | cons targetHead targetRest =>
    cases universal with
    | false =>
      refine ⟨.list [.atom "exists", .list (targetHead :: targetRest), output], ?_, ?_⟩
      · change (renameBinders? E next (head :: rest)).bind _ = _
        rw [renamedBinders]
        change (renameScopedFuel? f fuel _ _ body).bind _ = _
        rw [bodyRename]
        rfl
      · change (binders? F (targetHead :: targetRest)).bind _ = _
        rw [targetBinders]
        exact mappedBody
    | true =>
      refine ⟨.list [.atom "forall", .list (targetHead :: targetRest), output], ?_, ?_⟩
      · change (renameBinders? E next (head :: rest)).bind _ = _
        rw [renamedBinders]
        change (renameScopedFuel? f fuel _ _ body).bind _ = _
        rw [bodyRename]
        rfl
      · change (binders? F (targetHead :: targetRest)).bind _ = _
        rw [targetBinders]
        exact mappedBody

end Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
