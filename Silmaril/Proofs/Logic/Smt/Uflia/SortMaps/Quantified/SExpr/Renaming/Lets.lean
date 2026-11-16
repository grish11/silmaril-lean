module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Names.Thms

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
open CategoryTheory
open Uflia.SExpr (Environment Expr simpleSymbol reserved)
open Uflia.Quantified.SExpr
variable {E F : Environment} {k : Nat} {Γ : Fin k → SortCode String}

/-- Complete original RHS values are paired with fresh target spellings. -/
def namedLetLocals : Nat → Uflia.Quantified.SExpr.Locals E Γ → List (Local E Γ)
  | _, [] => []
  | next, (name, value) :: rest => ⟨name, freshName next, value⟩ :: namedLetLocals (next + 1) rest

@[simp] theorem sourceLocals_namedLet (next : Nat) (values : Uflia.Quantified.SExpr.Locals E Γ) :
    sourceLocals (namedLetLocals next values) = values := by
  induction values generalizing next with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨name, value⟩
    simp only [namedLetLocals, sourceLocals, List.map_cons]
    exact congrArg (List.cons (name, value)) (ih (next + 1))

@[simp] theorem sourceLocals_append (xs ys : List (Local E Γ)) :
    sourceLocals (xs ++ ys) = sourceLocals xs ++ sourceLocals ys := List.map_append
@[simp] theorem targetLocals_append (f : environmentSignature E ⟶ environmentSignature F) (xs ys : List (Local E Γ)) :
    targetLocals f (xs ++ ys) = targetLocals f xs ++ targetLocals f ys := List.map_append
@[simp] theorem localScope_append (xs ys : List (Local E Γ)) :
    localScope (xs ++ ys) = localScope xs ++ localScope ys := List.map_append

theorem valid_perm {next : Nat} {xs ys : List (Local E Γ)}
    (valid : ValidScope F next xs) (permutation : xs.Perm ys) : ValidScope F next ys := by
  rcases valid with ⟨distinct, short, away, legal⟩
  refine ⟨(permutation.map Local.target).nodup_iff.mp distinct, ?_, ?_, ?_⟩
  · intro entry member
    exact short entry (permutation.mem_iff.mpr member)
  · intro entry member declaration declared
    exact away entry (permutation.mem_iff.mpr member) declaration declared
  · intro entry member
    exact legal entry (permutation.mem_iff.mpr member)

/-- Allocate the entire parallel-let list without changing its source order.
The proof can allocate head first and permute the resulting scope validity. -/
theorem namedLetLocals_valid (F : Environment) (values : Uflia.Quantified.SExpr.Locals E Γ)
    (next : Nat) (locals : List (Local E Γ)) (valid : ValidScope F next locals)
    (bound : firstFresh F ≤ next) :
    ValidScope F (next + values.length) (namedLetLocals next values ++ locals) := by
  induction values generalizing next locals with
  | nil => simpa only [namedLetLocals, List.length_nil, Nat.add_zero, List.nil_append] using valid
  | cons pair rest ih =>
    rcases pair with ⟨name, value⟩
    have headValid := valid_fresh_cons F next locals valid bound name value
    have tailValid := ih (next + 1) (⟨name, freshName next, value⟩ :: locals)
      headValid (by omega)
    have reordered := valid_perm tailValid (List.perm_middle (a := (⟨name, freshName next, value⟩ : Local E Γ)))
    simpa only [namedLetLocals, List.length_cons, List.cons_append,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using reordered

/-- Original source names, used for the duplicate-name check, are unchanged by
recording their fresh target names. -/
@[simp] theorem namedLetLocals_source_any (next : Nat) (values : Uflia.Quantified.SExpr.Locals E Γ) (name : String) :
    (localScope (namedLetLocals next values)).any (fun pair => pair.1 == name) =
      values.any (fun pair => pair.1 == name) := by
  induction values generalizing next with
  | nil => rfl
  | cons pair rest ih =>
    rcases pair with ⟨key, value⟩
    change (key == name || (localScope (namedLetLocals (next + 1) rest)).any
      (fun pair => pair.1 == name)) = (key == name || rest.any (fun pair => pair.1 == name))
    rw [ih]

theorem target_names_any_false (f : environmentSignature E ⟶ environmentSignature F) (locals : List (Local E Γ))
    (name : String) (absent : name ∉ locals.map Local.target) :
    (targetLocals f locals).any (fun pair => pair.1 == name) = false := by
  apply List.any_eq_false.mpr
  intro pair member
  obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp member
  subst pair
  intro same
  apply absent
  exact List.mem_map.mpr ⟨entry, entryMember, beq_iff_eq.mp same⟩

/-- Every RHS uses the same old recursive oracle. The target body locals retain
exactly the mapped source RHS values, in the original binding-list order. -/
theorem renameBindings_success (f : NameMap E F)
    (source : Expr → Option (PackedTerm E Γ)) (target : Expr → Option (PackedTerm F (f.abstract.sorts ∘ Γ)))
    (rename : Expr → Option Expr)
    (children : ∀ e value, source e = some value → ∃ output,
      rename e = some output ∧ target output = some (mapPacked f.abstract value))
    (bindings : List Expr) (values : Uflia.Quantified.SExpr.Locals E Γ)
    (decoded : letBindings? source bindings = some values) (next : Nat)
    (bound : firstFresh F ≤ next) :
    ∃ output, renameBindings? rename next bindings = some (output, localScope (namedLetLocals next values)) ∧
      letBindings? target output = some (targetLocals f.abstract (namedLetLocals next values)) ∧
      values.length = bindings.length ∧ output.length = bindings.length := by
  induction bindings generalizing next values with
  | nil =>
    cases decoded
    exact ⟨[], rfl, rfl, rfl, rfl⟩
  | cons binding rest ih =>
    cases binding with
    | atom name => simp [letBindings?] at decoded
    | list parts =>
      cases parts with
      | nil => simp [letBindings?] at decoded
      | cons first parts =>
        cases first with
        | list xs => simp [letBindings?] at decoded
        | atom name =>
          cases parts with
          | nil => simp [letBindings?] at decoded
          | cons rhs parts =>
            cases parts with
            | cons extra parts => simp [letBindings?] at decoded
            | nil =>
              have checks : simpleSymbol name = true ∧ reserved.contains name = false := by
                cases hs : simpleSymbol name <;> cases hr : reserved.contains name <;>
                  simp_all [letBindings?]
              simp only [letBindings?, checks.1, checks.2, Bool.not_true, Bool.false_or,
                Bool.false_eq_true, ↓reduceIte] at decoded
              change (source rhs).bind _ = some values at decoded
              obtain ⟨value, hv, decoded⟩ := Option.bind_eq_some_iff.mp decoded
              change (letBindings? source rest).bind _ = some values at decoded
              obtain ⟨tail, ht, decoded⟩ := Option.bind_eq_some_iff.mp decoded
              have noDuplicate : tail.any (fun pair => pair.1 == name) = false := by
                cases hd : tail.any (fun pair => pair.1 == name) <;> simp_all
              simp only [noDuplicate, Bool.false_eq_true, ↓reduceIte] at decoded
              have same : (name, value) :: tail = values := Option.some.inj decoded
              subst values
              obtain ⟨rhsOutput, renamedRhs, mappedRhs⟩ := children rhs value hv
              obtain ⟨output, renamedTail, mappedTail, lengths, outputLengths⟩ := ih tail ht (next + 1) (by omega)
              have distinct := (namedLetLocals_valid F ((name, value) :: tail) next []
                (by simp [ValidScope]) bound).1
              simp only [namedLetLocals, List.append_nil, List.map_cons, List.nodup_cons] at distinct
              have noTargetDuplicate := target_names_any_false f.abstract
                (namedLetLocals (next + 1) tail) (freshName next) distinct.1
              refine ⟨.list [.atom (freshName next), rhsOutput] :: output, ?_, ?_, ?_, ?_⟩
              · simp only [renameBindings?, Uflia.Quantified.SExpr.Renaming.renameBindings?,
                  checks.1, checks.2, Bool.not_true, Bool.false_or,
                  Bool.false_eq_true, ↓reduceIte, renamedRhs, renamedTail]
                change (if (localScope (namedLetLocals (next + 1) tail)).any
                    (fun pair => pair.1 == name) then none else some
                    (.list [.atom (freshName next), rhsOutput] :: output,
                      (name, freshName next) :: localScope (namedLetLocals (next + 1) tail))) = _
                rw [namedLetLocals_source_any, noDuplicate]
                rfl
              · simp only [letBindings?, freshName_simple, freshName_not_reserved, Bool.not_true,
                  Bool.false_or, Bool.false_eq_true, ↓reduceIte, mappedRhs,
                  mappedTail]
                change (if (targetLocals f.abstract (namedLetLocals (next + 1) tail)).any
                    (fun pair => pair.1 == freshName next) then none else some
                    ((freshName next, mapPacked f.abstract value) ::
                      targetLocals f.abstract (namedLetLocals (next + 1) tail))) = _
                rw [noTargetDuplicate]
                rfl
              · simp only [List.length_cons, lengths]
              · simp only [List.length_cons, outputLengths]

/-- Parallel RHSs are transported in the old scope; only the body receives
the completed fresh local list, retaining every captured typed RHS value. -/
theorem renameLet_success (f : NameMap E F) (fuel : Nat)
    (bodySuccess : ∀ (locals : List (Local E Γ)) (next : Nat),
      ValidScope F next locals → firstFresh F ≤ next →
      ∀ body value, decodeScopedFuel? E fuel (sourceLocals locals) body = some value → ∃ output,
        renameScopedFuel? f fuel (localScope locals) next body = some output ∧
          decodeScopedFuel? F fuel (targetLocals f.abstract locals) output = some (mapPacked f.abstract value))
    (locals : List (Local E Γ)) (next : Nat)
    (valid : ValidScope F next locals) (bound : firstFresh F ≤ next)
    (head : Expr) (rest : List Expr) (values : Uflia.Quantified.SExpr.Locals E Γ)
    (decodedBindings : letBindings? (decodeScopedFuel? E fuel (sourceLocals locals))
      (head :: rest) = some values)
    (body : Expr) (value : PackedTerm E Γ)
    (decodedBody : decodeScopedFuel? E fuel (values ++ sourceLocals locals) body = some value) :
    ∃ output, renameScopedFuel? f (fuel + 1) (localScope locals) next
        (.list [.atom "let", .list (head :: rest), body]) = some output ∧
      decodeScopedFuel? F (fuel + 1) (targetLocals f.abstract locals) output =
        some (mapPacked f.abstract value) := by
  obtain ⟨bindings, renamedBindings, targetBindings, lengths, outputLengths⟩ :=
    renameBindings_success f (decodeScopedFuel? E fuel (sourceLocals locals))
      (decodeScopedFuel? F fuel (targetLocals f.abstract locals))
      (renameScopedFuel? f fuel (localScope locals) next)
      (bodySuccess locals next valid bound) (head :: rest) values decodedBindings next bound
  have bodyDecoded : decodeScopedFuel? E fuel
      (sourceLocals (namedLetLocals next values ++ locals)) body = some value := by
    simpa only [sourceLocals_append, sourceLocals_namedLet] using decodedBody
  obtain ⟨output, renamedBody, targetBody⟩ := bodySuccess
    (namedLetLocals next values ++ locals) (next + values.length)
    (namedLetLocals_valid F values next locals valid bound) (by omega) body value bodyDecoded
  have bodyRename : renameScopedFuel? f fuel
      (localScope (namedLetLocals next values) ++ localScope locals)
      (next + (head :: rest).length) body = some output := by
    simpa only [localScope_append, lengths] using renamedBody
  cases bindings with
  | nil => simp at outputLengths
  | cons targetHead targetRest =>
    refine ⟨.list [.atom "let", .list (targetHead :: targetRest), output], ?_, ?_⟩
    · change (renameBindings? (renameScopedFuel? f fuel (localScope locals) next) next (head :: rest)).bind _ = _
      rw [renamedBindings]
      change (renameScopedFuel? f fuel _ _ body).bind _ = _
      rw [bodyRename]
      rfl
    · change (letBindings? (decodeScopedFuel? F fuel (targetLocals f.abstract locals))
        (targetHead :: targetRest)).bind _ = _
      rw [targetBindings]
      simpa only [Option.bind_some, targetLocals_append] using targetBody

end Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
