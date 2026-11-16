module

public import Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming.Defs
public import Batteries.Data.List.Lemmas

/-! Successful concrete renaming preserves the complete syntax node count.
No source-decoder success or legality assumption is needed. -/
@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
open Silmaril.Logic.Smt.Uflia.SExpr
variable {E F : Environment}

/-- Fresh binder atoms replace atoms; their original sort syntax is unchanged. -/
theorem renameBinders_fuel (next : Nat) (bindings renamed : List Expr) (scope : Scope)
    (success : renameBinders? E next bindings = some (renamed, scope)) :
    expressionsFuel renamed = expressionsFuel bindings := by
  induction bindings generalizing next renamed scope with
  | nil =>
    simp only [renameBinders?] at success
    cases success
    rfl
  | cons binding rest ih =>
    unfold renameBinders? at success
    split at success
    · contradiction
    · rename_i allocation next input name sort tail same
      obtain ⟨hb, hr⟩ : binding = .list [.atom name, sort] ∧ rest = tail := List.cons.inj same
      subst binding
      subst tail
      split at success
      · contradiction
      · change (E.sort? sort).bind _ = some (renamed, scope) at success
        obtain ⟨sortCode, hsort, success⟩ := Option.bind_eq_some_iff.mp success
        change (renameBinders? E (allocation + 1) rest).bind _ = some (renamed, scope) at success
        obtain ⟨pair, hrest, success⟩ := Option.bind_eq_some_iff.mp success
        rcases pair with ⟨renamedRest, scopeRest⟩
        cases success
        simp only [expressionsFuel, expressionFuel, ih (allocation + 1) renamedRest scopeRest hrest]
    · contradiction

/-- Parallel RHS renaming preserves the binding-list node count whenever its
single old-scope recursion preserves each successful RHS node count. -/
theorem renameBindings_fuel (recur : Expr → Option Expr)
    (recurFuel : ∀ expression output, recur expression = some output →
      expressionFuel output = expressionFuel expression)
    (next : Nat) (bindings renamed : List Expr) (scope : Scope)
    (success : renameBindings? recur next bindings = some (renamed, scope)) :
    expressionsFuel renamed = expressionsFuel bindings := by
  induction bindings generalizing next renamed scope with
  | nil =>
    simp only [renameBindings?] at success
    cases success
    rfl
  | cons binding rest ih =>
    unfold renameBindings? at success
    split at success
    · contradiction
    · rename_i allocation next input name value tail same
      obtain ⟨hb, hr⟩ : binding = .list [.atom name, value] ∧ rest = tail := List.cons.inj same
      subst binding
      subst tail
      split at success
      · contradiction
      · change (recur value).bind _ = some (renamed, scope) at success
        obtain ⟨output, houtput, success⟩ := Option.bind_eq_some_iff.mp success
        change (renameBindings? recur (allocation + 1) rest).bind _ = some (renamed, scope) at success
        obtain ⟨pair, hrest, success⟩ := Option.bind_eq_some_iff.mp success
        rcases pair with ⟨renamedRest, scopeRest⟩
        change (if scopeRest.any (fun pair => pair.1 == name) then none
          else some (.list [.atom (freshName allocation), output] :: renamedRest,
            (name, freshName allocation) :: scopeRest)) = some (renamed, scope) at success
        split at success
        · contradiction
        · cases success
          simp only [expressionsFuel, expressionFuel, recurFuel value output houtput,
            ih (allocation + 1) renamedRest scopeRest hrest]
    · contradiction

/-- Sequencing preserves the sum of syntax-node counts. -/
theorem mapM_rename_fuel (recur : Expr → Option Expr)
    (recurFuel : ∀ expression output, recur expression = some output →
      expressionFuel output = expressionFuel expression)
    (inputs outputs : List Expr) (success : inputs.mapM recur = some outputs) :
    expressionsFuel outputs = expressionsFuel inputs := by
  have related := List.mapM_eq_some_iff_forall₂.mp success
  clear success
  induction related with
  | nil => rfl
  | cons head tail ih =>
    simp only [expressionsFuel, recurFuel _ _ head, ih]

/-- Every successful branch of the full quantified renamer retains node count,
including all quantifier blocks, parallel lets and arbitrary applications. -/
theorem renameScopedFuel_fuel (f : NameMap E F) (fuel : Nat) (scope : Scope) (next : Nat)
    (expression output : Expr)
    (success : renameScopedFuel? f fuel scope next expression = some output) :
    expressionFuel output = expressionFuel expression := by
  induction fuel generalizing scope next expression output with
  | zero => simp [renameScopedFuel?] at success
  | succ fuel ih =>
    unfold renameScopedFuel? at success
    split at success
    · cases success
      rfl
    · cases success
      rfl
    · rename_i name htrue hfalse
      cases found : localName? scope name with
      | some target =>
        simp only [found] at success
        cases success
        rfl
      | none =>
        simp only [found] at success
        split at success
        · cases success
          rfl
        · change (lookup? E name).bind _ = some output at success
          obtain ⟨index, hindex, success⟩ := Option.bind_eq_some_iff.mp success
          cases success
          rfl
    · rename_i head bindings body
      change (renameBinders? E next (head :: bindings)).bind _ = some output at success
      obtain ⟨pair, hbinders, success⟩ := Option.bind_eq_some_iff.mp success
      rcases pair with ⟨renamed, added⟩
      change (renameScopedFuel? f fuel (added.reverse ++ scope)
        (next + (head :: bindings).length) body).bind _ = some output at success
      obtain ⟨bodyOutput, hbody, success⟩ := Option.bind_eq_some_iff.mp success
      cases success
      have bindersFuel := renameBinders_fuel next (head :: bindings) renamed added hbinders
      have bodyFuel := ih _ _ body bodyOutput hbody
      simp only [expressionFuel, expressionsFuel, bindersFuel, bodyFuel]
    · rename_i head bindings body
      change (renameBinders? E next (head :: bindings)).bind _ = some output at success
      obtain ⟨pair, hbinders, success⟩ := Option.bind_eq_some_iff.mp success
      rcases pair with ⟨renamed, added⟩
      change (renameScopedFuel? f fuel (added.reverse ++ scope)
        (next + (head :: bindings).length) body).bind _ = some output at success
      obtain ⟨bodyOutput, hbody, success⟩ := Option.bind_eq_some_iff.mp success
      cases success
      have bindersFuel := renameBinders_fuel next (head :: bindings) renamed added hbinders
      have bodyFuel := ih _ _ body bodyOutput hbody
      simp only [expressionFuel, expressionsFuel, bindersFuel, bodyFuel]
    · rename_i head bindings body
      change (renameBindings? (renameScopedFuel? f fuel scope next) next (head :: bindings)).bind _ =
        some output at success
      obtain ⟨pair, hbindings, success⟩ := Option.bind_eq_some_iff.mp success
      rcases pair with ⟨renamed, added⟩
      change (renameScopedFuel? f fuel (added ++ scope)
        (next + (head :: bindings).length) body).bind _ = some output at success
      obtain ⟨bodyOutput, hbody, success⟩ := Option.bind_eq_some_iff.mp success
      cases success
      have bindingsFuel := renameBindings_fuel _ (fun e out result => ih scope next e out result)
        next (head :: bindings) renamed added hbindings
      have bodyFuel := ih _ _ body bodyOutput hbody
      simp only [expressionFuel, expressionsFuel, bindingsFuel, bodyFuel]
    · rename_i name arguments hforall hexists hlet
      split at success
      · change (arguments.mapM (renameScopedFuel? f fuel scope next)).bind _ = some output at success
        obtain ⟨outputs, houtputs, success⟩ := Option.bind_eq_some_iff.mp success
        cases success
        have argumentsFuel := mapM_rename_fuel _ (fun e out result => ih scope next e out result)
          arguments outputs houtputs
        simp only [expressionFuel, expressionsFuel, argumentsFuel]
      · split at success
        · contradiction
        · change (lookup? E name).bind _ = some output at success
          obtain ⟨index, hindex, success⟩ := Option.bind_eq_some_iff.mp success
          change (arguments.mapM (renameScopedFuel? f fuel scope next)).bind _ = some output at success
          obtain ⟨outputs, houtputs, success⟩ := Option.bind_eq_some_iff.mp success
          cases success
          have argumentsFuel := mapM_rename_fuel _ (fun e out result => ih scope next e out result)
            arguments outputs houtputs
          simp only [expressionFuel, expressionsFuel, argumentsFuel]
    · contradiction

/-- The executable closed entry preserves its default decoder fuel exactly. -/
theorem rename_fuel (f : NameMap E F) (expression output : Expr)
    (success : rename? f expression = some output) :
    expressionFuel output = expressionFuel expression :=
  renameScopedFuel_fuel f (expressionFuel expression) [] (firstFresh F) expression output success

end Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
