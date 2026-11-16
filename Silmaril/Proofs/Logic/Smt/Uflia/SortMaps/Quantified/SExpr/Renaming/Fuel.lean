module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming.Defs
public import Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming.Thms
public import Batteries.Data.List.Lemmas

/-! Successful concrete renaming preserves the complete syntax node count.
No source-decoder success or legality assumption is needed. -/
@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
open Silmaril.Logic.Smt.Uflia.SExpr
variable {E F : Environment}

private theorem sortExpr_fuel (s : SortCode String) : expressionFuel (sortExpr s) = 1 := by
  cases s <;> rfl

private theorem mapped_sort_fuel (f : NameMap E F) (expression : Expr) (sort : SortCode String)
    (decoded : E.sort? expression = some sort) :
    expressionFuel (sortExpr (f.abstract.sorts sort)) = expressionFuel expression := by
  cases expression with
  | atom name => exact sortExpr_fuel _
  | list children => simp [Environment.sort?] at decoded

/-- Source sorts parse as atoms, and every mapped sort is rendered as an atom. -/
theorem renameBinders_fuel (f : NameMap E F) (next : Nat) (bindings renamed : List Expr) (scope : Scope)
    (success : renameBinders? f next bindings = some (renamed, scope)) :
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
        change (renameBinders? f (allocation + 1) rest).bind _ = some (renamed, scope) at success
        obtain ⟨pair, hrest, success⟩ := Option.bind_eq_some_iff.mp success
        rcases pair with ⟨renamedRest, scopeRest⟩
        cases success
        simp only [expressionsFuel, expressionFuel, mapped_sort_fuel f sort sortCode hsort,
          ih (allocation + 1) renamedRest scopeRest hrest]
    · contradiction

private abbrev renameBindings_fuel :=
  Uflia.Quantified.SExpr.Renaming.renameBindings_fuel
private abbrev mapM_rename_fuel :=
  Uflia.Quantified.SExpr.Renaming.mapM_rename_fuel

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
      change (renameBinders? f next (head :: bindings)).bind _ = some output at success
      obtain ⟨pair, hbinders, success⟩ := Option.bind_eq_some_iff.mp success
      rcases pair with ⟨renamed, added⟩
      change (renameScopedFuel? f fuel (added.reverse ++ scope)
        (next + (head :: bindings).length) body).bind _ = some output at success
      obtain ⟨bodyOutput, hbody, success⟩ := Option.bind_eq_some_iff.mp success
      cases success
      have bindersFuel := renameBinders_fuel f next (head :: bindings) renamed added hbinders
      have bodyFuel := ih _ _ body bodyOutput hbody
      simp only [expressionFuel, expressionsFuel, bindersFuel, bodyFuel]
    · rename_i head bindings body
      change (renameBinders? f next (head :: bindings)).bind _ = some output at success
      obtain ⟨pair, hbinders, success⟩ := Option.bind_eq_some_iff.mp success
      rcases pair with ⟨renamed, added⟩
      change (renameScopedFuel? f fuel (added.reverse ++ scope)
        (next + (head :: bindings).length) body).bind _ = some output at success
      obtain ⟨bodyOutput, hbody, success⟩ := Option.bind_eq_some_iff.mp success
      cases success
      have bindersFuel := renameBinders_fuel f next (head :: bindings) renamed added hbinders
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

end Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
