module

public import Silmaril.Logic.Smt.Uflia.SortMaps.SExpr.Renaming.Category.Defs
public import Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.Thms
public import Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming.Defs

/-! Actual source rewriting across varying sorts. The map records name/profile
coherence and admission of mapped binder sorts, never decoder commutation. -/
@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
open CategoryTheory
open Silmaril.Logic.Smt.Uflia.SExpr
open Silmaril.Logic.Smt.Uflia.Quantified.SExpr

abbrev environmentSignature := SortMaps.SExpr.Renaming.environmentSignature

/-- Canonical atomic syntax for the ground sorts admitted by this decoder. -/
def sortExpr : SortCode String → Expr
  | .bool => .atom "Bool"
  | .int => .atom "Int"
  | .user name => .atom name

/-- An unused binder sort still needs a target declaration when its image is a
user sort. This is a sort-admission condition, separate from term decoding. -/
structure NameMap (E F : Environment) extends SortMaps.SExpr.Renaming.NameMap E F where
  sorts : ∀ expression sort, E.sort? expression = some sort →
    F.sort? (sortExpr (abstract.sorts sort)) = some (abstract.sorts sort)

abbrev freshName := Uflia.Quantified.SExpr.Renaming.freshName
abbrev Scope := Uflia.Quantified.SExpr.Renaming.Scope
abbrev localName? := Uflia.Quantified.SExpr.Renaming.localName?
abbrev firstFresh := Uflia.Quantified.SExpr.Renaming.firstFresh
abbrev renameBindings? := Uflia.Quantified.SExpr.Renaming.renameBindings?

/-- Parse each original sort, emit its actual image, and retain source order.
Repeated quantifier names remain legal and are resolved by lexical shadowing. -/
def renameBinders? {E F : Environment} (f : NameMap E F) :
    Nat → List Expr → Option (List Expr × Scope)
  | _, [] => some ([], [])
  | next, .list [.atom name, sort] :: rest => do
      if !simpleSymbol name || reserved.contains name then none else do
        let sourceSort ← E.sort? sort
        let (bindings, scope) ← renameBinders? f (next + 1) rest
        pure (.list [.atom (freshName next), sortExpr (f.abstract.sorts sourceSort)] :: bindings,
          (name, freshName next) :: scope)
  | _, _ => none

/-- Preserve constructors and parallel-let scope while changing global names,
quantifier sorts and fresh lexical names. The source decoder is admission. -/
def renameScopedFuel? {E F : Environment} (f : NameMap E F) :
    Nat → Scope → Nat → Expr → Option Expr
  | 0, _, _, _ => none
  | fuel + 1, scope, next, expression =>
      let recur := renameScopedFuel? f fuel scope next
      match expression with
      | .atom "true" => some (.atom "true")
      | .atom "false" => some (.atom "false")
      | .atom name =>
          match localName? scope name with
          | some target => some (.atom target)
          | none => match numeral? expression with
            | some _ => some expression
            | none => do
                let _ ← lookup? E name
                pure (.atom (f.rename name))
      | .list [.atom "forall", .list bindings@(_ :: _), body] => do
          let (bindings', added) ← renameBinders? f next bindings
          let body' ← renameScopedFuel? f fuel (added.reverse ++ scope)
            (next + bindings.length) body
          pure (.list [.atom "forall", .list bindings', body'])
      | .list [.atom "exists", .list bindings@(_ :: _), body] => do
          let (bindings', added) ← renameBinders? f next bindings
          let body' ← renameScopedFuel? f fuel (added.reverse ++ scope)
            (next + bindings.length) body
          pure (.list [.atom "exists", .list bindings', body'])
      | .list [.atom "let", .list bindings@(_ :: _), body] => do
          let (bindings', added) ← renameBindings? recur next bindings
          let body' ← renameScopedFuel? f fuel (added ++ scope)
            (next + bindings.length) body
          pure (.list [.atom "let", .list bindings', body'])
      | .list (.atom name :: arguments) => do
          if reserved.contains name then
            let arguments ← arguments.mapM recur
            pure (.list (.atom name :: arguments))
          else if arguments.isEmpty || (localName? scope name).isSome then none else do
            let _ ← lookup? E name
            let arguments ← arguments.mapM recur
            pure (.list (.atom (f.rename name) :: arguments))
      | _ => none

def rename? {E F : Environment} (f : NameMap E F) (expression : Expr) : Option Expr :=
  renameScopedFuel? f (expressionFuel expression) [] (firstFresh F) expression

/-- Open packed transport changes both the context and computed sort. -/
def mapPacked {E F : Environment}
    (f : environmentSignature E ⟶ environmentSignature F)
    {k : Nat} {Γ : Fin k → SortCode String}
    (value : Uflia.Quantified.SExpr.PackedTerm E Γ) :
    Uflia.Quantified.SExpr.PackedTerm F (f.sorts ∘ Γ) :=
  ⟨f.sorts value.sort, Hom.quantifiedTerm f value.term⟩

end Silmaril.Logic.Smt.Uflia.SortMaps.Quantified.SExpr.Renaming
