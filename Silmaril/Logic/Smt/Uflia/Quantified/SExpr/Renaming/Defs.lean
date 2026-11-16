module

public import Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Surface.Thms
public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Category.Thms

/-! Capture-safe concrete renaming preserves the complete source constructor tree,
including parallel lets. Binder names are freshened before global names change.
The source decoder remains the admission contract. -/
@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
open CategoryTheory
open Silmaril.Logic.Smt.Uflia.SExpr

/-- Global maps must also retain source binder-sort admission. The ground
NameMap alone cannot ensure this for a user sort unused by any operation. -/
structure NameMap (E F : Environment) extends Uflia.SExpr.Renaming.NameMap E F where
  sorts : ∀ expression sort, E.sort? expression = some sort → F.sort? expression = some sort

namespace NameMap
variable {E F G H : Environment}

@[ext] theorem ext (f g : NameMap E F) (h : f.toNameMap = g.toNameMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

def id (E : Environment) : NameMap E E :=
  ⟨Uflia.SExpr.Renaming.NameMap.id E, fun _ _ h => h⟩

def comp (f : NameMap E F) (g : NameMap F G) : NameMap E G :=
  ⟨f.toNameMap.comp g.toNameMap, fun e s h => g.sorts e s (f.sorts e s h)⟩

@[simp] theorem id_comp (f : NameMap E F) : (id E).comp f = f := by
  apply ext
  exact Uflia.SExpr.Renaming.NameMap.id_comp f.toNameMap

@[simp] theorem comp_id (f : NameMap E F) : f.comp (id F) = f := by
  apply ext
  exact Uflia.SExpr.Renaming.NameMap.comp_id f.toNameMap

theorem assoc (f : NameMap E F) (g : NameMap F G) (h : NameMap G H) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  apply ext
  exact Uflia.SExpr.Renaming.NameMap.assoc f.toNameMap g.toNameMap h.toNameMap
end NameMap

/-- An explicit environment, with all sort-admission-preserving coherent name maps. -/
structure EnvironmentSignature where
  environment : Environment

instance : Category EnvironmentSignature where
  Hom E F := NameMap E.environment F.environment
  id E := NameMap.id E.environment
  comp := NameMap.comp
  id_comp := NameMap.id_comp
  comp_id := NameMap.comp_id
  assoc := NameMap.assoc

def environmentFunctor : EnvironmentSignature ⥤ Uflia.Signature String where
  obj E := E.environment.signature
  map f := f.abstract
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Dollar followed by underscores is a legal simple symbol for every length. -/
def freshName (index : Nat) : String := String.ofList ('$' :: List.replicate index '_')

abbrev Scope := List (String × String)

def localName? : Scope → String → Option String
  | [], _ => none
  | (source, target) :: rest, name =>
      if source = name then some target else localName? rest name

/-- Fresh names start longer than every target declaration name. Subsequent
binders increase the index, so they cannot capture earlier target locals. -/
def firstFresh (F : Environment) : Nat :=
  F.declarations.foldl (fun bound declaration => max bound declaration.name.length) 0 + 1

/-- Preserve the original sort expression; target sort admission is guaranteed
by NameMap.sorts. Pairs remain in source order, before quantifier reversal. -/
def renameBinders? (E : Environment) : Nat → List Expr → Option (List Expr × Scope)
  | _, [] => some ([], [])
  | next, .list [.atom name, sort] :: rest => do
      if !simpleSymbol name || reserved.contains name then none else do
        let _ ← E.sort? sort
        let (bindings, scope) ← renameBinders? E (next + 1) rest
        pure (.list [.atom (freshName next), sort] :: bindings,
          (name, freshName next) :: scope)
  | _, _ => none

/-- All RHSs use the same old lexical scope. Check ORIGINAL duplicate names;
freshening is not allowed to make a rejected parallel let admissible. -/
def renameBindings? (recur : Expr → Option Expr) :
    Nat → List Expr → Option (List Expr × Scope)
  | _, [] => some ([], [])
  | next, .list [.atom name, value] :: rest => do
      if !simpleSymbol name || reserved.contains name then none else do
        let value ← recur value
        let (bindings, scope) ← renameBindings? recur (next + 1) rest
        if scope.any (fun pair => pair.1 == name) then none else
          pure (.list [.atom (freshName next), value] :: bindings,
            (name, freshName next) :: scope)
  | _, _ => none

/-- This traverses source syntax, not decoded terms. Quantifier scopes nest in
binder-list order; let RHSs remain parallel. Disjoint child scopes may reuse the
same fresh supply, since their bound names are never in scope in each other. -/
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
          let (bindings', added) ← renameBinders? E next bindings
          let body' ← renameScopedFuel? f fuel (added.reverse ++ scope)
            (next + bindings.length) body
          pure (.list [.atom "forall", .list bindings', body'])
      | .list [.atom "exists", .list bindings@(_ :: _), body] => do
          let (bindings', added) ← renameBinders? E next bindings
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

/-- Quantified packed terms retain the computed sort under a signature map. -/
def mapPacked {E F : Environment} (f : E.signature ⟶ F.signature)
    {k : Nat} {Γ : Fin k → SortCode String} (term : PackedTerm E Γ) : PackedTerm F Γ :=
  ⟨term.sort, term.term.map f⟩

end Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
