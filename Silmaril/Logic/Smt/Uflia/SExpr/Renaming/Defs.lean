module

public import Silmaril.Logic.Smt.Uflia.SExpr.Thms

/-! Executable lexical normalization for concrete symbol renaming. Local bindings
are substituted after their right-hand sides are normalized in the outer scope.
This removes binders before inserting their values, avoiding name capture even
when distinct global symbols are identified. The institution presentation and
full decoder commutation theorem are developed separately. -/

@[expose] public section

namespace Silmaril.Logic.Smt.Uflia.SExpr.Renaming

open CategoryTheory

/-- The actual target declaration behind a typed symbol. -/
def symbolIndex {E : Environment} : {n : Nat} → {inputs : Fin n → SortCode String} →
    {output : SortCode String} → Symbol E n inputs output → Fin E.declarations.length
  | _, _, _, .declared i => i

/-- A concrete name map is compatible with an actual abstract signature map.
Lookup coherence concerns declaration lookup only, not decoder commutation.
No injectivity condition is imposed: equal-profile symbols may be identified. -/
structure NameMap (E F : Environment) where
  rename : String → String
  abstract : E.signature ⟶ F.signature
  lookup : ∀ (name : String) (i : Fin E.declarations.length),
    lookup? E name = some i →
    lookup? F (rename name) = some (symbolIndex (abstract.operations (.declared i)))
  targetName : ∀ (name : String) (i : Fin E.declarations.length),
    lookup? E name = some i →
    (F.declarations.get (symbolIndex (abstract.operations (.declared i)))).name = rename name

/-- Transport the computed sort together with the abstract term. -/
def mapPacked {E F : Environment} (f : E.signature ⟶ F.signature)
    (t : PackedTerm E) : PackedTerm F :=
  ⟨t.sort, Uflia.Term.map f t.term⟩

abbrev SyntaxLocals := List (String × Expr)

def syntaxLocal? : SyntaxLocals → String → Option Expr
  | [], _ => none
  | (name, value) :: rest, key =>
      if name = key then some value else syntaxLocal? rest key

/-- Parallel bindings use the caller's recursion function, hence its old scope.
The checks mirror `letBindings?`, including duplicate names. -/
def syntaxBindings? (recur : Expr → Option Expr) : List Expr → Option SyntaxLocals
  | [] => some []
  | .list [.atom name, value] :: rest => do
      if !simpleSymbol name || reserved.contains name then none else do
        let value ← recur value
        let values ← syntaxBindings? recur rest
        if values.any (fun pair => pair.1 == name) then none
        else pure ((name, value) :: values)
  | _ => none

/-- Rename only names looked up as actual source declarations. Built-in names,
numerals and other atoms are not rewritten by a global symbol map. -/
def globalName (E : Environment) (rename : String → String) (name : String) : String :=
  match lookup? E name with
  | some _ => rename name
  | none => name

/-- Normalize full lexical `let` syntax and rename free declared symbols.
Fuel bounds recursion through the source, not the potentially larger substituted
output. No output-size cap or parser-admission change is introduced here. -/
def normalizeFuel? (E : Environment) (rename : String → String) :
    Nat → SyntaxLocals → Expr → Option Expr
  | 0, _, _ => none
  | fuel + 1, locals, expression =>
      let recur := normalizeFuel? E rename fuel locals
      match expression with
      | .atom "true" => some (.atom "true")
      | .atom "false" => some (.atom "false")
      | .atom name =>
          match syntaxLocal? locals name with
          | some value => some value
          | none =>
              match numeral? expression with
              | some _ => some expression
              | none => some (.atom (globalName E rename name))
      | .list [.atom "let", .list bindings@(_ :: _), body] => do
          let values ← syntaxBindings? recur bindings
          normalizeFuel? E rename fuel (values ++ locals) body
      | .list (.atom name :: arguments) => do
          -- A lexical scalar blocks UF application, including nullary syntax.
          if (syntaxLocal? locals name).isSome then none else do
            let arguments ← arguments.mapM recur
            pure (.list (.atom (globalName E rename name) :: arguments))
      | _ => none

/-- The default source-node budget is independent of substitution expansion. -/
def normalize? (E : Environment) (rename : String → String) (expression : Expr) :
    Option Expr :=
  normalizeFuel? E rename (expressionFuel expression) [] expression

end Silmaril.Logic.Smt.Uflia.SExpr.Renaming
