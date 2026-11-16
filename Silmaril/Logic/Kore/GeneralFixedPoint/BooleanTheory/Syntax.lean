module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Predicates.Defs

/-! Whole ordinary Boolean theory input: one declared value sort, homogeneous
ordinary symbols with retained constructor/functional metadata, monomorphic
value axioms, and one-variable result-sort-parametric predicate schemes. -/
@[expose] public section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.BooleanTheory
open Operational.Text

inductive RawPredicate where
  | top | bottom
  | equal (sort : String) (left right : RawPattern)
  | member (sort : String) (left right : RawPattern)
  | neg (p : RawPredicate)
  | conj (p q : RawPredicate)
  | disj (p q : RawPredicate)
  | ex (name bound : String) (p : RawPredicate)
  deriving Repr

inductive RawSentence where
  | value (p : RawPattern)
  | scheme (parameter : String) (p : RawPredicate)
  deriving Repr

structure Attributes where
  functional : Bool := false
  constructor : Bool := false
  deriving DecidableEq, Repr

structure Symbol where
  profile : Kore.Modules.SymbolDeclaration
  attributes : Attributes
  deriving DecidableEq, Repr

inductive Declaration where
  | sort (name : String)
  | symbol (d : Symbol)
  | axiomDecl (p : RawSentence)
  | claim (p : RawSentence)
  deriving Repr

structure Located where
  location : Kore.Modules.Location
  declaration : Declaration
  deriving Repr

structure Source where
  moduleName : String
  location : Kore.Modules.Location
  declarations : List Located
  deriving Repr

namespace Syntax

def attributes : Parser Attributes := fun ts => do
  let (_, ts) ← punct '[' ts
  let rec go (fuel : Nat) (a : Attributes) : Parser Attributes := fun ts => do
    match fuel, ts with
    | 0, _ => none
    | _+1, .punctuation ']' :: ts => return (a, ts)
    | n+1, .name name :: ts =>
      let (_, ts) ← Kore.Modules.Syntax.emptyBraces ts
      let (_, ts) ← punct '(' ts
      let (_, ts) ← punct ')' ts
      let a ← match name with
        | "functional" => if a.functional then none else some {a with functional := true}
        | "constructor" => if a.constructor then none else some {a with constructor := true}
        | _ => none
      match ts with
      | .punctuation ',' :: ts =>
          -- A comma must introduce another actual attribute, never a trailing comma.
          match ts with
          | .name _ :: _ => go n a ts
          | _ => none
      | .punctuation ']' :: ts => return (a, ts)
      | _ => none
    | _, _ => none
  go (ts.length+1) {} ts

def resultSort (parameter : String) : Parser Unit := fun ts => do
  let (_, ts) ← word parameter ts
  return ((), ts)

def predicate (parameter : String) : Nat → Parser RawPredicate
  | 0, _ => none
  | n+1, .name name :: .punctuation '{' :: ts => do
    if name == "\\equals" || name == "\\in" then do
      let (input, ts) ← sort ts
      let (_, ts) ← punct ',' ts
      let (_, ts) ← resultSort parameter ts
      let (_, ts) ← punct '}' ts
      let (_, ts) ← punct '(' ts
      let (p, ts) ← GeneralFixedPoint.Syntax.pattern n ts
      let (_, ts) ← punct ',' ts
      let (q, ts) ← GeneralFixedPoint.Syntax.pattern n ts
      let (_, ts) ← punct ')' ts
      return (if name == "\\equals" then .equal input p q else .member input p q, ts)
    else do
      let (_, ts) ← resultSort parameter ts
      let (_, ts) ← punct '}' ts
      let (_, ts) ← punct '(' ts
      match name with
      | "\\top" | "\\bottom" =>
          let (_, ts) ← punct ')' ts
          return (if name == "\\top" then .top else .bottom, ts)
      | "\\not" =>
          let (p, ts) ← predicate parameter n ts
          let (_, ts) ← punct ')' ts
          return (.neg p, ts)
      | "\\and" | "\\or" | "\\implies" | "\\iff" =>
          let (p, ts) ← predicate parameter n ts
          let (_, ts) ← punct ',' ts
          let (q, ts) ← predicate parameter n ts
          let (_, ts) ← punct ')' ts
          let p := match name with
            | "\\and" => .conj p q
            | "\\or" => .disj p q
            | "\\implies" => .disj (.neg p) q
            | _ => .conj (.disj (.neg p) q) (.disj (.neg q) p)
          return (p, ts)
      | "\\exists" =>
          let (name, ts) ← identifier ts
          let (_, ts) ← punct ':' ts
          let (bound, ts) ← sort ts
          let (_, ts) ← punct ',' ts
          let (p, ts) ← predicate parameter n ts
          let (_, ts) ← punct ')' ts
          return (.ex name bound p, ts)
      | _ => none
  | _+1, _ => none

def sentence (fuel : Nat) : Parser RawSentence := fun ts => do
  let (_, ts) ← punct '{' ts
  match ts with
  | .punctuation '}' :: ts =>
      let (p, ts) ← GeneralFixedPoint.Syntax.pattern fuel ts
      let (_, ts) ← Kore.Modules.Syntax.emptyAttributes ts
      return (.value p, ts)
  | .name parameter :: .punctuation '}' :: ts =>
      if !GeneralFixedPoint.Syntax.ordinary parameter then none else do
        let (p, ts) ← predicate parameter fuel ts
        let (_, ts) ← Kore.Modules.Syntax.emptyAttributes ts
        return (.scheme parameter p, ts)
  | _ => none

def declarationBody (fuel : Nat) : Parser Declaration := fun ts =>
  match ts with
    | .name "sort" :: ts => do
        let (name, ts) ← identifier ts
        let (_, ts) ← Kore.Modules.Syntax.emptyBraces ts
        let (_, ts) ← Kore.Modules.Syntax.emptyAttributes ts
        return (Declaration.sort name, ts)
    | .name "symbol" :: ts => do
        let (profile, ts) ← Kore.Modules.Syntax.profile ts
        let (attrs, ts) ← attributes ts
        return (Declaration.symbol ⟨profile, attrs⟩, ts)
    | .name "axiom" :: ts => do
        let (p, ts) ← sentence fuel ts
        return (Declaration.axiomDecl p, ts)
    | .name "claim" :: ts => do
        let (p, ts) ← sentence fuel ts
        return (Declaration.claim p, ts)
    | _ => none

def declaration (total fuel : Nat) : Parser Located := fun ts => do
  let start := total - ts.length
  let (d, rest) ← declarationBody fuel ts
  return (⟨⟨start, ts.length - rest.length⟩, d⟩, rest)

def declarations (total : Nat) : Nat → Parser (List Located)
  | 0, _ => none
  | _+1, .name "endmodule" :: ts => return ([], ts)
  | n+1, ts => do
      let (d, ts) ← declaration total (n+1) ts
      let (ds, ts) ← declarations total n ts
      return (d :: ds, ts)

def parse (text : String) : Option Source := do
  let ts ← Kore.FixedPoint.Syntax.lex (text.toList.length+1) text.toList []
  let total := ts.length
  let (_, ts) ← Kore.Modules.Syntax.emptyAttributes ts
  let start := total-ts.length
  let (_, ts) ← word "module" ts
  let (name, ts) ← identifier ts
  let (ds, ts) ← declarations total (total+1) ts
  let (_, rest) ← Kore.Modules.Syntax.emptyAttributes ts
  if !rest.isEmpty then none else
    some ⟨name, ⟨start, total-rest.length-start⟩, ds⟩

end Syntax
end Silmaril.Logic.Kore.GeneralFixedPoint.BooleanTheory
