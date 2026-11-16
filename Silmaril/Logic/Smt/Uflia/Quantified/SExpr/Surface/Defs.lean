module

public import Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Defs

/-! Independent source evaluation. Literal provenance records source shape, not
whether a runtime integer happens to equal a literal. Quantifiers range over the
supplied carriers, and reject unless every body instance has Boolean sort. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Surface
open Silmaril.Logic.Smt.Uflia.SExpr

structure Data {E : Environment} (M : Model E.signature) (sort : SortCode String) where
  value : M.carriers.value sort
  literal : Option Int

structure Value {E : Environment} (M : Model E.signature) where
  sort : SortCode String
  data : Data M sort

def Value.expect? {E : Environment} {M : Model E.signature}
    (s : SortCode String) (v : Value M) : Option (Data M s) :=
  if h : v.sort = s then some (h ▸ v.data) else none

abbrev Locals {E : Environment} (M : Model E.signature) := List (String × Value M)

def local? {E : Environment} {M : Model E.signature} : Locals M → String → Option (Value M)
  | [], _ => none
  | (name, value) :: rest, key => if name = key then some value else local? rest key

/-- Semantic application uses model operations, never typed term evaluation. -/
def apply {E : Environment} (M : Model E.signature) {n inputs output}
    (op : Operation E.signature n inputs output) (args : ∀ i, Data M (inputs i)) : Data M output :=
  ⟨M.apply op (fun i => (args i).value), match op with
    | .integer n => some n
    | .scale k => (args 0).literal.map (k * ·)
    | _ => none⟩

def boolean {E : Environment} (M : Model E.signature) (b : Bool) : Value M :=
  ⟨.bool, ⟨b, none⟩⟩
def integer {E : Environment} (M : Model E.signature) (n : Int) : Value M :=
  ⟨.int, ⟨n, some n⟩⟩

def arguments? {E : Environment} (M : Model E.signature)
    (recur : Expr → Option (Value M)) :
    (inputs : List (SortCode String)) → List Expr →
      Option ((i : Fin inputs.length) → Data M (inputs.get i))
  | [], [] => some (fun i => i.elim0)
  | input :: inputs, e :: es => do
      let t ← recur e
      let t ← t.expect? input
      let ts ← arguments? M recur inputs es
      pure (Fin.cases t ts)
  | _, _ => none

def uf? (E : Environment) (M : Model E.signature) (recur : Expr → Option (Value M))
    (name : String) (es : List Expr) : Option (Value M) := do
  let i ← lookup? E name
  let args ← arguments? M recur (E.declarations.get i).inputs es
  pure ⟨(E.declarations.get i).output, apply M (.uf (.declared i)) args⟩

def unary? {E : Environment} (M : Model E.signature) (recur : Expr → Option (Value M))
    {input output} (op : Operation E.signature 1 (fun _ => input) output) (a : Expr) :
    Option (Value M) := do
  let a ← recur a
  let a ← a.expect? input
  pure ⟨output, apply M op (fun _ => a)⟩

def binary? {E : Environment} (M : Model E.signature) (recur : Expr → Option (Value M))
    {input output} (op : Operation E.signature 2 (fun _ => input) output) (a b : Expr) :
    Option (Value M) := do
  let a ← recur a
  let a ← a.expect? input
  let b ← recur b
  let b ← b.expect? input
  pure ⟨output, apply M op (Fin.cases a (fun _ => b))⟩

def negate? {E : Environment} (M : Model E.signature) (v : Option (Value M)) : Option (Value M) := do
  let v ← v
  let v ← v.expect? .bool
  pure ⟨.bool, apply M .not (fun _ => v)⟩

def implication? {E : Environment} (M : Model E.signature) (recur : Expr → Option (Value M))
    (a b : Expr) : Option (Value M) := do
  let a ← recur a
  let a ← a.expect? .bool
  let b ← recur b
  let b ← b.expect? .bool
  pure ⟨.bool, apply M .or (Fin.cases (apply M .not (fun _ => a)) (fun _ => b))⟩

def xor? {E : Environment} (M : Model E.signature) (recur : Expr → Option (Value M))
    (a b : Expr) : Option (Value M) := do
  let a ← recur a
  let a ← a.expect? .bool
  let b ← recur b
  let b ← b.expect? .bool
  pure ⟨.bool, apply M .not (fun _ => apply M (.eq .bool) (Fin.cases a (fun _ => b)))⟩

def ite? {E : Environment} (M : Model E.signature) (recur : Expr → Option (Value M))
    (c a b : Expr) : Option (Value M) := do
  let c ← recur c
  let c ← c.expect? .bool
  let a ← recur a
  let b ← recur b
  let b ← b.expect? a.sort
  pure ⟨a.sort, apply M (.ite a.sort) (Fin.cases c (Fin.cases a.data (fun _ => b)))⟩

/-- Parallel bindings: the same outer recursion evaluates every RHS. -/
def letBindings? {E : Environment} (M : Model E.signature) (recur : Expr → Option (Value M)) :
    List Expr → Option (Locals M)
  | [] => some []
  | .list [.atom name, e] :: rest => do
      if !simpleSymbol name || reserved.contains name then none else do
        let value ← recur e
        let values ← letBindings? M recur rest
        if values.any (fun pair => pair.1 == name) then none
        else pure ((name, value) :: values)
  | _ => none

def pair {E : Environment} (M : Model E.signature) {s}
    (op : Operation E.signature 2 (fun _ => s) s) (a b : Data M s) : Data M s :=
  apply M op (Fin.cases a (fun _ => b))

def foldValues {E : Environment} (M : Model E.signature) {s}
    (op : Operation E.signature 2 (fun _ => s) s) (a : Data M s) (rest : List (Data M s)) : Data M s :=
  rest.foldl (pair M op) a

def typedValues? {E : Environment} (M : Model E.signature) (recur : Expr → Option (Value M))
    (s : SortCode String) (es : List Expr) : Option (List (Data M s)) :=
  es.mapM (fun e => do let t ← recur e; t.expect? s)

def fold? {E : Environment} (M : Model E.signature) (recur : Expr → Option (Value M))
    {s} (op : Operation E.signature 2 (fun _ => s) s) : List Expr → Option (Value M)
  | a :: b :: rest => do
      let a ← recur a
      let a ← a.expect? s
      let bs ← typedValues? M recur s (b :: rest)
      pure ⟨s, foldValues M op a bs⟩
  | _ => none

def conjunction {E : Environment} (M : Model E.signature) : List (Data M .bool) → Data M .bool
  | [] => ⟨true, none⟩
  | first :: rest => foldValues M .and first rest

def compare? {E : Environment} (M : Model E.signature) (recur : Expr → Option (Value M))
    (op : Operation E.signature 2 (fun _ => .int) .bool) (reverse : Bool) :
    List Expr → Option (Value M)
  | a :: b :: rest => do
      let ts ← typedValues? M recur .int (a :: b :: rest)
      let relation := fun a b => apply M op (Fin.cases (if reverse then b else a)
        (fun _ => if reverse then a else b))
      pure ⟨.bool, conjunction M (SExpr.adjacent relation ts)⟩
  | _ => none

def equalities? {E : Environment} (M : Model E.signature) (recur : Expr → Option (Value M))
    (distinct : Bool) : List Expr → Option (Value M)
  | a :: b :: rest => do
      let a ← recur a
      let ts ← typedValues? M recur a.sort (b :: rest)
      let relation := fun x y =>
        let eq := apply M (.eq a.sort) (Fin.cases x (fun _ => y))
        if distinct then apply M .not (fun _ => eq) else eq
      pure ⟨.bool, conjunction M (if distinct then SExpr.allPairs relation (a.data :: ts)
        else SExpr.adjacent relation (a.data :: ts))⟩
  | _ => none

def scale {E : Environment} (M : Model E.signature) (k : Int) (t : Data M .int) : Data M .int :=
  ⟨k * t.value, t.literal.map (k * ·)⟩

/-- Admission depends on literal provenance, never on a runtime numeric test. -/
def multiplyFactors? {E : Environment} (M : Model E.signature) :
    List (Data M .int) → Int → Option (Data M .int) → Option (Data M .int)
  | [], k, none => some ⟨k, some k⟩
  | [], k, some t => some (scale M k t)
  | t :: rest, k, factor => match t.literal with
    | some n => multiplyFactors? M rest (k * n) factor
    | none => match factor with
      | some _ => none
      | none => multiplyFactors? M rest k (some t)

def multiply? {E : Environment} (M : Model E.signature) (recur : Expr → Option (Value M)) :
    List Expr → Option (Value M)
  | a :: b :: rest => do
      let ts ← typedValues? M recur .int (a :: b :: rest)
      let value ← multiplyFactors? M ts 1 none
      pure ⟨.int, value⟩
  | _ => none

/-- Quantifier bodies must evaluate to Boolean values at EVERY bound value.
Rejection is propagated, never interpreted as Boolean false. -/
def quantify? {E : Environment} (M : Model E.signature) (universal : Bool)
    (recur : Locals M → Expr → Option (Value M)) :
    Locals M → List (String × SortCode String) → Expr → Option (Value M)
  | locals, [], body => recur locals body
  | locals, (name, sort) :: rest, body => by
      classical
      let result := fun x : M.carriers.value sort =>
        (quantify? M universal recur ((name, ⟨sort, ⟨x, none⟩⟩) :: locals) rest body).bind
          (Value.expect? .bool)
      exact if ∀ x, (result x).isSome = true then
        some (boolean M (if universal then decide (∀ x, (result x).map Data.value = some true)
          else decide (∃ x, (result x).map Data.value = some true)))
        else none

def evaluateScopedFuel? (E : Environment) (M : Model E.signature) :
    Nat → Locals M → Expr → Option (Value M)
  | 0, _, _ => none
  | fuel + 1, locals, e =>
    let recur := evaluateScopedFuel? E M fuel locals
    match e with
    | .atom "true" => some (boolean M true)
    | .atom "false" => some (boolean M false)
    | .atom name => match local? locals name with
      | some v => some v
      | none => match numeral? e with
        | some n => some (integer M n)
        | none => uf? E M recur name []
    | .list [.atom "forall", .list bindings@(_ :: _), body] => do
        let binders ← SExpr.binders? E bindings
        quantify? M true (evaluateScopedFuel? E M fuel) locals binders body
    | .list [.atom "exists", .list bindings@(_ :: _), body] => do
        let binders ← SExpr.binders? E bindings
        quantify? M false (evaluateScopedFuel? E M fuel) locals binders body
    | .list [.atom "let", .list bindings@(_ :: _), body] => do
        let values ← letBindings? M recur bindings
        evaluateScopedFuel? E M fuel (values ++ locals) body
    | .list [.atom "not", a] => unary? M recur .not a
    | .list [.atom "-", a] => unary? M recur (.scale (-1)) a
    | .list (.atom "and" :: es) => fold? M recur .and es
    | .list (.atom "or" :: es) => fold? M recur .or es
    | .list [.atom "=>", a, b] => implication? M recur a b
    | .list [.atom "xor", a, b] => xor? M recur a b
    | .list (.atom "+" :: es) => fold? M recur .add es
    | .list (.atom "-" :: es) => fold? M recur .sub es
    | .list (.atom "<=" :: es) => compare? M recur .le false es
    | .list (.atom "<" :: es) => compare? M recur .lt false es
    | .list (.atom ">=" :: es) => compare? M recur .le true es
    | .list (.atom ">" :: es) => compare? M recur .lt true es
    | .list (.atom "=" :: es) => equalities? M recur false es
    | .list (.atom "distinct" :: es) => equalities? M recur true es
    | .list [.atom "ite", c, a, b] => ite? M recur c a b
    | .list (.atom "*" :: es) => multiply? M recur es
    | .list (.atom name :: args) =>
      if args.isEmpty || reserved.contains name || (local? locals name).isSome then none
      else uf? E M recur name args
    | _ => none

def evaluate? (E : Environment) (M : Model E.signature) (e : Expr) : Option (Value M) :=
  evaluateScopedFuel? E M (expressionFuel e) [] e

def Holds (E : Environment) (M : Model E.signature) (e : Expr) : Prop :=
  ∃ literal, evaluate? E M e = some ⟨.bool, ⟨true, literal⟩⟩

end Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Surface
