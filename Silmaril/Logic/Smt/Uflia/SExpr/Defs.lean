module

public import Silmaril.Logic.Smt.Uflia.Thms
public import Silmaril.Logic.Smt.SExpr.Defs

/-!
# A typed S-expression frontend for abstract UF/LIA

This frontend is independent of the older SMT script decoder. It accepts a
declaration prefix with nonparametric user sorts and UF symbols of arbitrary
arity, and decodes ground terms into the abstract sorted language. Symbols are
looked up by name, with exact arity and sort checks. Bool/Int have fixed meanings.
Associative operators accept at least two operands; equality and comparisons
chain, and distinct is pairwise. Parallel lexical `let` lowers to typed terms.
Multiplication normalizes concrete coefficients over additive terms and retains
the existing arbitrary-term scaling semantics for other typed Int factors. Quantifiers, division, modulo, attributes, quoted identifiers and
incremental commands are unsupported. Rejection is an error, never UNSAT.

Fuel is explicit in recursive decoding. The default counts S-expression nodes.
Acceptance has a proof of an actual decoder equality; no
external semantic certificate is an input to parsing.
-/

@[expose] public section

namespace Silmaril.Logic.Smt.Uflia.SExpr

open Silmaril.Logic.Algebraic

abbrev Expr := Silmaril.Logic.Smt.SE

structure Declaration where
  name : String
  inputs : List (SortCode String)
  output : SortCode String

structure Environment where
  sorts : List String := []
  declarations : List Declaration := []

/-- Each actual declaration supplies exactly its recorded operation profile. -/
inductive Symbol (E : Environment) : (n : Nat) → (Fin n → SortCode String) →
    SortCode String → Type where
  | declared (i : Fin E.declarations.length) :
      Symbol E (E.declarations.get i).inputs.length (E.declarations.get i).inputs.get
        (E.declarations.get i).output

def Environment.signature (E : Environment) : Signature String := ⟨Symbol E⟩

def reserved : List String :=
  ["true", "false", "not", "and", "or", "=>", "xor", "=", "distinct", "ite",
    "+", "-", "*", "<=", "<", ">=", ">", "div", "mod", "abs", "**", "let", "forall", "exists"]

/-- ASCII SMT-LIB simple symbols, excluding lexical reserved words. Quoted
symbols are outside this frontend; arbitrary strings inside `Expr.atom` are
not automatically valid identifiers. -/
def simpleSymbol (name : String) : Bool :=
  let initial := fun c : Char => c.isAlpha || "~!@$%^&*_-+=<>.?/".toList.contains c
  match name.toList with
  | [] => false
  | c :: cs => initial c && cs.all (fun c => initial c || c.isDigit) &&
      !["!", "_", "as", "BINARY", "DECIMAL", "HEXADECIMAL", "NUMERAL", "STRING",
        "exists", "forall", "let", "match", "par"].contains name

def Environment.sort? (E : Environment) : Expr → Option (SortCode String)
  | .atom "Bool" => some .bool
  | .atom "Int" => some .int
  | .atom name => if simpleSymbol name && E.sorts.contains name then some (.user name) else none
  | _ => none

def Environment.addDeclaration? (E : Environment) (name : String)
    (inputs : List (SortCode String)) (output : SortCode String) : Option Environment :=
  if simpleSymbol name && !reserved.contains name &&
      !(E.declarations.any (fun d => d.name == name)) then
    some { E with declarations := E.declarations ++ [⟨name, inputs, output⟩] }
  else none

/-- Decode declaration commands in order. Only earlier sort declarations are
visible. Functions are not overloaded and names are declared once. -/
def Environment.command? (E : Environment) : Expr → Option Environment
  | .list [.atom "declare-sort", .atom name, .atom "0"] =>
      if simpleSymbol name && name != "Bool" && name != "Int" &&
          !reserved.contains name && !E.sorts.contains name then
        some { E with sorts := E.sorts ++ [name] }
      else none
  | .list [.atom "declare-const", .atom name, output] => do
      let result ← E.sort? output
      E.addDeclaration? name [] result
  | .list [.atom "declare-fun", .atom name, .list inputs, output] => do
      let arguments ← inputs.mapM E.sort?
      let result ← E.sort? output
      E.addDeclaration? name arguments result
  | _ => none

def declarations? (forms : List Expr) : Option Environment :=
  forms.foldlM Environment.command? {}

/-- An environment obtained from an actual successfully decoded declaration
prefix. Raw `Environment` values remain available for abstract API use. -/
structure DeclarationPrefix where
  forms : List Expr
  environment : Environment
  decoded : declarations? forms = some environment

/-- A decoded term keeps its computed sort, which is checked before casting. -/
structure PackedTerm (E : Environment) where
  sort : SortCode String
  term : Uflia.Term E.signature sort

def PackedTerm.expect? {E : Environment} (sort : SortCode String) (t : PackedTerm E) :
    Option (Uflia.Term E.signature sort) :=
  if h : t.sort = sort then some (h ▸ t.term) else none

def decodeArguments? {E : Environment} (recur : Expr → Option (PackedTerm E)) :
    (inputs : List (SortCode String)) → List Expr →
      Option ((i : Fin inputs.length) → Uflia.Term E.signature (inputs.get i))
  | [], [] => some (fun i => Fin.elim0 i)
  | input :: inputs, e :: es => do
      let t ← recur e
      let t ← t.expect? input
      let ts ← decodeArguments? recur inputs es
      pure (Fin.cases t ts)
  | _, _ => none

def lookup? (E : Environment) (name : String) : Option (Fin E.declarations.length) :=
  if simpleSymbol name && !reserved.contains name then
    (List.finRange E.declarations.length).find? (fun i => (E.declarations.get i).name == name)
  else none

def applyUF? (E : Environment) (recur : Expr → Option (PackedTerm E))
    (name : String) (args : List Expr) : Option (PackedTerm E) := do
  let i ← lookup? E name
  let terms ← decodeArguments? recur (E.declarations.get i).inputs args
  pure ⟨(E.declarations.get i).output, .app (.uf (.declared i)) terms⟩

/-- SMT-LIB decimal numerals have no leading zero except the numeral `0`. -/
def naturalNumeral? (n : String) : Option Nat :=
  match n.toList with
  | '0' :: _ :: _ => none
  | cs => Silmaril.Logic.Smt.digits 10 Silmaril.Logic.Smt.decVal cs

def numeral? : Expr → Option Int
  | .atom n => (naturalNumeral? n).map Int.ofNat
  | .list [.atom "-", .atom n] =>
      (naturalNumeral? n).map (fun n => -(n : Int))
  | _ => none

def unary? {E : Environment} (recur : Expr → Option (PackedTerm E))
    {input output : SortCode String}
    (op : Operation E.signature 1 (fun _ => input) output) (e : Expr) :
    Option (PackedTerm E) := do
  let t ← recur e
  let t ← t.expect? input
  pure ⟨output, .app op (fun _ => t)⟩

def binary? {E : Environment} (recur : Expr → Option (PackedTerm E))
    {input output : SortCode String}
    (op : Operation E.signature 2 (fun _ => input) output) (a b : Expr) :
    Option (PackedTerm E) := do
  let a ← recur a
  let a ← a.expect? input
  let b ← recur b
  let b ← b.expect? input
  pure ⟨output, .app op (Fin.cases a (fun _ => b))⟩

def equality? {E : Environment} (recur : Expr → Option (PackedTerm E)) (a b : Expr) :
    Option (PackedTerm E) := do
  let a ← recur a
  let b ← recur b
  let b ← b.expect? a.sort
  pure ⟨.bool, .app (.eq a.sort) (Fin.cases a.term (fun _ => b))⟩

def negate? {E : Environment} (decoded : Option (PackedTerm E)) :
    Option (PackedTerm E) := do
  let t ← decoded
  let t ← t.expect? .bool
  pure ⟨.bool, .app .not (fun _ => t)⟩

def implication? {E : Environment} (recur : Expr → Option (PackedTerm E)) (a b : Expr) :
    Option (PackedTerm E) := do
  let a ← recur a
  let a ← a.expect? .bool
  let b ← recur b
  let b ← b.expect? .bool
  pure ⟨.bool, .app .or (Fin.cases (.app .not (fun _ => a)) (fun _ => b))⟩

def xor? {E : Environment} (recur : Expr → Option (PackedTerm E)) (a b : Expr) :
    Option (PackedTerm E) := do
  let a ← recur a
  let a ← a.expect? .bool
  let b ← recur b
  let b ← b.expect? .bool
  pure ⟨.bool, .app .not (fun _ => .app (.eq .bool) (Fin.cases a (fun _ => b)))⟩

def ite? {E : Environment} (recur : Expr → Option (PackedTerm E)) (c a b : Expr) :
    Option (PackedTerm E) := do
  let c ← recur c
  let c ← c.expect? .bool
  let a ← recur a
  let b ← recur b
  let b ← b.expect? a.sort
  pure ⟨a.sort, .app (.ite a.sort) (Fin.cases c (Fin.cases a.term (fun _ => b)))⟩

/-- Typed local values are already elaborated in the outer environment. No
text substitution or fresh-name oracle is needed to avoid capture. -/
abbrev Locals (E : Environment) := List (String × PackedTerm E)

def local? {E : Environment} : Locals E → String → Option (PackedTerm E)
  | [], _ => none
  | (name, value) :: rest, key => if name = key then some value else local? rest key

/-- All right-hand sides use the same caller-supplied outer scope. -/
def letBindings? {E : Environment} (recur : Expr → Option (PackedTerm E)) :
    List Expr → Option (Locals E)
  | [] => some []
  | .list [.atom name, e] :: rest => do
      if !simpleSymbol name || reserved.contains name then none else do
        let value ← recur e
        let values ← letBindings? recur rest
        if values.any (fun pair => pair.1 == name) then none
        else pure ((name, value) :: values)
  | _ => none

def pair {E : Environment} {sort : SortCode String}
    (op : Operation E.signature 2 (fun _ => sort) sort)
    (a b : Uflia.Term E.signature sort) : Uflia.Term E.signature sort :=
  .app op (Fin.cases a (fun _ => b))

/-- Left-associated folding preserves the old binary output exactly. -/
def foldTerms {E : Environment} {sort : SortCode String}
    (op : Operation E.signature 2 (fun _ => sort) sort)
    (first : Uflia.Term E.signature sort) (rest : List (Uflia.Term E.signature sort)) :
    Uflia.Term E.signature sort := rest.foldl (pair op) first

def typedTerms? {E : Environment} (recur : Expr → Option (PackedTerm E))
    (sort : SortCode String) (es : List Expr) : Option (List (Uflia.Term E.signature sort)) :=
  es.mapM (fun e => do let t ← recur e; t.expect? sort)

def fold? {E : Environment} (recur : Expr → Option (PackedTerm E))
    {sort : SortCode String} (op : Operation E.signature 2 (fun _ => sort) sort) :
    List Expr → Option (PackedTerm E)
  | a :: b :: rest => do
      let a ← recur a
      let a ← a.expect? sort
      let bs ← typedTerms? recur sort (b :: rest)
      pure ⟨sort, foldTerms op a bs⟩
  | _ => none

def conjunction {E : Environment} : List (Formula E.signature) → Formula E.signature
  | [] => Uflia.Term.boolean true
  | first :: rest => foldTerms .and first rest

def adjacent {α β : Type} (relation : α → α → β) : List α → List β
  | a :: b :: rest => relation a b :: adjacent relation (b :: rest)
  | _ => []

def allPairs {α β : Type} (relation : α → α → β) : List α → List β
  | [] => []
  | a :: rest => rest.map (relation a) ++ allPairs relation rest

def compare? {E : Environment} (recur : Expr → Option (PackedTerm E))
    (op : Operation E.signature 2 (fun _ => .int) .bool) (reverse : Bool) :
    List Expr → Option (PackedTerm E)
  | a :: b :: rest => do
      let ts ← typedTerms? recur .int (a :: b :: rest)
      let relation := fun a b => .app op (Fin.cases (if reverse then b else a)
        (fun _ => if reverse then a else b))
      pure ⟨.bool, conjunction (adjacent relation ts)⟩
  | _ => none

def equalities? {E : Environment} (recur : Expr → Option (PackedTerm E))
    (distinct : Bool) : List Expr → Option (PackedTerm E)
  | a :: b :: rest => do
      let a ← recur a
      let ts ← typedTerms? recur a.sort (b :: rest)
      let relation := fun x y =>
        let eq := .app (.eq a.sort) (Fin.cases x (fun _ => y))
        if distinct then .app .not (fun _ => eq) else eq
      pure ⟨.bool, conjunction (if distinct then allPairs relation (a.term :: ts)
        else adjacent relation (a.term :: ts))⟩
  | _ => none

/-- Recognize literal integer values after typed elaboration, including unary
negation. This does not treat arbitrary constant expressions as coefficients. -/
def integerValue? {E : Environment} {sort : SortCode String} :
    Uflia.Term E.signature sort → Option Int
  | .app (.integer n) _ => some n
  | .app (.scale k) args => (integerValue? (args 0)).map (k * ·)
  | _ => none

/-- Fold literal coefficients and distribute scaling over additive terms.
Other Int terms retain the existing arbitrary-term scale operation; source
acceptance is mathematical linear elaboration, not a claim of exact membership
in the narrower textual QF_LIA coefficient grammar. Other sorts are unchanged. -/
def scaleLinear {E : Environment} {sort : SortCode String} (coefficient : Int) :
    Uflia.Term E.signature sort → Uflia.Term E.signature sort
  | .app (.integer n) _ => Uflia.Term.integer (coefficient * n)
  | .app (.add) args => pair .add (scaleLinear coefficient (args 0))
      (scaleLinear coefficient (args 1))
  | .app (.sub) args => pair .sub (scaleLinear coefficient (args 0))
      (scaleLinear coefficient (args 1))
  | .app (.scale k) args => scaleLinear (coefficient * k) (args 0)
  | term => match sort with
    | .int => .app (.scale coefficient) (fun _ => term)
    | _ => term

def multiplyFactors? {E : Environment} :
    List (Uflia.Term E.signature .int) → Int → Option (Uflia.Term E.signature .int) →
      Option (Uflia.Term E.signature .int)
  | [], coefficient, none => some (Uflia.Term.integer coefficient)
  | [], coefficient, some term => some (scaleLinear coefficient term)
  | t :: rest, coefficient, factor => match integerValue? t with
    | some k => multiplyFactors? rest (coefficient * k) factor
    | none => match factor with
      | some _ => none
      | none => multiplyFactors? rest coefficient (some t)

def multiply? {E : Environment} (recur : Expr → Option (PackedTerm E)) :
    List Expr → Option (PackedTerm E)
  | a :: b :: rest => do
      let ts ← typedTerms? recur .int (a :: b :: rest)
      let term ← multiplyFactors? ts 1 none
      pure ⟨.int, term⟩
  | _ => none

/-- Scoped elaboration lowers let-bound variables to closed typed terms. Binding
right-hand sides are parallel; locals shadow both outer locals and user function
names. A local scalar cannot fall back to a global function in application position. -/
def decodeScopedFuel? (E : Environment) : Nat → Locals E → Expr → Option (PackedTerm E)
  | 0, _, _ => none
  | fuel + 1, locals, e =>
    let recur := decodeScopedFuel? E fuel locals
    match e with
    | .atom "true" => some ⟨.bool, Uflia.Term.boolean true⟩
    | .atom "false" => some ⟨.bool, Uflia.Term.boolean false⟩
    | .atom name => match local? locals name with
      | some term => some term
      | none => match numeral? e with
        | some n => some ⟨.int, Uflia.Term.integer n⟩
        | none => applyUF? E recur name []
    | .list [.atom "let", .list bindings@(_ :: _), body] => do
        let values ← letBindings? recur bindings
        decodeScopedFuel? E fuel (values ++ locals) body
    | .list [.atom "not", a] => unary? recur .not a
    | .list [.atom "-", a] => unary? recur (.scale (-1)) a
    | .list (.atom "and" :: es) => fold? recur .and es
    | .list (.atom "or" :: es) => fold? recur .or es
    | .list [.atom "=>", a, b] => implication? recur a b
    | .list [.atom "xor", a, b] => xor? recur a b
    | .list (.atom "+" :: es) => fold? recur .add es
    | .list (.atom "-" :: es) => fold? recur .sub es
    | .list (.atom "<=" :: es) => compare? recur .le false es
    | .list (.atom "<" :: es) => compare? recur .lt false es
    | .list (.atom ">=" :: es) => compare? recur .le true es
    | .list (.atom ">" :: es) => compare? recur .lt true es
    | .list (.atom "=" :: es) => equalities? recur false es
    | .list (.atom "distinct" :: es) => equalities? recur true es
    | .list [.atom "ite", c, a, b] => ite? recur c a b
    | .list (.atom "*" :: es) => multiply? recur es
    | .list (.atom name :: args) =>
      if args.isEmpty || reserved.contains name || (local? locals name).isSome then none
      else applyUF? E recur name args
    | _ => none

/-- The original entry point elaborates in an empty local-variable scope. -/
def decodeTermFuel? (E : Environment) (fuel : Nat) (e : Expr) : Option (PackedTerm E) :=
  decodeScopedFuel? E fuel [] e

mutual
/-- Count syntax nodes explicitly rather than using an imported generated
`SizeOf` implementation, which need not expose executable code. -/
def expressionFuel : Expr → Nat
  | .atom _ => 1
  | .list xs => expressionsFuel xs + 1

def expressionsFuel : List Expr → Nat
  | [] => 0
  | e :: es => expressionFuel e + expressionsFuel es
end

def decodeTerm? (E : Environment) (e : Expr) : Option (PackedTerm E) :=
  decodeTermFuel? E (expressionFuel e) e

def decodeFormula? (E : Environment) (e : Expr) : Option (Formula E.signature) := do
  let t ← decodeTerm? E e
  t.expect? .bool

/-- Accepted S-expression assertions carry the actual executable decoder result. -/
structure Assertion (E : Environment) where
  expression : Expr
  formula : Formula E.signature
  decoded : decodeFormula? E expression = some formula

end Silmaril.Logic.Smt.Uflia.SExpr
