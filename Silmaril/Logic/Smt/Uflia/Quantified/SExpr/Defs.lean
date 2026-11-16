module

public import Silmaril.Logic.Smt.Uflia.Quantified.Variables
public import Silmaril.Logic.Smt.Uflia.SExpr.Thms

/-! Typed open-term generalization of the ground helper routines in
`Uflia/SExpr/Defs.lean` at base 6f78d7a34a. Existing ground definitions are unchanged.
The new context-indexed backend supports binders in every Boolean term position. -/
@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.Quantified

def Term.boolean {U : Type} {A : Signature U} {k : Nat} {Γ : Fin k → SortCode U}
    (b : Bool) : Term A Γ .bool := .app (.boolean b) (fun i => i.elim0)
def Term.integer {U : Type} {A : Signature U} {k : Nat} {Γ : Fin k → SortCode U}
    (n : Int) : Term A Γ .int := .app (.integer n) (fun i => i.elim0)

namespace SExpr
open Silmaril.Logic.Smt.Uflia.SExpr
variable {k : Nat} {Γ : Fin k → SortCode String}

/-- A decoded term keeps its computed sort, which is checked before casting. -/
structure PackedTerm (E : Environment) {k : Nat} (Γ : Fin k → SortCode String) where
  sort : SortCode String
  term : Quantified.Term E.signature Γ sort

def PackedTerm.expect? {E : Environment} (sort : SortCode String) (t : PackedTerm E Γ) :
    Option (Quantified.Term E.signature Γ sort) :=
  if h : t.sort = sort then some (h ▸ t.term) else none

def decodeArguments? {E : Environment} (recur : Expr → Option (PackedTerm E Γ)) :
    (inputs : List (SortCode String)) → List Expr →
      Option ((i : Fin inputs.length) → Quantified.Term E.signature Γ (inputs.get i))
  | [], [] => some (fun i => Fin.elim0 i)
  | input :: inputs, e :: es => do
      let t ← recur e
      let t ← t.expect? input
      let ts ← decodeArguments? recur inputs es
      pure (Fin.cases t ts)
  | _, _ => none

def applyUF? (E : Environment) (recur : Expr → Option (PackedTerm E Γ))
    (name : String) (args : List Expr) : Option (PackedTerm E Γ) := do
  let i ← lookup? E name
  let terms ← decodeArguments? recur (E.declarations.get i).inputs args
  pure ⟨(E.declarations.get i).output, .app (.uf (.declared i)) terms⟩

def unary? {E : Environment} (recur : Expr → Option (PackedTerm E Γ))
    {input output : SortCode String}
    (op : Operation E.signature 1 (fun _ => input) output) (e : Expr) :
    Option (PackedTerm E Γ) := do
  let t ← recur e
  let t ← t.expect? input
  pure ⟨output, .app op (fun _ => t)⟩

def binary? {E : Environment} (recur : Expr → Option (PackedTerm E Γ))
    {input output : SortCode String}
    (op : Operation E.signature 2 (fun _ => input) output) (a b : Expr) :
    Option (PackedTerm E Γ) := do
  let a ← recur a
  let a ← a.expect? input
  let b ← recur b
  let b ← b.expect? input
  pure ⟨output, .app op (Fin.cases a (fun _ => b))⟩

def equality? {E : Environment} (recur : Expr → Option (PackedTerm E Γ)) (a b : Expr) :
    Option (PackedTerm E Γ) := do
  let a ← recur a
  let b ← recur b
  let b ← b.expect? a.sort
  pure ⟨.bool, .app (.eq a.sort) (Fin.cases a.term (fun _ => b))⟩

def negate? {E : Environment} (decoded : Option (PackedTerm E Γ)) :
    Option (PackedTerm E Γ) := do
  let t ← decoded
  let t ← t.expect? .bool
  pure ⟨.bool, .app .not (fun _ => t)⟩

def implication? {E : Environment} (recur : Expr → Option (PackedTerm E Γ)) (a b : Expr) :
    Option (PackedTerm E Γ) := do
  let a ← recur a
  let a ← a.expect? .bool
  let b ← recur b
  let b ← b.expect? .bool
  pure ⟨.bool, .app .or (Fin.cases (.app .not (fun _ => a)) (fun _ => b))⟩

def xor? {E : Environment} (recur : Expr → Option (PackedTerm E Γ)) (a b : Expr) :
    Option (PackedTerm E Γ) := do
  let a ← recur a
  let a ← a.expect? .bool
  let b ← recur b
  let b ← b.expect? .bool
  pure ⟨.bool, .app .not (fun _ => .app (.eq .bool) (Fin.cases a (fun _ => b)))⟩

def ite? {E : Environment} (recur : Expr → Option (PackedTerm E Γ)) (c a b : Expr) :
    Option (PackedTerm E Γ) := do
  let c ← recur c
  let c ← c.expect? .bool
  let a ← recur a
  let b ← recur b
  let b ← b.expect? a.sort
  pure ⟨a.sort, .app (.ite a.sort) (Fin.cases c (Fin.cases a.term (fun _ => b)))⟩

/-- Typed local values are already elaborated in the outer environment. No
text substitution or fresh-name oracle is needed to avoid capture. -/
abbrev Locals (E : Environment) {k : Nat} (Γ : Fin k → SortCode String) := List (String × PackedTerm E Γ)

def local? {E : Environment} : Locals E Γ → String → Option (PackedTerm E Γ)
  | [], _ => none
  | (name, value) :: rest, key => if name = key then some value else local? rest key

/-- All right-hand sides use the same caller-supplied outer scope. -/
def letBindings? {E : Environment} (recur : Expr → Option (PackedTerm E Γ)) :
    List Expr → Option (Locals E Γ)
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
    (a b : Quantified.Term E.signature Γ sort) : Quantified.Term E.signature Γ sort :=
  .app op (Fin.cases a (fun _ => b))

/-- Left-associated folding preserves the old binary output exactly. -/
def foldTerms {E : Environment} {sort : SortCode String}
    (op : Operation E.signature 2 (fun _ => sort) sort)
    (first : Quantified.Term E.signature Γ sort) (rest : List (Quantified.Term E.signature Γ sort)) :
    Quantified.Term E.signature Γ sort := rest.foldl (pair op) first

def typedTerms? {E : Environment} (recur : Expr → Option (PackedTerm E Γ))
    (sort : SortCode String) (es : List Expr) : Option (List (Quantified.Term E.signature Γ sort)) :=
  es.mapM (fun e => do let t ← recur e; t.expect? sort)

def fold? {E : Environment} (recur : Expr → Option (PackedTerm E Γ))
    {sort : SortCode String} (op : Operation E.signature 2 (fun _ => sort) sort) :
    List Expr → Option (PackedTerm E Γ)
  | a :: b :: rest => do
      let a ← recur a
      let a ← a.expect? sort
      let bs ← typedTerms? recur sort (b :: rest)
      pure ⟨sort, foldTerms op a bs⟩
  | _ => none

def conjunction {E : Environment} : List (Quantified.Formula E.signature Γ) → Quantified.Formula E.signature Γ
  | [] => Quantified.Term.boolean true
  | first :: rest => foldTerms .and first rest

def adjacent {α β : Type} (relation : α → α → β) : List α → List β
  | a :: b :: rest => relation a b :: adjacent relation (b :: rest)
  | _ => []

def allPairs {α β : Type} (relation : α → α → β) : List α → List β
  | [] => []
  | a :: rest => rest.map (relation a) ++ allPairs relation rest

def compare? {E : Environment} (recur : Expr → Option (PackedTerm E Γ))
    (op : Operation E.signature 2 (fun _ => .int) .bool) (reverse : Bool) :
    List Expr → Option (PackedTerm E Γ)
  | a :: b :: rest => do
      let ts ← typedTerms? recur .int (a :: b :: rest)
      let relation := fun a b => .app op (Fin.cases (if reverse then b else a)
        (fun _ => if reverse then a else b))
      pure ⟨.bool, conjunction (adjacent relation ts)⟩
  | _ => none

def equalities? {E : Environment} (recur : Expr → Option (PackedTerm E Γ))
    (distinct : Bool) : List Expr → Option (PackedTerm E Γ)
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
    Quantified.Term E.signature Γ sort → Option Int
  | .app (.integer n) _ => some n
  | .app (.scale k) args => (integerValue? (args 0)).map (k * ·)
  | _ => none

/-- Fold literal coefficients and distribute scaling over additive terms.
Other Int terms retain the existing arbitrary-term scale operation; source
acceptance is mathematical linear elaboration, not a claim of exact membership
in the narrower textual QF_LIA coefficient grammar. Other sorts are unchanged. -/
def scaleLinear {E : Environment} {sort : SortCode String} (coefficient : Int) :
    Quantified.Term E.signature Γ sort → Quantified.Term E.signature Γ sort
  | .app (.integer n) _ => Quantified.Term.integer (coefficient * n)
  | .app (.add) args => pair .add (scaleLinear coefficient (args 0))
      (scaleLinear coefficient (args 1))
  | .app (.sub) args => pair .sub (scaleLinear coefficient (args 0))
      (scaleLinear coefficient (args 1))
  | .app (.scale k) args => scaleLinear (coefficient * k) (args 0)
  | term => match sort with
    | .int => .app (.scale coefficient) (fun _ => term)
    | _ => term

def multiplyFactors? {E : Environment} :
    List (Quantified.Term E.signature Γ .int) → Int → Option (Quantified.Term E.signature Γ .int) →
      Option (Quantified.Term E.signature Γ .int)
  | [], coefficient, none => some (Quantified.Term.integer coefficient)
  | [], coefficient, some term => some (scaleLinear coefficient term)
  | t :: rest, coefficient, factor => match integerValue? t with
    | some k => multiplyFactors? rest (coefficient * k) factor
    | none => match factor with
      | some _ => none
      | none => multiplyFactors? rest coefficient (some t)

def multiply? {E : Environment} (recur : Expr → Option (PackedTerm E Γ)) :
    List Expr → Option (PackedTerm E Γ)
  | a :: b :: rest => do
      let ts ← typedTerms? recur .int (a :: b :: rest)
      let term ← multiplyFactors? ts 1 none
      pure ⟨.int, term⟩
  | _ => none

/-- Binding names and sorts are checked. Repeated names are permitted: the
last same-list binder shadows earlier ones, as with sequential nesting. -/
def binders? (E : Environment) : List Expr → Option (List (String × SortCode String))
  | [] => some []
  | .list [.atom name, sort] :: rest => do
      if !simpleSymbol name || reserved.contains name then none else do
        let sort ← E.sort? sort
        let tail ← binders? E rest
        some ((name, sort) :: tail)
  | _ => none

def quantify? (E : Environment) (universal : Bool)
    (decode : ∀ {k : Nat} {Γ : Fin k → SortCode String}, Locals E Γ → Expr → Option (PackedTerm E Γ)) :
    {k : Nat} → {Γ : Fin k → SortCode String} → Locals E Γ →
      List (String × SortCode String) → Expr → Option (PackedTerm E Γ)
  | _, _, locals, [], body => decode locals body
  | _, _, locals, (name, sort) :: rest, body => do
      let shifted := locals.map (fun entry =>
        ((entry.1, ⟨entry.2.sort, entry.2.term.weaken sort⟩) : String × PackedTerm E _))
      let value : PackedTerm E _ := ⟨sort, .var 0⟩
      let result ← quantify? E universal decode ((name, value) :: shifted) rest body
      let term ← result.expect? .bool
      pure ⟨.bool, if universal then .all sort term else .ex sort term⟩

/-- Scoped elaboration lowers let-bound variables to typed terms in the current context. Binding
right-hand sides are parallel; locals shadow both outer locals and user function
names. A local scalar cannot fall back to a global function in application position. -/
def decodeScopedFuel? (E : Environment) : Nat → {k : Nat} → {Γ : Fin k → SortCode String} →
    Locals E Γ → Expr → Option (PackedTerm E Γ)
  | 0, _, _, _, _ => none
  | fuel + 1, _, _, locals, e =>
    let recur := decodeScopedFuel? E fuel locals
    match e with
    | .atom "true" => some ⟨.bool, Quantified.Term.boolean true⟩
    | .atom "false" => some ⟨.bool, Quantified.Term.boolean false⟩
    | .atom name => match local? locals name with
      | some term => some term
      | none => match numeral? e with
        | some n => some ⟨.int, Quantified.Term.integer n⟩
        | none => applyUF? E recur name []
    | .list [.atom "forall", .list bindings@(_ :: _), body] => do
        let binders ← binders? E bindings
        quantify? E true (fun locals body => decodeScopedFuel? E fuel locals body) locals binders body
    | .list [.atom "exists", .list bindings@(_ :: _), body] => do
        let binders ← binders? E bindings
        quantify? E false (fun locals body => decodeScopedFuel? E fuel locals body) locals binders body
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

def decodeTerm? (E : Environment) (e : Expr) : Option (PackedTerm E (fun i : Fin 0 => i.elim0)) :=
  decodeScopedFuel? E (expressionFuel e) [] e

def decodeSentence? (E : Environment) (e : Expr) : Option (Sentence E.signature) := do
  let term ← decodeTerm? E e
  term.expect? .bool

structure Accepted (E : Environment) where
  expression : Expr
  sentence : Sentence E.signature
  decoded : decodeSentence? E expression = some sentence

/-- Parse exactly one expression using the shared byte reader. -/
def parse? (E : Environment) (bytes : List UInt8) : Option (Sentence E.signature) := do
  let forms ← Silmaril.Logic.Smt.readForms bytes
  match forms with
  | [expression] => decodeSentence? E expression
  | _ => none

/-- Retain the actual input bytes and both reader and typed-decoder equations. -/
structure ByteAccepted (E : Environment) extends Accepted E where
  bytes : List UInt8
  reads : Silmaril.Logic.Smt.readForms bytes = some [expression]

def accept? (E : Environment) (bytes : List UInt8) : Option (ByteAccepted E) :=
  match hread : Silmaril.Logic.Smt.readForms bytes with
  | some [expression] =>
      match hdecode : decodeSentence? E expression with
      | some sentence => some ⟨⟨expression, sentence, hdecode⟩, bytes, hread⟩
      | none => none
  | _ => none

noncomputable def ByteAccepted.Holds {E : Environment} (a : ByteAccepted E)
    (M : Model E.signature) : Prop := Sentence.Holds a.sentence M
noncomputable def ByteAccepted.Sat {E : Environment} (a : ByteAccepted E) : Prop :=
  Sentence.Sat a.sentence
noncomputable def ByteAccepted.Unsat {E : Environment} (a : ByteAccepted E) : Prop :=
  Sentence.Unsat a.sentence

/-- Byte-level UNSAT requires successful parsing; rejection is not UNSAT. -/
noncomputable def Unsat (E : Environment) (bytes : List UInt8) : Prop :=
  ∃ p, parse? E bytes = some p ∧ Sentence.Unsat p

noncomputable def Sat (E : Environment) (bytes : List UInt8) : Prop :=
  ∃ p, parse? E bytes = some p ∧ Sentence.Sat p

theorem ByteAccepted.parsed {E : Environment} (a : ByteAccepted E) :
    parse? E a.bytes = some a.sentence := by
  simp only [parse?, a.reads]
  exact a.decoded

end SExpr
end Silmaril.Logic.Smt.Uflia.Quantified
