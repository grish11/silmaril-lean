module

public import Silmaril.Logic.Smt.Uflia.Packaged.Defs

/-!
# Direct meaning of QF-UFLIA source expressions

These rules interpret S-expressions in one coherent global model. They neither
invoke the term decoder nor evaluate an elaborated term. They cover literals,
declared functions, Boolean/integer operations, comparisons, equality, distinct,
conditionals and parallel let bindings. `Surface.Thms` exposes preservation of
every successful result from the currently admitted decoder. The adjacent
README defines the terminology and explains the theorem's direction and scope.
-/

@[expose] public section

namespace Silmaril.Logic.Smt.Uflia.SExpr.Surface

open Silmaril.Logic.Algebraic

attribute [local instance] Classical.propDecidable

/-- Surface unary operations, independent of the elaborator's operation type. -/
inductive Unary : SortCode String → SortCode String → Type where
  | not : Unary .bool .bool
  | neg : Unary .int .int

def Unary.token {input output : SortCode String} : Unary input output → String
  | .not => "not"
  | .neg => "-"

def Unary.value {input output : SortCode String} (M : Packaged.GlobalModel) : Unary input output →
    M.carriers.value input → M.carriers.value output
  | .not, x => !x
  | .neg, x => -x

/-- Binary surface operations use standard integer and Boolean meanings. -/
inductive Binary : SortCode String → SortCode String → Type where
  | and : Binary .bool .bool
  | or : Binary .bool .bool
  | implies : Binary .bool .bool
  | xor : Binary .bool .bool
  | add : Binary .int .int
  | sub : Binary .int .int
  | le : Binary .int .bool
  | lt : Binary .int .bool
  | ge : Binary .int .bool
  | gt : Binary .int .bool

def Binary.token {input output : SortCode String} : Binary input output → String
  | .and => "and"
  | .or => "or"
  | .implies => "=>"
  | .xor => "xor"
  | .add => "+"
  | .sub => "-"
  | .le => "<="
  | .lt => "<"
  | .ge => ">="
  | .gt => ">"

def Binary.value {input output : SortCode String} (M : Packaged.GlobalModel) : Binary input output →
    M.carriers.value input → M.carriers.value input → M.carriers.value output
  | .and, x, y => x && y
  | .or, x, y => x || y
  | .implies, x, y => !x || y
  | .xor, x, y => !(x == y)
  | .add, x, y => x + y
  | .sub, x, y => x - y
  | .le, x, y => decide (x ≤ y)
  | .lt, x, y => decide (x < y)
  | .ge, x, y => decide (y ≤ x)
  | .gt, x, y => decide (y < x)

/-- The four admitted left-associated variadic operations. -/
inductive FoldOp : SortCode String → Type where
  | and : FoldOp .bool
  | or : FoldOp .bool
  | add : FoldOp .int
  | sub : FoldOp .int

def FoldOp.token {sort : SortCode String} : FoldOp sort → String
  | .and => "and"
  | .or => "or"
  | .add => "+"
  | .sub => "-"

def FoldOp.value {sort : SortCode String} (M : Packaged.GlobalModel) :
    FoldOp sort → M.carriers.value sort → M.carriers.value sort → M.carriers.value sort
  | .and, x, y => x && y
  | .or, x, y => x || y
  | .add, x, y => x + y
  | .sub, x, y => x - y

/-- Adjacent comparisons in source order, with conjunction of all links. -/
def adjacentValue {α : Type} (relation : α → α → Bool) : List α → Bool
  | a :: b :: rest => relation a b && adjacentValue relation (b :: rest)
  | _ => true

/-- Pairwise disequality, including nonadjacent values. -/
noncomputable def distinctValue {α : Type} : List α → Bool
  | [] => true
  | a :: rest => rest.all (fun b => !(decide (a = b))) && distinctValue rest

inductive CompareOp where
  | le | lt | ge | gt

def CompareOp.token : CompareOp → String
  | .le => "<="
  | .lt => "<"
  | .ge => ">="
  | .gt => ">"

def CompareOp.value : CompareOp → Int → Int → Bool
  | .le, x, y => decide (x ≤ y)
  | .lt, x, y => decide (x < y)
  | .ge, x, y => decide (y ≤ x)
  | .gt, x, y => decide (y < x)

/-- Semantic local values do not contain elaborated terms or decoder results. -/
structure Value (M : Packaged.GlobalModel) where
  sort : SortCode String
  value : M.carriers.value sort

abbrev Scope (M : Packaged.GlobalModel) := List (String × Value M)

def lookupValue? {M : Packaged.GlobalModel} : Scope M → String → Option (Value M)
  | [], _ => none
  | (name, value) :: rest, key => if name = key then some value else lookupValue? rest key

mutual
/-- Direct scoped evaluation follows the frontend's lexical dispatch. Literals
are recognized first, local scalar names shadow global functions, and reserved
heads never acquire an alternative UF interpretation. -/
inductive Evaluates (E : Environment) (M : Packaged.GlobalModel) :
    Scope M → Expr → (sort : SortCode String) → M.carriers.value sort → Prop where
  | boolean {scope : Scope M} (b : Bool) :
      Evaluates E M scope (.atom (if b then "true" else "false")) .bool b
  | numeral {scope : Scope M} (text : String) (n : Nat)
      (parsed : naturalNumeral? text = some n)
      (unbound : lookupValue? scope text = none) :
      Evaluates E M scope (.atom text) .int (n : Int)
  | local {scope : Scope M} (name : String) (value : Value M)
      (notTrue : name ≠ "true") (notFalse : name ≠ "false")
      (found : lookupValue? scope name = some value) :
      Evaluates E M scope (.atom name) value.sort value.value
  | constant {scope : Scope M} (name : String) (i : Fin E.declarations.length)
      (unreserved : reserved.contains name = false)
      (unbound : lookupValue? scope name = none)
      (notNumeral : naturalNumeral? name = none)
      (found : lookup? E name = some i)
      (empty : (E.declarations.get i).inputs = [])
      (args : (j : Fin (E.declarations.get i).inputs.length) →
        M.carriers.value ((E.declarations.get i).inputs.get j)) :
      Evaluates E M scope (.atom name) (E.declarations.get i).output
        (M.operation (E.declarations.get i).name args)
  | app {scope : Scope M} (name : String) (i : Fin E.declarations.length)
      (unreserved : reserved.contains name = false)
      (unbound : lookupValue? scope name = none)
      (found : lookup? E name = some i)
      (es : List Expr) (nonempty : es ≠ [])
      (args : (j : Fin (E.declarations.get i).inputs.length) →
        M.carriers.value ((E.declarations.get i).inputs.get j))
      (evaluated : ArgumentsEvaluate E M scope (E.declarations.get i).inputs es args) :
      Evaluates E M scope (.list (.atom name :: es)) (E.declarations.get i).output
        (M.operation (E.declarations.get i).name args)
  | unary {scope : Scope M} {input output : SortCode String}
      (op : Unary input output) {e : Expr} {v : M.carriers.value input}
      (operand : Evaluates E M scope e input v) :
      Evaluates E M scope (.list [.atom op.token, e]) output (op.value M v)
  | binary {scope : Scope M} {input output : SortCode String}
      (op : Binary input output) {a b : Expr} {x y : M.carriers.value input}
      (left : Evaluates E M scope a input x) (right : Evaluates E M scope b input y) :
      Evaluates E M scope (.list [.atom op.token, a, b]) output (op.value M x y)
  | fold {scope : Scope M} {sort : SortCode String} (op : FoldOp sort)
      (a b : Expr) (rest : List Expr) (x : M.carriers.value sort)
      (xs : List (M.carriers.value sort))
      (first : Evaluates E M scope a sort x)
      (remaining : OperandsEvaluate E M scope sort (b :: rest) xs) :
      Evaluates E M scope (.list (.atom op.token :: a :: b :: rest)) sort
        (xs.foldl (op.value M) x)
  | multiply {scope : Scope M} (a b : Expr) (rest : List Expr)
      (values : List Int)
      (operands : OperandsEvaluate E M scope .int (a :: b :: rest) values) :
      Evaluates E M scope (.list (.atom "*" :: a :: b :: rest)) .int values.prod
  | comparison {scope : Scope M} (op : CompareOp) (a b : Expr) (rest : List Expr)
      (values : List Int)
      (operands : OperandsEvaluate E M scope .int (a :: b :: rest) values) :
      Evaluates E M scope (.list (.atom op.token :: a :: b :: rest)) .bool
        (adjacentValue op.value values)
  | equalChain {scope : Scope M} {sort : SortCode String}
      (a b : Expr) (rest : List Expr) (values : List (M.carriers.value sort))
      (operands : OperandsEvaluate E M scope sort (a :: b :: rest) values) :
      Evaluates E M scope (.list (.atom "=" :: a :: b :: rest)) .bool
        (adjacentValue (fun x y => decide (x = y)) values)
  | distinct {scope : Scope M} {sort : SortCode String}
      (a b : Expr) (rest : List Expr) (values : List (M.carriers.value sort))
      (operands : OperandsEvaluate E M scope sort (a :: b :: rest) values) :
      Evaluates E M scope (.list (.atom "distinct" :: a :: b :: rest)) .bool
        (distinctValue values)
  | equality {scope : Scope M} {a b : Expr} {sort : SortCode String}
      {x y : M.carriers.value sort}
      (left : Evaluates E M scope a sort x) (right : Evaluates E M scope b sort y) :
      Evaluates E M scope (.list [.atom "=", a, b]) .bool (decide (x = y))
  | ite {scope : Scope M} {c a b : Expr} {sort : SortCode String}
      {condition : Bool} {x y : M.carriers.value sort}
      (test : Evaluates E M scope c .bool condition)
      (left : Evaluates E M scope a sort x) (right : Evaluates E M scope b sort y) :
      Evaluates E M scope (.list [.atom "ite", c, a, b]) sort
        (if condition = true then x else y)
  | letExpr {scope values : Scope M} {bindings : List Expr} {body : Expr}
      {sort : SortCode String} {value : M.carriers.value sort}
      (nonempty : bindings ≠ [])
      (bindingsValue : BindingsEvaluate E M scope bindings values)
      (bodyValue : Evaluates E M (values ++ scope) body sort value) :
      Evaluates E M scope (.list [.atom "let", .list bindings, body]) sort value

/-- Declared function operands may have different sorts. Their semantic values
follow the declaration's exact profile, independently of term decoding. -/
inductive ArgumentsEvaluate (E : Environment) (M : Packaged.GlobalModel) :
    (scope : Scope M) → (inputs : List (SortCode String)) → List Expr →
      ((i : Fin inputs.length) → M.carriers.value (inputs.get i)) → Prop where
  | nil (scope : Scope M) :
      ArgumentsEvaluate E M scope [] [] (fun i => Fin.elim0 i)
  | cons {scope : Scope M} {input : SortCode String} {inputs : List (SortCode String)}
      {e : Expr} {es : List Expr} (x : M.carriers.value input)
      (xs : (i : Fin inputs.length) → M.carriers.value (inputs.get i))
      (head : Evaluates E M scope e input x)
      (tail : ArgumentsEvaluate E M scope inputs es xs) :
      ArgumentsEvaluate E M scope (input :: inputs) (e :: es) (Fin.cases x xs)

/-- Ordered operand evaluation is a mutual family so its positive recursive
occurrences do not depend on a nested relation parameter. -/
inductive OperandsEvaluate (E : Environment) (M : Packaged.GlobalModel) :
    (scope : Scope M) → (sort : SortCode String) →
      List Expr → List (M.carriers.value sort) → Prop where
  | nil (scope : Scope M) (sort : SortCode String) : OperandsEvaluate E M scope sort [] []
  | cons {scope : Scope M} {sort : SortCode String} {e : Expr}
      {value : M.carriers.value sort} {es : List Expr} {values : List (M.carriers.value sort)}
      (head : Evaluates E M scope e sort value)
      (tail : OperandsEvaluate E M scope sort es values) :
      OperandsEvaluate E M scope sort (e :: es) (value :: values)

/-- Parallel binding RHSs share the outer scope. Distinct, legal binding names
are checked independently of the elaborator; only the body sees their values. -/
inductive BindingsEvaluate (E : Environment) (M : Packaged.GlobalModel) :
    Scope M → List Expr → Scope M → Prop where
  | nil (scope : Scope M) : BindingsEvaluate E M scope [] []
  | cons {scope values : Scope M} {rest : List Expr} {e : Expr}
      (name : String) (value : Value M)
      (legal : simpleSymbol name = true)
      (unreserved : reserved.contains name = false)
      (fresh : values.any (fun pair => pair.1 == name) = false)
      (rhs : Evaluates E M scope e value.sort value.value)
      (tail : BindingsEvaluate E M scope rest values) :
      BindingsEvaluate E M scope (.list [.atom name, e] :: rest) ((name, value) :: values)
end

/-- Direct closed-assertion meaning makes no reference to a decoder result. -/
def Holds (E : Environment) (M : Packaged.GlobalModel) (expression : Expr) : Prop :=
  Evaluates E M [] expression .bool true

/-- The preservation obligation for a recursive decoder callback. This is a
property to prove, not a premise supplied by the parser or a satisfaction definition. -/
def Sound (E : Environment) (M : Packaged.GlobalModel) (scope : Scope M)
    (recur : Expr → Option (PackedTerm E)) : Prop :=
  ∀ e t, recur e = some t →
    Evaluates E M scope e t.sort ((M.reduct (Packaged.nameMap E)).eval t.term)

/-- Proof-side comparison with a semantic scope. This bridge is deliberately
separate from the direct semantics: source evaluation stores only carrier values. -/
noncomputable def interpretTerm {E : Environment} (M : Packaged.GlobalModel)
    (t : PackedTerm E) : Value M :=
  ⟨t.sort, (M.reduct (Packaged.nameMap E)).eval t.term⟩

noncomputable def interpretLocals {E : Environment} (M : Packaged.GlobalModel)
    (locals : Locals E) : Scope M :=
  locals.map (fun pair => (pair.1, interpretTerm M pair.2))

end Silmaril.Logic.Smt.Uflia.SExpr.Surface
