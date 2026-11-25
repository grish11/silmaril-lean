module

public import Silmaril.Courses.Cambridge.L3.Metatheory.SubstitutionAlgebra
public import Silmaril.Semantics.ElgotMonads.Defs

/-! # Compositional may denotation for Cambridge L3 data and references

The denotation uses state over the powerset monad. Subexpressions compose by
bind. Expressions that inspect an entire record first collect its fields in
source order, threading intermediate stores. Allocation returns every fresh
address. Values use the course's original runtime representation, with
lambdas treated as opaque values in this fragment.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.L3.Denotation

open scoped Silmaril.Elgot.Nondet

/-- The syntax covered by the adequacy theorem. Values may also enter through
a store read. There is no observation of a function's behaviour in this fragment. -/
inductive Fragment : Expr → Prop where
  | value {e : Expr} : IsValue e → Fragment e
  | bvar (i : Nat) : Fragment (.bvar i)
  | letE {A : Ty} {value body : Expr} :
      Fragment value → Fragment body → Fragment (.letE A value body)
  | matchSum {e left right : Expr} {A B : Ty} :
      Fragment e → Fragment left → Fragment right → Fragment (.matchSum e A left B right)
  | binary {a b : Expr} {op : Op} : Fragment a → Fragment b → Fragment (.binary a op b)
  | cond {c a b : Expr} : Fragment c → Fragment a → Fragment b → Fragment (.cond c a b)
  | seq {a b : Expr} : Fragment a → Fragment b → Fragment (.seq a b)
  | loop {c b : Expr} : Fragment c → Fragment b → Fragment (.loop c b)
  | pair {a b : Expr} : Fragment a → Fragment b → Fragment (.pair a b)
  | fst {e : Expr} : Fragment e → Fragment (.fst e)
  | snd {e : Expr} : Fragment e → Fragment (.snd e)
  | inl {e : Expr} {T : Ty} : Fragment e → Fragment (.inl e T)
  | inr {e : Expr} {T : Ty} : Fragment e → Fragment (.inr e T)
  | record {labels : RecordLabels} {fields : labels.Index → Expr} :
      (∀ i, Fragment (fields i)) → Fragment (.record labels fields)
  | project {e : Expr} {label : Label} : Fragment e → Fragment (.project e label)
  | ref {e : Expr} : Fragment e → Fragment (.ref e)
  | deref {e : Expr} : Fragment e → Fragment (.deref e)
  | assign {lhs rhs : Expr} : Fragment lhs → Fragment rhs → Fragment (.assign lhs rhs)

abbrev Computation (A : Type) := StateT Store SetM A

def Returns {A : Type} (m : Computation A) (s : Store) (a : A) (t : Store) : Prop :=
  (a, t) ∈ₘ m.run s

def fail {A : Type} : Computation A := fun _ => (∅ : Set (A × Store))

def integer (n : Int) : Value := ⟨.int n, .int n⟩
def boolean (b : Bool) : Value := ⟨.bool b, .bool b⟩
def unit : Value := ⟨.skip, .skip⟩
def address (a : Loc) : Value := ⟨.loc a, .loc a⟩

def pair (a b : Value) : Value := ⟨.pair a.val b.val, .pair a.property b.property⟩
def injectLeft (v : Value) (T : Ty) : Value := ⟨.inl v.val T, .inl v.property⟩
def injectRight (v : Value) (T : Ty) : Value := ⟨.inr v.val T, .inr v.property⟩
def record (labels : RecordLabels) (values : labels.Index → Value) : Value :=
  ⟨.record labels (fun i => (values i).val), .record (fun i => (values i).property)⟩

def binary (op : Op) (a b : Value) : Computation Value :=
  match op, a.val, b.val with
  | .add, .int x, .int y => pure (integer (x + y))
  | .ge, .int x, .int y => pure (boolean (x ≥ y))
  | _, _, _ => fail

def branch (v : Value) (yes no : Computation Value) : Computation Value :=
  match v.val with
  | .bool true => yes
  | .bool false => no
  | _ => fail

def sequence (v : Value) (right : Computation Value) : Computation Value :=
  match v.val with
  | .skip => right
  | _ => fail

def first (v : Value) : Computation Value :=
  match v with
  | ⟨.pair left _, ready⟩ =>
      pure ⟨left, by cases ready with | pair vl _ => exact vl⟩
  | _ => fail

def second (v : Value) : Computation Value :=
  match v with
  | ⟨.pair _ right, ready⟩ =>
      pure ⟨right, by cases ready with | pair _ vr => exact vr⟩
  | _ => fail

def field (v : Value) (label : Label) : Computation Value := fun s =>
  match v with
  | ⟨.record labels fields, ready⟩ =>
      { outcome |
        ∃ i, labels.label i = label ∧
          outcome = (⟨fields i, by cases ready with | record all => exact all i⟩, s) }
  | _ => (∅ : Set (Value × Store))

/-- Collect the ordered field denotations. Boundary `i` carries the store
before field `i`, with the last boundary carrying the returned store. -/
def fields {n : Nat} (denotations : Fin n → Computation Value) :
    Computation (Fin n → Value) := fun s =>
  { outcome |
    ∃ stores : Fin (n + 1) → Store,
      stores 0 = s ∧ stores (Fin.last n) = outcome.2 ∧
      ∀ i, Returns (denotations i) (stores i.castSucc) (outcome.1 i) (stores i.succ) }

def allocate (v : Value) : Computation Value := fun s =>
  { outcome | ∃ a, a ∉ s ∧ outcome = (address a, s.insert a v) }

def read (v : Value) : Computation Value := fun s =>
  match v.val with
  | .loc a => { outcome | s.lookup a = some outcome.1 ∧ outcome.2 = s }
  | _ => (∅ : Set (Value × Store))

def write (lhs rhs : Value) : Computation Value := fun s =>
  match lhs.val with
  | .loc a => { outcome | a ∈ s ∧ outcome = (unit, s.insert a rhs) }
  | _ => (∅ : Set (Value × Store))

/-- The direct rules evaluate the right operand of assignment after the
left operand produces a location. -/
def assign (lhs : Value) (rhs : Computation Value) : Computation Value :=
  match lhs.val with
  | .loc _ => rhs >>= write lhs
  | _ => fail

/-- An Elgot iteration exits when its Boolean test is false and continues
after a true test and a unit result from the body. -/
def whileBody (test body : Computation Value) (_ : Unit) : Computation (Value ⊕ Unit) :=
  fun s =>
    { outcome |
      (outcome.1 = .inl unit ∧ Returns test s (boolean false) outcome.2) ∨
      (outcome.1 = .inr () ∧
        ∃ middle, Returns test s (boolean true) middle ∧ Returns body middle unit outcome.2) }

def whileLoop (test body : Computation Value) : Computation Value :=
  Silmaril.Elgot.iter (whileBody test body) ()

/-- An open index remains a variable when quoting an opaque function value.
Looking up an open index as an expression has no return. -/
inductive Binding where
  | index (index : Nat)
  | value (value : Value)

abbrev Environment := Nat → Binding

def Binding.expr : Binding → Expr
  | .index i => .bvar i
  | .value v => v.val

def Binding.denote : Binding → Computation Value
  | .index _ => fail
  | .value v => pure v

def Environment.empty : Environment := Binding.index

def Environment.substitution (env : Environment) : Nat → Expr :=
  fun i => (env i).expr

def Environment.closeValue (env : Environment) (v : Value) : Value :=
  ⟨v.val.subst env.substitution, v.property.subst env.substitution⟩

def Environment.extend (env : Environment) (v : Value) : Environment
  | 0 => .value v
  | i + 1 => env i

def Binding.shift : Binding → Binding
  | .index i => .index (i + 1)
  | .value v => .value ⟨v.val.rename Nat.succ, v.property.rename Nat.succ⟩

def Environment.lift (env : Environment) : Environment
  | 0 => .index 0
  | i + 1 => (env i).shift

def Environment.compose (inner outer : Environment) : Environment := fun i =>
  match inner i with
  | .index j => outer j
  | .value v => .value (outer.closeValue v)

def splitSum (v : Value) (left right : Value → Computation Value) : Computation Value :=
  match v with
  | ⟨.inl e _, h⟩ => left ⟨e, by cases h with | inl ready => exact ready⟩
  | ⟨.inr e _, h⟩ => right ⟨e, by cases h with | inr ready => exact ready⟩
  | _ => fail

/-- Structural interpretation of the original L3 expression. `Fragment`
specifies the supported expressions in the correspondence theorems. -/
def denoteWith (env : Environment) : Expr → Computation Value
  | .int n => pure (integer n)
  | .bool b => pure (boolean b)
  | .skip => pure unit
  | .loc a => pure (address a)
  | .bvar i => (env i).denote
  | .lam A body => pure (env.closeValue ⟨.lam A body, .lam A body⟩)
  | .binary a op b => denoteWith env a >>= fun v => denoteWith env b >>= binary op v
  | .cond c a b =>
      denoteWith env c >>= fun v => branch v (denoteWith env a) (denoteWith env b)
  | .seq a b => denoteWith env a >>= fun v => sequence v (denoteWith env b)
  | .loop c b => whileLoop (denoteWith env c) (denoteWith env b)
  | .pair a b => denoteWith env a >>= fun v => denoteWith env b >>= fun w => pure (pair v w)
  | .fst e => denoteWith env e >>= first
  | .snd e => denoteWith env e >>= second
  | .inl e T => denoteWith env e >>= fun v => pure (injectLeft v T)
  | .inr e T => denoteWith env e >>= fun v => pure (injectRight v T)
  | .record labels es =>
      fields (fun i => denoteWith env (es i)) >>= fun vs => pure (record labels vs)
  | .project e label => denoteWith env e >>= fun v => field v label
  | .ref e => denoteWith env e >>= allocate
  | .deref e => denoteWith env e >>= read
  | .assign lhs rhs =>
      denoteWith env lhs >>= fun v => assign v (denoteWith env rhs)
  | .letE _ value body =>
      denoteWith env value >>= fun v => denoteWith (env.extend v) body
  | .matchSum e _ left _ right =>
      denoteWith env e >>= fun v => splitSum v
        (fun argument => denoteWith (env.extend argument) left)
        (fun argument => denoteWith (env.extend argument) right)
  | _ => fail
termination_by structural e => e

/-- Closed-source interpretation. -/
def denote (e : Expr) : Computation Value := denoteWith Environment.empty e

/-- Data observations are indexed by the original L3 type, retaining the
labels and types of all record fields. -/
inductive DataType : Ty → Type where
  | int : DataType .int
  | bool : DataType .bool
  | unit : DataType .unit
  | prod {A B : Ty} (left : DataType A) (right : DataType B) : DataType (.prod A B)
  | sum {A B : Ty} (left : DataType A) (right : DataType B) : DataType (.sum A B)
  | record {labels : RecordLabels} {types : labels.Index → Ty}
      (fields : ∀ i, DataType (types i)) : DataType (.record labels types)

abbrev DataType.Result {T : Ty} : DataType T → Type
  | .int => Int
  | .bool => Bool
  | .unit => Unit
  | .prod a b => a.Result × b.Result
  | .sum a b => a.Result ⊕ b.Result
  | .record fs => ∀ i, (fs i).Result
termination_by structural shape => shape

def DataType.value {T : Ty} : (shape : DataType T) → shape.Result → Value
  | .int, n => integer n
  | .bool, b => boolean b
  | .unit, _ => Denotation.unit
  | .prod a b, result =>
      let result : a.Result × b.Result := result
      pair (a.value result.1) (b.value result.2)
  | @DataType.sum A B a b, result =>
      let result : a.Result ⊕ b.Result := result
      match result with
      | .inl left => injectLeft (a.value left) (.sum A B)
      | .inr right => injectRight (b.value right) (.sum A B)
  | @DataType.record labels _ fs, xs => Denotation.record labels (fun i => (fs i).value (xs i))
termination_by structural shape _ => shape

/-- Observe a typed data result while retaining its final store. -/
def DataType.Observes {T : Ty} (shape : DataType T) (e : Expr) (s : Store)
    (result : shape.Result) (t : Store) : Prop :=
  Returns (denote e) s (shape.value result) t

end Silmaril.Courses.Cambridge.L3.Denotation
