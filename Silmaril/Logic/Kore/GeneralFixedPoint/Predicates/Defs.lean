module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Institution.Defs

/-! Cross-sort predicates over checked original source patterns. Leaf meanings
run the existing independent raw interpreter. Predicate truth uses set equality
and overlap directly; native encoding uses separately generated definedness
operations, not an assumed adequacy oracle. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Predicates
open CategoryTheory
open Algebraic.ManySorted (Signature)

structure Value (scope : Kore.Modules.Scope) (objects : Names) (sort : String) where
  fuel : Nat
  raw : RawPattern
  typed : Pattern scope [] objects sort
  accepted : Checking.elaborate scope fuel [] objects sort raw = some typed
  admitted : typed.admissible = true

def checkValue (scope : Kore.Modules.Scope) (objects : Names) (sort : String)
    (fuel : Nat) (raw : RawPattern) : Option (Value scope objects sort) :=
  match accepted : Checking.elaborate scope fuel [] objects sort raw with
  | none => none
  | some typed => if admitted : typed.admissible = true then
      some ⟨fuel, raw, typed, accepted, admitted⟩ else none

abbrev Env {scope : Kore.Modules.Scope}
    (M : Matching.GeneralFixedPoint.Model scope.signature) (objects : Names) :=
  ∀ i, M.carrier (context objects i)

def Value.denote {scope objects sort} (p : Value scope objects sort)
    (M : Matching.GeneralFixedPoint.Model scope.signature) (v : Env M objects) :
    Set (M.carrier sort) :=
  (Semantics.denote scope M p.fuel []
    (Semantics.interpret M objects (fun i => {v i})) sort p.raw).getD ∅

/-- Result-sort-polymorphic predicates. A result sort is never substituted into
operand sorts or object binders. Source equality compares whole denotation sets. -/
inductive Predicate (scope : Kore.Modules.Scope) : Names → Type where
  | top {objects} : Predicate scope objects
  | bottom {objects} : Predicate scope objects
  | equal {objects} (sort : String) (left right : Value scope objects sort) : Predicate scope objects
  | member {objects} (sort : String) (left right : Value scope objects sort) : Predicate scope objects
  | neg {objects} : Predicate scope objects → Predicate scope objects
  | conj {objects} : Predicate scope objects → Predicate scope objects → Predicate scope objects
  | disj {objects} : Predicate scope objects → Predicate scope objects → Predicate scope objects
  | ex {objects} (name bound : String) (body : Predicate scope ((name, bound) :: objects)) : Predicate scope objects

/-- This recursion is independent of native matching interpretation/lowering. -/
def Predicate.truth {scope} (M : Matching.GeneralFixedPoint.Model scope.signature) :
    {objects : Names} → Predicate scope objects → Env M objects → Prop
  | _, .top, _ => True
  | _, .bottom, _ => False
  | _, .equal _ p q, v => p.denote M v = q.denote M v
  | _, .member _ p q, v => (p.denote M v ∩ q.denote M v).Nonempty
  | _, .neg p, v => ¬ p.truth M v
  | _, .conj p q, v => p.truth M v ∧ q.truth M v
  | _, .disj p q, v => p.truth M v ∨ q.truth M v
  | _, .ex _ bound p, v => ∃ x : M.carrier bound, p.truth M (Fin.cases x v)

/-- Genuine uniform scheme semantics, for every inhabited result carrier,
without selecting finitely many result sorts during source checking. -/
def Predicate.denote {scope objects} (p : Predicate scope objects)
    (M : Matching.GeneralFixedPoint.Model scope.signature) (v : Env M objects)
    (Result : Type) : Set Result := {_x | p.truth M v}

def Predicate.Satisfies {scope objects} (p : Predicate scope objects)
    (M : Matching.GeneralFixedPoint.Model scope.signature) : Prop :=
  ∀ (Result : Type) [Nonempty Result] (v : Env M objects),
    ∀ x : Result, x ∈ p.denote M v Result

/-- Source symbols and a distinct generated definedness operation for every
actual operand/result sort pair. No generated symbol is made source-visible. -/
inductive Operation (scope : Kore.Modules.Scope) :
    (n : Nat) → (Fin n → String) → String → Type where
  | source {n inputs output} (op : scope.signature.operations n inputs output) :
      Operation scope n inputs output
  | ceil (input output : String) : Operation scope 1 (fun _ => input) output

def signature (scope : Kore.Modules.Scope) : Signature String := ⟨Operation scope⟩

def inclusion (scope : Kore.Modules.Scope) : scope.signature ⟶ signature scope where
  operations := Operation.source

/-- Independently fixed definedness graphs on every tuple. Ordinary operation
graphs and carriers are preserved literally. -/
def expand {scope} (M : Matching.GeneralFixedPoint.Model scope.signature) :
    Matching.GeneralFixedPoint.Model (signature scope) where
  carrier := M.carrier
  nonempty := M.nonempty
  operation := fun op args => match op with
    | .source op => M.operation op args
    | .ceil _ _ => Set.univ

abbrev NativePattern (scope : Kore.Modules.Scope) (objects : Names) (sort : String) :=
  Matching.GeneralFixedPoint.Pattern (signature scope) (context []) (context objects) sort

def Value.lower {scope objects sort} (p : Value scope objects sort) : NativePattern scope objects sort :=
  p.typed.map (inclusion scope)

def ceiling {scope objects input} (output : String) (p : NativePattern scope objects input) :
    NativePattern scope objects output := .app (.ceil input output) (fun _ => p)

def equal {scope objects input} (output : String)
    (p q : NativePattern scope objects input) : NativePattern scope objects output :=
  .neg (ceiling output ((Matching.GeneralFixedPoint.Pattern.conj p (.neg q)).disj (.conj (.neg p) q)))

def member {scope objects input} (output : String)
    (p q : NativePattern scope objects input) : NativePattern scope objects output :=
  ceiling output (.conj p q)

/-- Native lowering implements set equality via absence of a symmetric-difference
witness; pointwise iff would be incorrect for arbitrary matching patterns. -/
def Predicate.lower {scope} : {objects : Names} → Predicate scope objects →
    (result : String) → NativePattern scope objects result
  | _, .top, _ => .base Matching.FirstOrder.Pattern.top
  | _, .bottom, _ => .base Matching.FirstOrder.Pattern.bottom
  | _, .equal _ p q, result => Predicates.equal result p.lower q.lower
  | _, .member _ p q, result => Predicates.member result p.lower q.lower
  | _, .neg p, result => .neg (p.lower result)
  | _, .conj p q, result => .conj (p.lower result) (q.lower result)
  | _, .disj p q, result => (p.lower result).disj (q.lower result)
  | _, .ex _ bound p, result => .ex bound (p.lower result)

end Silmaril.Logic.Kore.GeneralFixedPoint.Predicates
