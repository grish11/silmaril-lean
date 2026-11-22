module

public import Silmaril.Formats.PER.Thms
public import Silmaril.Semantics.Naming.Defs

@[expose] public section

namespace Silmaril.Formats.PER.EGraph

variable {Name : Type} {size : Nat}

/-- A term node uses term IDs; an e-node uses class IDs. Children are positional. -/
structure Node (Name Id : Type) where
  label : Name
  children : List Id
  deriving DecidableEq

def Ordered (terms : Array (Node Name Nat)) : Prop :=
  ∀ id : Fin terms.size, ∀ child ∈ terms[id].children, child < id.val

instance (terms : Array (Node Name Nat)) : Decidable (Ordered terms) :=
  inferInstanceAs (Decidable (∀ id : Fin terms.size, ∀ child ∈ terms[id].children, child < id.val))

abbrev Dag (Name : Type) := { terms : Array (Node Name Nat) // Ordered terms }

def checkDag? (terms : Array (Node Name Nat)) : Option (Dag Name) :=
  if ordered : Ordered terms then some ⟨terms, ordered⟩ else none

abbrev Dag.Id (dag : Dag Name) := Fin dag.val.size

def Dag.children (dag : Dag Name) (id : dag.Id) : List dag.Id :=
  dag.val[id].children.attach.map fun child =>
    ⟨child.val, (dag.property id child.val child.property).trans id.isLt⟩

/-- A finite snapshot boundary. Implementations can supply their current class
function, without exposing a parent array or assuming a reduction strategy. -/
structure Partition (size : Nat) where
  count : Nat
  classOf : Fin size → Fin count

def termId? (size id : Nat) : Option (Fin size) :=
  if valid : id < size then some ⟨id, valid⟩ else none

def Partition.lookup (part : Partition size) (id : Nat) : Option (Fin part.count) :=
  (termId? size id).map part.classOf

def Partition.per (part : Partition size) : PER (Fin size) := PER.kernel part.classOf

def Partition.rawPER (part : Partition size) : PER Nat := PER.ofDecoder part.lookup

/-- Names are supplied by an abstract relation on term IDs. Out-of-range IDs
contribute no names. This requires neither a hash nor unique names. -/
def Partition.classNames {Key : Type} (part : Partition size)
    (names : Semantics.Naming.Relation Key Nat) : Semantics.Naming.Relation Key (Fin part.count) :=
  Semantics.Naming.project names part.lookup

def Dag.signature (dag : Dag Name) (part : Partition dag.val.size) (id : dag.Id) :
    Node Name (Fin part.count) := ⟨dag.val[id].label, (dag.children id).map part.classOf⟩

/-- The signature-table invariant, without committing to a table or hash. -/
def Dag.Rebuilt (dag : Dag Name) (part : Partition dag.val.size) : Prop :=
  ∀ left right, dag.signature part left = dag.signature part right → part.classOf left = part.classOf right

instance [DecidableEq Name] (dag : Dag Name) (part : Partition dag.val.size) : Decidable (dag.Rebuilt part) :=
  inferInstanceAs (Decidable (∀ left right, dag.signature part left = dag.signature part right →
    part.classOf left = part.classOf right))

/-- Congruence on witnessed term applications only. Invalid raw term IDs cannot
be used, and related children must match in order, including arity. -/
def Dag.Congruent (dag : Dag Name) (relation : PER dag.Id) : Prop :=
  ∀ left right : dag.Id, dag.val[left].label = dag.val[right].label →
    List.Forall₂ relation.rel (dag.children left) (dag.children right) → relation.rel left right

abbrev Seeds (size : Nat) := Fin size → Fin size → Bool

/-- A model has guarded reflexivity, PER symmetry and transitivity, asserted
seed equalities, and congruence for all observed applications in the DAG. -/
structure Model (dag : Dag Name) (seeds : Seeds dag.val.size) where
  per : PER dag.Id
  reflexive : ∀ id, per.Dom id
  asserts : ∀ left right, seeds left right = true → per.rel left right
  congruent : dag.Congruent per

/-- Equality justified in every model. The raw ID interpretation is restricted
to the finite DAG; this is not closure over missing term applications. -/
def Dag.generated (dag : Dag Name) (seeds : Seeds dag.val.size) : PER dag.Id where
  rel left right := ∀ model : Model dag seeds, model.per.rel left right
  laws.symm := by intro left right same model; exact model.per.laws.symm (same model)
  laws.trans := by intro left middle right first second model; exact model.per.laws.trans (first model) (second model)

def Dag.Sound (dag : Dag Name) (seeds : Seeds dag.val.size) (part : Partition dag.val.size) : Prop :=
  part.per ≤ dag.generated seeds

/-- A proposed snapshot must merge exactly these two old classes. Class IDs
may change; support is unchanged and all other equivalences are preserved. -/
def Partition.IsMerge (before after : Partition size) (left right : Fin size) : Prop :=
  ∀ x y, after.classOf x = after.classOf y ↔ before.classOf x = before.classOf y ∨
    (before.classOf x = before.classOf left ∧ before.classOf y = before.classOf right) ∨
    (before.classOf x = before.classOf right ∧ before.classOf y = before.classOf left)

instance (before after : Partition size) (left right : Fin size) : Decidable (before.IsMerge after left right) :=
  inferInstanceAs (Decidable (∀ x y, after.classOf x = after.classOf y ↔ before.classOf x = before.classOf y ∨
    (before.classOf x = before.classOf left ∧ before.classOf y = before.classOf right) ∨
    (before.classOf x = before.classOf right ∧ before.classOf y = before.classOf left)))

inductive Reason where
  | seed
  | collision

def Dag.Allows (dag : Dag Name) (seeds : Seeds dag.val.size) (part : Partition dag.val.size)
    (left right : dag.Id) : Reason → Prop
  | .seed => seeds left right = true
  | .collision => dag.signature part left = dag.signature part right ∧ part.classOf left ≠ part.classOf right

instance [DecidableEq Name] (dag : Dag Name) (seeds : Seeds dag.val.size) (part : Partition dag.val.size)
    (left right : dag.Id) (reason : Reason) : Decidable (dag.Allows seeds part left right reason) :=
  match reason with
  | .seed => inferInstanceAs (Decidable (_ = true))
  | .collision => inferInstanceAs (Decidable (_ = _ ∧ _ ≠ _))

/-- Check one proposed seed merge or rebuild step. The caller supplies the
updated partition (for example from union-find); rejection leaves no result. -/
def Dag.merge? [DecidableEq Name] (dag : Dag Name) (seeds : Seeds dag.val.size)
    (before after : Partition dag.val.size) (left right : dag.Id) (reason : Reason) :
    Option { result : Partition dag.val.size //
      dag.Allows seeds before left right reason ∧ before.IsMerge result left right } :=
  if valid : dag.Allows seeds before left right reason ∧ before.IsMerge after left right then
    some ⟨after, valid⟩
  else none

end Silmaril.Formats.PER.EGraph
