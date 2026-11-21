module

public import Mathlib.Data.Set.Basic

/-! A finite or infinite observation of names and payloads. Binding is a property of
one relation, not an injectivity assumption on a real hash. -/

@[expose] public section

namespace Silmaril.Semantics.Naming

abbrev Relation (Name Payload : Type) := Name → Payload → Prop

variable {Name Payload Wire : Type}

def Binding (rel : Relation Name Payload) : Prop :=
  ∀ ⦃name left right⦄, rel name left → rel name right → left = right

def UniqueNames (rel : Relation Name Payload) : Prop := Binding (fun payload name => rel name payload)

/-- All known names for a payload, with no uniqueness or canonicality requirement. -/
def names (rel : Relation Name Payload) (payload : Payload) : Set Name :=
  { name | rel name payload }

def Subset (left right : Relation Name Payload) : Prop :=
  ∀ ⦃name payload⦄, left name payload → right name payload

def union (left right : Relation Name Payload) : Relation Name Payload :=
  fun name payload => left name payload ∨ right name payload

/-- Preserve all existing bindings; admit defaults only at names absent from the base. -/
def fillMissing (base defaults : Relation Name Payload) : Relation Name Payload :=
  fun name payload => base name payload ∨ ((¬ ∃ old, base name old) ∧ defaults name payload)

def inter (left right : Relation Name Payload) : Relation Name Payload :=
  fun name payload => left name payload ∧ right name payload

def collisions (rel : Relation Name Payload) : Set Name :=
  { name | ∃ left right, rel name left ∧ rel name right ∧ left ≠ right }

def graph (lookup : Name → Option Payload) : Relation Name Payload :=
  fun name payload => lookup name = some payload

/-- Logical lookup. Executable stores should instead supply their lookup and use `graph`. -/
noncomputable def Binding.lookup {rel : Relation Name Payload} (_ : Binding rel) : Name → Option Payload :=
  fun name => open Classical in
    if found : ∃ payload, rel name payload then some (Classical.choose found) else none

noncomputable def UniqueNames.lookup {rel : Relation Name Payload} (unique : UniqueNames rel) :
    Payload → Option Name := Binding.lookup unique

/-- Serialization may be partial or nondeterministic. No payload is silently substituted. -/
def push (rel : Relation Name Payload) (serializes : Payload → Wire → Prop) : Relation Name Wire :=
  fun name wire => ∃ payload, rel name payload ∧ serializes payload wire

/-- View names at a semantic type via a partial projection. Unprojectable payloads
contribute no names; this does not remove their bindings from the source. -/
def project (rel : Relation Name Payload) (decode : Payload → Option Wire) : Relation Name Wire :=
  push rel (graph decode)

/-- Names for equivalence classes, contributed by all named representatives. -/
def quotient (rel : Relation Name Payload) (equiv : Setoid Payload) :
    Relation Name (Quotient equiv) :=
  project rel (fun payload => some (Quotient.mk equiv payload))

/-- The graph of a partial naming function, in name-to-payload orientation.
Only `some name` contributes a pair; an undefined output contributes nothing. -/
def nameGraph (name? : Payload → Option Name) : Relation Name Payload :=
  fun name payload => graph name? payload name

/-- Compatibility is inclusion, not equality with the graph. It does not imply
binding or require an observation of every successful output. -/
def PartialHashCompatible (hash? : Wire → Option Name) (rel : Relation Name Wire) : Prop :=
  Subset rel (nameGraph hash?)

/-- Consistency with a fixed total byte hash, without any collision-freedom claim. -/
def HashCompatible (hash : Wire → Name) (rel : Relation Name Wire) : Prop :=
  ∀ ⦃name wire⦄, rel name wire → hash wire = name

/-- The object and raw stores have independent domains, even when the name type is shared. -/
structure Stores (Name Obj Blob : Type) where
  objects : Relation Name Obj
  blobs : Relation Name Blob

namespace Stores

variable {Obj Blob : Type}

def Binding (store : Stores Name Obj Blob) : Prop :=
  Naming.Binding store.objects ∧ Naming.Binding store.blobs

def Subset (left right : Stores Name Obj Blob) : Prop :=
  Naming.Subset left.objects right.objects ∧ Naming.Subset left.blobs right.blobs

def union (left right : Stores Name Obj Blob) : Stores Name Obj Blob :=
  ⟨Naming.union left.objects right.objects, Naming.union left.blobs right.blobs⟩

/-- The two stores can share a name type, but not a name in their actual domains. -/
def DisjointDomains (store : Stores Name Obj Blob) : Prop :=
  ∀ ⦃name obj blob⦄, store.objects name obj → ¬ store.blobs name blob

/-- Merge serialized objects with the raw store. Cross-domain collisions are not erased. -/
def flatten (store : Stores Name Obj Wire) (serializes : Obj → Wire → Prop) : Relation Name Wire :=
  Naming.union (push store.objects serializes) store.blobs

end Stores

/-- Track binding observations, identifying every collision with an absorbing top. -/
inductive Checked (Name Payload : Type) where
  | observed (rel : Relation Name Payload) (bound : Binding rel)
  | conflict

namespace Checked

noncomputable def classify (rel : Relation Name Payload) : Checked Name Payload :=
  open Classical in if bound : Binding rel then .observed rel bound else .conflict

noncomputable def merge : Checked Name Payload → Checked Name Payload → Checked Name Payload
  | .observed left _, .observed right _ => classify (union left right)
  | _, _ => .conflict

end Checked
end Silmaril.Semantics.Naming
