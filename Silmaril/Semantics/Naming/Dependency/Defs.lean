module

public import Silmaril.Semantics.Naming.Defs

@[expose] public section

namespace Silmaril.Semantics.Naming

/-- The left lane names objects; the right lane names terminal blobs. -/
abbrev Child (Name : Type) := Sum Name Name

/-- `children` can be specified by a relation, or by membership in an enumeration.
Bindings and child enumeration are independent inputs. -/
structure Dependency (Name Obj Blob : Type) where
  store : Stores Name Obj Blob
  children : Obj → Set (Child Name)

namespace Dependency

variable {Name Obj Blob : Type}

def Requests (graph : Dependency Name Obj Blob) (child : Child Name) (parent : Name) : Prop :=
  ∃ object, graph.store.objects parent object ∧ child ∈ graph.children object

/-- An edge is a request from a bound object, even when its child is missing.
In particular, only objects have outgoing requests. -/
def Edge (graph : Dependency Name Obj Blob) (child : Child Name) : Child Name → Prop
  | .inl parent => graph.Requests child parent
  | .inr _ => False

def Depends (graph : Dependency Name Obj Blob) (child parent : Name) : Prop :=
  graph.Requests (.inl child) parent

def Reachable (graph : Dependency Name Obj Blob) (root : Name) : Name → Prop :=
  _root_.Relation.ReflTransGen (fun parent child => graph.Depends child parent) root

def Available (graph : Dependency Name Obj Blob) : Child Name → Prop
  | .inl name => ∃ object, graph.store.objects name object
  | .inr name => ∃ blob, graph.store.blobs name blob

/-- Root presence plus availability of every request from a reachable object. -/
def CompleteBelow (graph : Dependency Name Obj Blob) (root : Name) : Prop :=
  graph.Available (.inl root) ∧ ∀ ⦃parent child⦄,
    graph.Reachable root parent → graph.Requests child parent → graph.Available child

def AcyclicBelow (graph : Dependency Name Obj Blob) (root : Name) : Prop :=
  ∀ ⦃name⦄, graph.Reachable root name → ¬ _root_.Relation.TransGen graph.Depends name name

/-- `Bounded edge fuel root` permits at most `fuel` object-to-object steps.
Reading a terminal blob is not an object dependency step. -/
def Bounded {Name : Type} (edge : Name → Name → Prop) : Nat → Name → Prop
  | 0, parent => ∀ ⦃child⦄, ¬ edge child parent
  | fuel + 1, parent => ∀ ⦃child⦄, edge child parent → Bounded edge fuel child

end Dependency
end Silmaril.Semantics.Naming
