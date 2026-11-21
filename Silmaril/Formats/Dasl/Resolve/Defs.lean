module

public import Silmaril.Formats.Dasl.Defs
public import Silmaril.Semantics.Naming.Thms

/-! Store-relative semantics over already decoded objects. Missing wire and invalid wire
must be distinguished by a concrete store adapter, not by treating bad bytes as objects. -/

@[expose] public section

namespace Silmaril.Formats.Dasl

open Silmaril.Semantics.Naming

abbrev Store (Name : Type) := Stores Name (Shallow Name) ByteArray

variable {Name : Type}

def ShallowNames (store : Store Name) : Relation Name (Shallow Name) := store.objects

/-- Resolve the root and validate any asserted bindings. An edge may remain opaque even
when the store could resolve it, so this relation is not generally functional. -/
def PartialNames (store : Store Name) : Relation Name (Partial Name) :=
  fun name tree => store.objects name tree.shallow ∧ tree.bindings.Subset store

/-- Finite full expansion. The only recursion through a CAS edge follows the shallow
object stored under that name. There is no constructor for an unresolved target. -/
inductive Expands (store : Store Name) : Shallow Name → Named Name → Prop where
  | obj {name source target} : store.objects name source → Expands store source target →
      Expands store (.ref (.obj name)) (.obj name target)
  | blob {name payload} : store.blobs name payload →
      Expands store (.ref (.blob name)) (.blob name payload)
  | dict {keys : Finset String} {source : ↥keys → Shallow Name} {target : ↥keys → Named Name} :
      (∀ key, Expands store (source key) (target key)) → Expands store (.dict keys source) (.dict keys target)
  | list {len : Nat} {source : Fin len → Shallow Name} {target : Fin len → Named Name} :
      (∀ index, Expands store (source index) (target index)) → Expands store (.list len source) (.list len target)
  | i64 (bits) : Expands store (.i64 bits) (.i64 bits)
  | bytes (payload) : Expands store (.bytes payload) (.bytes payload)
  | string (text) : Expands store (.string text) (.string text)
  | bool (value) : Expands store (.bool value) (.bool value)
  | null : Expands store .null .null

def FullNames (store : Store Name) : Relation Name (Named Name) :=
  fun name value => ∃ source, store.objects name source ∧ Expands store source value

def ValueNames (store : Store Name) : Relation Name Value :=
  fun name value => ∃ target, FullNames store name target ∧ target.erase = value

/-- Direct dependencies are taken from the shallow object, including inline containers. -/
def Shallow.directLinks (tree : Shallow Name) : Set (Link Name) := Partial.links false tree.embed

def Depends (store : Store Name) (child parent : Name) : Prop :=
  ∃ source, store.objects parent source ∧ Link.obj child ∈ source.directLinks

/-- Object names reachable from the root, including the root. Raw links are leaves. -/
def Reachable (store : Store Name) (root : Name) : Name → Prop :=
  _root_.Relation.ReflTransGen (fun parent child => Depends store child parent) root

/-- Only links of reachable objects need to resolve. Unrelated blocks do not affect a root. -/
def ClosedBelow (store : Store Name) (root : Name) : Prop :=
  ∀ ⦃parent source⦄, Reachable store root parent → store.objects parent source →
    (∀ child, Link.obj child ∈ source.directLinks → ∃ target, store.objects child target) ∧
    (∀ child, Link.blob child ∈ source.directLinks → ∃ payload, store.blobs child payload)

/-- A sufficient closure condition for completion. No missing payload is defaulted, and no
wire payload appears as an object unless it has been decoded into this store. -/
def Closed (store : Store Name) : Prop :=
  ∀ ⦃parent source⦄, store.objects parent source →
    (∀ child, Link.obj child ∈ source.directLinks → ∃ target, store.objects child target) ∧
    (∀ child, Link.blob child ∈ source.directLinks → ∃ payload, store.blobs child payload)

/-- Nontrivial means at least one link was actually resolved, not just the root itself. -/
def PartialOnly (store : Store Name) (root : Name) : Prop :=
  (∃ tree, PartialNames store root tree ∧
    ((∃ name source, tree.bindings.objects name source) ∨ (∃ name payload, tree.bindings.blobs name payload))) ∧
  ¬ ∃ target, FullNames store root target

end Silmaril.Formats.Dasl
