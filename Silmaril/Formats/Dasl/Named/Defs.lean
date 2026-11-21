module

public import Silmaril.Formats.Dasl.Resolve.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl

variable {Name : Type}

/-- The least observation of a fully expanded tree. The object component compares
shallow targets; the blob component compares bytes. -/
abbrev Named.observed (tree : Named Name) : Store Name := tree.embed.bindings

def Named.AdmittedBy (tree : Named Name) (store : Store Name) : Prop :=
  tree.observed.Subset store

def Named.Coherent (tree : Named Name) : Prop := tree.observed.Binding

def Named.Compatible (tree : Named Name) (store : Store Name) : Prop :=
  store.Binding ∧ tree.AdmittedBy store

abbrev Named.Valid (store : Store Name) := {tree : Named Name // tree.Compatible store}

/-- One name has two unequal witnesses in the same lane. Object/blob roles are
tagged; disjoint untagged name domains are a separate profile condition. -/
def Named.Conflict (tree : Named Name) : Prop :=
  (∃ name left right, tree.observed.objects name left ∧ tree.observed.objects name right ∧ left ≠ right) ∨
  (∃ name left right, tree.observed.blobs name left ∧ tree.observed.blobs name right ∧ left ≠ right)

/-- Local, bottom-up naming choices for a nameless value, recording the shallow result.
At an object edge the store must admit the shallow target produced by the child choices.
Every inline child must have choices and a blob edge requires its exact bytes. -/
inductive CanName (store : Store Name) : Value → Shallow Name → Prop where
  | obj {name child target} : CanName store child target → store.objects name target →
      CanName store (Value.obj child) (.ref (.obj name))
  | blob {name bytes} : store.blobs name bytes → CanName store (Value.blob bytes) (.ref (.blob name))
  | dict {keys : Finset String} {children : ↥keys → Value} {targets : ↥keys → Shallow Name} :
      (∀ key, CanName store (children key) (targets key)) → CanName store (.dict keys children) (.dict keys targets)
  | list {len : Nat} {children : Fin len → Value} {targets : Fin len → Shallow Name} :
      (∀ index, CanName store (children index) (targets index)) → CanName store (.list len children) (.list len targets)
  | i64 (bits : UInt64) : CanName store (.i64 bits) (.i64 bits)
  | bytes (bytes : ByteArray) : CanName store (.bytes bytes) (.bytes bytes)
  | string (text : String) : CanName store (.string text) (.string text)
  | bool (value : Bool) : CanName store (.bool value) (.bool value)
  | null : CanName store .null .null

end Silmaril.Formats.Dasl
