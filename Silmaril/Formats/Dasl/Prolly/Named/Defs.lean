module

public import Silmaril.Formats.Dasl.Named.Defs
public import Silmaril.Formats.Dasl.Prolly.Root.Defs
public import Silmaril.Formats.Dasl.Prolly.Thms

@[expose] public section

namespace Silmaril.Formats.Dasl.Prolly

open Silmaril.Semantics Silmaril.Semantics.Prolly

variable {Name Key Payload : Type}

/-- A finite expansion of exactly this shallow spelling. In particular, a
known key name need not have such a witness. -/
def ExpansionReady (store : Store Name) (source : Shallow Name) : Prop :=
  ∃ value, CanName store value source

/-- Nonstructural requirements for full expansion of the Prolly representation.
Leaf keys and values, and branch separators, must each be expandable at their
selected encodings. The separate `Stored` predicate supplies structural blocks. -/
def NodeReady (key : Encode.TotalCodec Key (Shallow Name)) (payload : Encode.TotalCodec Payload (Shallow Name))
    (store : Store Name) : (level : Nat) → Node Key Payload level → Prop
  | 0, entries => ∀ row ∈ entries, ExpansionReady store (key.encode row.1) ∧ ExpansionReady store (payload.encode row.2)
  | level + 1, children => ∀ row ∈ children, ExpansionReady store (key.encode row.1) ∧ NodeReady key payload store level row.2

/-- Roots of the fixed layout/naming profile whose exact canonical encoding
has a finite full expansion in the supplied binding store. Structural storage
prevents a different child block at a selected name from witnessing validity. -/
def RootProfile.NamedRoots [LinearOrder Key] (profile : RootProfile Name Key Payload) (store : Store Name) :
    Naming.Relation Name (Key → Option Payload) := fun name lookup =>
  store.Binding ∧ ∃ (map : OrderedMap Key Payload) (address : Block Name Key Payload → Name),
    let tree := build profile.policy map
    (∀ key, map.lookup? key = lookup key) ∧ tree.Admits profile.nameBlock? address ∧ tree.rootName address = name ∧
    Stored (blockCodec profile.key profile.payload) address tree store ∧
    ∃ named, encodeBlock profile.key profile.payload (nodeBlock address tree.level tree.root) = some named.embed.shallow ∧
      FullNames store name named

end Silmaril.Formats.Dasl.Prolly
