module

public import Silmaril.Formats.Dasl.Prolly.Root.Defs
public import Silmaril.Formats.Dasl.Prolly.Thms
public import Silmaril.Semantics.Naming.Thms
import Silmaril.Proofs.Formats.Dasl.ProllyRoot

public section

namespace Silmaril.Formats.Dasl.Prolly.RootProfile

open Silmaril.Semantics Silmaril.Semantics.Prolly

variable {Name Key Payload : Type} (profile : RootProfile Name Key Payload)

theorem admits_iff_serializes (tree : Semantics.Prolly.Tree Key Payload) (address : Block Name Key Payload → Name) :
    tree.Admits profile.nameBlock? address ↔ ∀ block ∈ blockOccurrences address tree.level tree.root,
      ∃ value bytes, (blockCodec profile.key profile.payload).encode? block = some value ∧
        profile.render? value = some bytes ∧ profile.hash? bytes = some (address block) :=
  Proofs.Formats.Dasl.ProllyRoot.admits_iff_serializes profile tree address

theorem byteObservations_hashCompatible {tree : Semantics.Prolly.Tree Key Payload}
    {address : Block Name Key Payload → Name} (admitted : tree.Admits profile.nameBlock? address) :
    Naming.PartialHashCompatible profile.hash? (profile.byteObservations tree address) :=
  Proofs.Formats.Dasl.ProllyRoot.byteObservations_hashCompatible profile admitted

/-- Naming is not publication. Given successful naming at every block, a binding
shallow extension exists exactly when the union of its observations with the base binds. -/
theorem stored_extension_iff (tree : Semantics.Prolly.Tree Key Payload) (address : Block Name Key Payload → Name)
    (base : Store Name) (admitted : tree.Admits profile.nameBlock? address) :
    (∃ extension, base.Subset extension ∧ extension.Binding ∧
      Stored (blockCodec profile.key profile.payload) address tree extension) ↔
    (base.union (profile.observations tree address)).Binding :=
  Proofs.Formats.Dasl.ProllyRoot.stored_extension_iff profile base admitted

variable [LinearOrder Key]

theorem roots_iff (map : OrderedMap Key Payload) (root : Name) :
    profile.Roots root map.lookup? ↔ profile.rootName? map = some root :=
  Proofs.Formats.Dasl.ProllyRoot.roots_iff profile map root

/-- Exactly one name iff bottom-up encoding succeeds with that root. The proof
compares all admitted addresses, not only a preferred address assignment. -/
theorem rootNames_eq_singleton_iff (map : OrderedMap Key Payload) (root : Name) :
    Naming.names profile.Roots map.lookup? = {root} ↔ profile.rootName? map = some root := by
  simp only [Naming.names_eq_singleton_iff, profile.roots_iff map]
  exact ⟨And.left, fun hit => ⟨hit, fun _ other => Option.some.inj (other.symm.trans hit)⟩⟩

end Silmaril.Formats.Dasl.Prolly.RootProfile
