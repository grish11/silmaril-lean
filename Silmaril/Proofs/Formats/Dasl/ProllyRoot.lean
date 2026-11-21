module

public import Silmaril.Formats.Dasl.Prolly.Root.Defs
public import Silmaril.Formats.Dasl.Prolly.Thms
public import Silmaril.Semantics.Naming.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.ProllyRoot

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.Prolly Silmaril.Semantics Silmaril.Semantics.Prolly

variable {Name Key Payload : Type} (profile : RootProfile Name Key Payload)
  {tree : Semantics.Prolly.Tree Key Payload} {address : Block Name Key Payload → Name}

theorem roots_iff [LinearOrder Key] (map : OrderedMap Key Payload) (root : Name) :
    profile.Roots root map.lookup? ↔ profile.rootName? map = some root := by
  rw [RootProfile.rootName?, Semantics.Prolly.Tree.rootName?_eq_some_iff]
  constructor
  · rintro ⟨other, address, same, admitted, named⟩
    cases OrderedMap.eq_of_lookup same
    exact ⟨address, admitted, named⟩
  · rintro ⟨address, admitted, named⟩
    exact ⟨map, address, fun _ => rfl, admitted, named⟩

theorem stored_extension_iff (base : Store Name) (admitted : tree.Admits profile.nameBlock? address) :
    (∃ extension, base.Subset extension ∧ extension.Binding ∧
      Stored (blockCodec profile.key profile.payload) address tree extension) ↔
    (base.union (profile.observations tree address)).Binding := by
  constructor
  · rintro ⟨extension, incl, binding, stored⟩
    apply binding.subset
    constructor
    · rintro name value (existing | ⟨block, ⟨rfl, occurs⟩, encoded⟩)
      · exact incl.1 existing
      · obtain ⟨actual, rendered, present⟩ := stored block occurs
        have same : value = actual := Option.some.inj (encoded.symm.trans (blockCodec_encode .. ▸ rendered))
        exact same.symm ▸ present
    · rintro name bytes (existing | impossible)
      · exact incl.2 existing
      · exact impossible.elim
  · intro binding
    refine ⟨base.union (profile.observations tree address), ⟨fun _ _ hit => .inl hit, fun _ _ hit => .inl hit⟩,
      binding, ?_⟩
    intro block occurs
    obtain ⟨bytes, serialized, _⟩ := Option.bind_eq_some_iff.mp (admitted block occurs)
    obtain ⟨value, encoded, _⟩ := Option.bind_eq_some_iff.mp serialized
    exact ⟨value, blockCodec_encode .. ▸ encoded, .inr ⟨block, ⟨rfl, occurs⟩, encoded⟩⟩

theorem admits_iff_serializes (tree : Semantics.Prolly.Tree Key Payload) (address : Block Name Key Payload → Name) :
    tree.Admits profile.nameBlock? address ↔ ∀ block ∈ blockOccurrences address tree.level tree.root,
      ∃ value bytes, (blockCodec profile.key profile.payload).encode? block = some value ∧
        profile.render? value = some bytes ∧ profile.hash? bytes = some (address block) := by
  simp only [Semantics.Prolly.Tree.Admits, RootProfile.nameBlock?, blockCodec_encode,
    Option.bind_eq_some_iff]
  constructor
  · intro success block hit
    obtain ⟨bytes, ⟨value, encoded, rendered⟩, named⟩ := success block hit
    exact ⟨value, bytes, encoded, rendered, named⟩
  · intro success block hit
    obtain ⟨value, bytes, encoded, rendered, named⟩ := success block hit
    exact ⟨bytes, ⟨value, encoded, rendered⟩, named⟩

theorem byteObservations_hashCompatible (admitted : tree.Admits profile.nameBlock? address) :
    Naming.PartialHashCompatible profile.hash? (profile.byteObservations tree address) := by
  rintro name bytes ⟨value, ⟨block, ⟨rfl, occurs⟩, encoded⟩, rendered⟩
  change encodeBlock profile.key profile.payload block = some value at encoded
  change profile.render? value = some bytes at rendered
  change profile.hash? bytes = some (address block)
  simpa [RootProfile.nameBlock?, encoded, rendered] using admitted block occurs

end Silmaril.Proofs.Formats.Dasl.ProllyRoot
