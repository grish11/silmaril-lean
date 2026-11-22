module

public import Silmaril.Formats.Dasl.Congruence.Witness.Defs
import Silmaril.Proofs.Formats.Dasl.Congruence.Witness

public section

namespace Silmaril.Formats.Dasl.CongruenceWitness

open Silmaril.Semantics Naming

variable {Name : Type}

theorem decodedStore_binding (profile : Wire.Profile Name) (blobName : Name → Bool)
    {wire : Stores Name ByteArray ByteArray} (bound : wire.Binding) : (decodedStore profile blobName wire).Binding :=
  ⟨(bound.1.project profile.parse?).subset (fun _ _ hit => hit.2), bound.2.subset (fun _ _ hit => hit.2)⟩

theorem decodedStore_mono (profile : Wire.Profile Name) (blobName : Name → Bool)
    {wire extended : Stores Name ByteArray ByteArray} (incl : wire.Subset extended) :
    (decodedStore profile blobName wire).Subset (decodedStore profile blobName extended) :=
  ⟨fun _ _ ⟨guard, bytes, raw, decoded⟩ => ⟨guard, bytes, incl.1 raw, decoded⟩,
    fun _ _ ⟨guard, raw⟩ => ⟨guard, incl.2 raw⟩⟩

theorem decodedStore_compatible (profile : Wire.Profile Name) (blobName : Name → Bool)
    {wire extended : Stores Name ByteArray ByteArray} (incl : wire.Subset extended) (bound : extended.Binding) :
    Compatible (decodedStore profile blobName wire) (decodedStore profile blobName extended) :=
  ⟨decodedStore_mono profile blobName incl, decodedStore_binding profile blobName bound⟩

variable [LinearOrder Name] {certificate : Certificate Name} {base extended : Store Name}

theorem Certificate.Valid.mono {allowed : Link Name → Prop}
    (valid : certificate.Valid base allowed) (incl : base.Subset extended) : certificate.Valid extended allowed :=
  Proofs.Formats.Dasl.CongruenceWitness.valid_mono valid incl

theorem Certificate.Valid.refines_full {allowed : Link Name → Prop} {name : Name}
    {observed : Partial Name} {full : Named Name} (valid : certificate.Valid base allowed)
    (compatible : Compatible base extended) (hit : certificate.views.lookup? name = some observed)
    (complete : FullNames extended name full) : Extends observed full.embed :=
  complete.refines compatible.2 ((valid.mono compatible.1).1 hit).1

theorem Certificate.seed_le {model : PER (Partial Name)} (checked : certificate.CheckedBy model) :
    certificate.seed ≤ model := sInf_le checked

theorem Certificate.named_of_edge {enabled : Tree.Shape (Link Name) Name → Prop} {left right : Name}
    {first second : Partial Name} (hl : certificate.views.lookup? left = some first)
    (hr : certificate.views.lookup? right = some second) (edge : certificate.edges first second) :
    (certificate.named enabled).rel left right :=
  ⟨first, second, hl, hr, (Tree.constructors enabled).le_generated _ fun target => target.property edge⟩

theorem Certificate.named_dom {enabled : Tree.Shape (Link Name) Name → Prop} (name : Name) :
    (certificate.named enabled).Dom name ↔ (certificate.views.lookup? name).isSome :=
  ⟨fun ⟨tree, _, hit, _, _⟩ => Option.isSome_iff_exists.mpr ⟨tree, hit⟩,
    fun known => let ⟨_, hit⟩ := Option.isSome_iff_exists.mp known; named_of_edge hit hit (.inl ⟨name, hit, rfl⟩)⟩

theorem Certificate.generated_sound {enabled : Tree.Shape (Link Name) Name → Prop} {model : PER (Partial Name)}
    (checked : certificate.CheckedBy model) (closed : (Tree.constructors enabled).Closed model) :
    certificate.generated enabled ≤ model := (Tree.constructors enabled).generated_le (seed_le checked) closed

theorem Certificate.generated_closed (certificate : Certificate Name) (enabled : Tree.Shape (Link Name) Name → Prop) :
    (Tree.constructors enabled).Closed (certificate.generated enabled) :=
  (Tree.constructors enabled).generated_closed certificate.seed

theorem Certificate.named_sound {enabled : Tree.Shape (Link Name) Name → Prop} {model : PER (Partial Name)}
    (checked : certificate.CheckedBy model) (closed : (Tree.constructors enabled).Closed model) :
    certificate.named enabled ≤ model.decodePull certificate.views.lookup? :=
  fun _ _ ⟨first, second, left, right, related⟩ => ⟨first, second, left, right, generated_sound checked closed related⟩

/-- Each endpoint has unchanged store evidence, and the inferred equality is
sound in every compatible extension whose closed model checks the finite edges. -/
theorem Certificate.sound_in_extensions {allowed : Link Name → Prop} {enabled : Tree.Shape (Link Name) Name → Prop}
    (valid : certificate.Valid base allowed) (model : Store Name → PER (Partial Name))
    (checks : ∀ extension, Compatible base extension → certificate.CheckedBy (model extension))
    (closed : ∀ extension, Compatible base extension → (Tree.constructors enabled).Closed (model extension)) :
    ∀ extension, Compatible base extension → certificate.Valid extension allowed ∧
      certificate.named enabled ≤ (model extension).decodePull certificate.views.lookup? :=
  fun extension compatible => ⟨valid.mono compatible.1, named_sound (checks extension compatible) (closed extension compatible)⟩

end Silmaril.Formats.Dasl.CongruenceWitness
