module

public import Silmaril.Formats.Dasl.Wire.Profile.Defs
public import Silmaril.Formats.Dasl.Encode.Thms

public section

namespace Silmaril.Formats.Dasl.Wire

open Silmaril.Semantics.Naming

variable {Name Source : Type} [DecidableEq Source]
variable {profile : Profile Name} {layout : Encode.TotalCodec Source (Shallow Name)}
variable {store : Relation Name ByteArray} {source : Source} {bytes : ByteArray} {name : Name}

theorem Profile.root_iff (encoded : (profile.codec layout).encode? source = some bytes) :
    profile.roots layout store name source ↔ profile.objectName name = true ∧ store name bytes := by
  simp [Profile.roots, Encode.codedNames, push, Encode.PartialCodec.rel, encoded]

theorem Profile.roots_binding (bound : Binding store) : Binding (profile.roots layout store) := by
  intro _ _ _ left right
  exact Encode.codedNames_binding bound (profile.codec layout) left.2 right.2

theorem Profile.read_root {read : Name → Option ByteArray}
    (root : profile.roots layout (graph read) name source) : profile.read? layout read name = some source := by
  obtain ⟨supported, _, present, encoded⟩ := root
  simpa [Profile.read?, supported, show read name = some _ from present] using
    (show profile.decode? layout _ = some source from (profile.codec layout).recovers encoded)

/-- Existence needs wire success and a supported, present computed root. Uniqueness
uses the fixed addressing function; binding (and hash injectivity) is not required. -/
theorem Profile.canonical_root {address : ByteArray → Name} (integrity : HashCompatible address store)
    (encoded : (profile.codec layout).encode? source = some bytes)
    (supported : profile.objectName (address bytes) = true) (present : store (address bytes) bytes) :
    ∃! name, profile.roots layout store name source :=
  ⟨address bytes, (Profile.root_iff encoded).mpr ⟨supported, present⟩,
    fun _ hit => (integrity ((Profile.root_iff encoded).mp hit).2).symm⟩

end Silmaril.Formats.Dasl.Wire
