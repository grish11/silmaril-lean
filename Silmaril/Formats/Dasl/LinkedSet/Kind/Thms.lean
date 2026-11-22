module

public import Silmaril.Formats.Dasl.LinkedSet.Kind.Defs

public section

namespace Silmaril.Formats.Dasl.LinkedSet

variable {Name Object : Type}

theorem resolve_mixed (reader : Reader Object Name) (kind : Kind) (link : TypedLink Name kind) :
    reader.resolveTyped? (TypedLink.toMixed kind link) = reader.resolveTyped? link := rfl

theorem encode_mixed (kind : Kind) (link : TypedLink Name kind) :
    (typedLink .mixed).encode (TypedLink.toMixed kind link) = (typedLink kind).encode link := rfl

theorem resolve_object (reader : Reader Object Name) (link : TypedLink Name .objects) :
    ∃ name, link.val = .obj name ∧ reader.resolveTyped? link = (reader.object? name).map Item.object := by
  obtain ⟨raw, allowed⟩ := link
  cases raw with
  | obj name => exact ⟨name, rfl, rfl⟩
  | blob _ => cases allowed

theorem resolve_blob (reader : Reader Object Name) (link : TypedLink Name .blobs) :
    ∃ name, link.val = .blob name ∧ reader.resolveTyped? link = (reader.blob? name).map Item.blob := by
  obtain ⟨raw, allowed⟩ := link
  cases raw with
  | obj _ => cases allowed
  | blob name => exact ⟨name, rfl, rfl⟩

theorem encode_mixed_positions (kind : Kind) (links : List (TypedLink Name kind)) :
    (links.map (TypedLink.toMixed kind)).map (typedLink .mixed).encode = links.map (typedLink kind).encode := by
  simp only [List.map_map, Function.comp_def, encode_mixed]

theorem encode_mixed_layout (kind : Kind) (layout : TypedLayout Name kind) :
    encodeTyped (TypedLayout.toMixed kind layout) = encodeTyped layout := rfl

theorem decodeTyped_recovers [DecidableEq Name] {profile : Profile Object Name} {kind : Kind}
    (layout : TypedLayout Name kind) (valid : Valid profile layout.val) :
    decodeTyped? profile kind (encodeTyped layout) = some layout := by
  simp [decodeTyped?, encodeTyped, recovers valid, narrow?, layout.property]

end Silmaril.Formats.Dasl.LinkedSet
