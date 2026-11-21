module

public import Silmaril.Formats.Dasl.LinkedSet.Defs
import Silmaril.Proofs.Formats.Dasl.LinkedSet

public section

namespace Silmaril.Formats.Dasl.LinkedSet

variable {Object Name : Type}

theorem key_injective {objects : Encode.PartialCodec Object ByteArray} {left right : Item Object} {key : Key}
    (first : key? objects left = some key) (second : key? objects right = some key) : left = right :=
  Proofs.Formats.Dasl.LinkedSet.key_injective first second

theorem cardinality_eq (layout : Layout Name) : cardinality layout = (keys layout).card := by
  simpa [keys, cardinality, Semantics.OrderedMap.keys] using
    (List.toFinset_card_of_nodup layout.keys_nodup).symm

variable [DecidableEq Name] {profile : Profile Object Name} {layout : Layout Name}

theorem decode_valid {value : Shallow Name} (hit : decode? profile value = some layout) : Valid profile layout :=
  Proofs.Formats.Dasl.LinkedSet.decode_valid hit

theorem recovers (valid : Valid profile layout) : decode? profile (encode layout) = some layout :=
  Proofs.Formats.Dasl.LinkedSet.recovers valid

theorem ofKeys_sound {requested : Finset Key} (hit : ofKeys? profile requested = some layout) :
    Valid profile layout ∧ keys layout = requested :=
  Proofs.Formats.Dasl.LinkedSet.ofKeys_sound hit

theorem ofKeys_complete (requested : Finset Key) (present : ∀ key ∈ requested, Supported profile key) :
    ∃ result, ofKeys? profile requested = some result :=
  Proofs.Formats.Dasl.LinkedSet.ofKeys_complete requested present

theorem normalize_sound {values : List (Item Object)} (hit : normalize? profile values = some layout) :
    Valid profile layout ∧ ∀ value, Member profile layout value ↔ value ∈ values :=
  Proofs.Formats.Dasl.LinkedSet.normalize_sound hit

theorem normalize_complete (values : List (Item Object))
    (ready : ∀ value ∈ values, ∃ key, key? profile.objects value = some key ∧ Supported profile key) :
    ∃ result, normalize? profile values = some result :=
  Proofs.Formats.Dasl.LinkedSet.normalize_complete values ready

theorem member_resolves (valid : Valid profile layout) (value : Item Object) :
    Member profile layout value ↔ ∃ key link, key? profile.objects value = some key ∧
      layout.lookup? key = some link ∧ profile.reader.resolve? link = some value :=
  Proofs.Formats.Dasl.LinkedSet.member_resolves valid value

/-- Names come from the profile's explicit preferred-link function. This does
not deduce name uniqueness from a store binding. -/
theorem eq_of_members {left right : Layout Name} (validLeft : Valid profile left) (validRight : Valid profile right)
    (same : ∀ value, Member profile left value ↔ Member profile right value) : left = right :=
  Proofs.Formats.Dasl.LinkedSet.eq_of_members validLeft validRight same

/-- Only supported keys participate: each selected link must resolve to a payload
whose successful canonical encoding has that key. -/
noncomputable def equiv (profile : Profile Object Name) :
    {layout : Layout Name // Valid profile layout} ≃
      {set : Finset Key // ∀ key ∈ set, Supported profile key} where
  toFun valid := ⟨keys valid.val, fun _ => Proofs.Formats.Dasl.LinkedSet.supported_of_valid valid.property⟩
  invFun set :=
    let existsLayout := ofKeys_complete set.val set.property
    ⟨existsLayout.choose, (ofKeys_sound existsLayout.choose_spec).1⟩
  left_inv valid := by
    have chosen := ofKeys_complete (profile := profile) (keys valid.val)
      (fun _ => Proofs.Formats.Dasl.LinkedSet.supported_of_valid valid.property)
    have spec := ofKeys_sound chosen.choose_spec
    exact Subtype.ext (Proofs.Formats.Dasl.LinkedSet.eq_of_keys spec.1 valid.property spec.2)
  right_inv set := Subtype.ext (ofKeys_sound (ofKeys_complete set.val set.property).choose_spec).2

end Silmaril.Formats.Dasl.LinkedSet
