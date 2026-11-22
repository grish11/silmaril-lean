module

public import Silmaril.Formats.Dasl.NameLinkSet.Compatibility.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.NameLinkSet.Compatibility

open Silmaril.Formats.Dasl Silmaril.Formats.Dasl.NameLinkSet
open Silmaril.Semantics (OrderedMap)

variable {Name Object : Type}

private theorem encode_tagged (link : Link Name) : mixedKey.encode (taggedKey link) = link := by
  cases link <;> rfl

private theorem tagged_encode (key : MixedKey Name) : taggedKey (mixedKey.encode key) = key := by
  cases key <;> rfl

variable [LinearOrder Name]

theorem reindex_contains (layout : LinkedSet.Layout Name) (link : Link Name) :
    (index (ofContentLayout layout)).contains (taggedKey link) = true ↔
      ∃ key, layout.lookup? key = some link := by
  rw [contains_iff, ofContentLayout, normalize_names, List.mem_toFinset]
  constructor
  · intro present
    obtain ⟨⟨key, stored⟩, entry, same⟩ := List.mem_map.mp present
    have equal : stored = link := by simpa [encode_tagged] using congrArg mixedKey.encode same
    exact ⟨key, layout.lookup_eq_some_iff.mpr (equal ▸ entry)⟩
  · rintro ⟨key, hit⟩
    exact List.mem_map_of_mem (layout.lookup_eq_some_iff.mp hit)

theorem reindex_member {profile : LinkedSet.Profile Object Name} {layout : LinkedSet.Layout Name}
    (valid : LinkedSet.Valid profile layout) (value : LinkedSet.Item Object) :
    value ∈ contents mixedKey (readerRelation profile.reader) (ofContentLayout layout) ↔
      LinkedSet.Member profile layout value := by
  rw [LinkedSet.member_resolves valid]
  constructor
  · rintro ⟨name, present, read⟩
    let link := mixedKey.encode name
    have indexed := (contains_iff (ofContentLayout layout) name).mpr present
    have linked : (index (ofContentLayout layout)).contains (taggedKey link) = true := by
      simpa [link, tagged_encode] using indexed
    obtain ⟨key, hit⟩ := (reindex_contains layout link).mp linked
    have accepted := valid (key, link) (layout.lookup_eq_some_iff.mp hit)
    change profile.reader.resolve? link = some value at read
    have encoded : LinkedSet.key? profile.objects value = some key := by
      cases result : LinkedSet.key? profile.objects value with
      | none => simp [LinkedSet.Profile.entry?, read, result] at accepted
      | some actual =>
        simp only [LinkedSet.Profile.entry?, read, result, Option.bind_some] at accepted
        split at accepted
        · exact congrArg (some ∘ Prod.fst) (Option.some.inj accepted)
        · cases accepted
    exact ⟨key, link, encoded, hit, read⟩
  · rintro ⟨key, link, _, hit, read⟩
    have indexed := (reindex_contains layout link).mpr ⟨key, hit⟩
    exact ⟨taggedKey link, (contains_iff _ _).mp indexed, by simpa [readerRelation, encode_tagged] using read⟩

theorem reindex_contents_eq_iff {profile : LinkedSet.Profile Object Name} {left right : LinkedSet.Layout Name}
    (validLeft : LinkedSet.Valid profile left) (validRight : LinkedSet.Valid profile right) :
    contents mixedKey (readerRelation profile.reader) (ofContentLayout left) =
      contents mixedKey (readerRelation profile.reader) (ofContentLayout right) ↔ left = right := by
  constructor
  · intro same
    apply LinkedSet.eq_of_members validLeft validRight
    intro value
    rw [← reindex_member validLeft, ← reindex_member validRight, same]
  · rintro rfl
    rfl

theorem singleton_contents (reader : LinkedSet.Reader Object Name) (link : Link Name) :
    contents mixedKey (readerRelation reader) (normalize [taggedKey link]) =
      { value | reader.resolve? link = some value } := by
  ext value
  simp [contents, normalize_names, readerRelation, encode_tagged]

end Silmaril.Proofs.Formats.Dasl.NameLinkSet.Compatibility
