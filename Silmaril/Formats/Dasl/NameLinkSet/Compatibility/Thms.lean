module

public import Silmaril.Formats.Dasl.NameLinkSet.Compatibility.Defs
import Silmaril.Proofs.Formats.Dasl.NameLinkSet.Compatibility

public section

namespace Silmaril.Formats.Dasl.NameLinkSet

variable {Name Object : Type} [LinearOrder Name]

theorem reindex_contains (layout : LinkedSet.Layout Name) (link : Link Name) :
    (index (ofContentLayout layout)).contains (taggedKey link) = true ↔
      ∃ key, layout.lookup? key = some link :=
  Proofs.Formats.Dasl.NameLinkSet.Compatibility.reindex_contains layout link

theorem reindex_member {profile : LinkedSet.Profile Object Name} {layout : LinkedSet.Layout Name}
    (valid : LinkedSet.Valid profile layout) (value : LinkedSet.Item Object) :
    value ∈ contents mixedKey (readerRelation profile.reader) (ofContentLayout layout) ↔
      LinkedSet.Member profile layout value :=
  Proofs.Formats.Dasl.NameLinkSet.Compatibility.reindex_member valid value

/-- A fixed valid content profile retains its preferred names and canonical keys.
Arbitrary name layouts with the same content image need not coincide. -/
theorem reindex_contents_eq_iff {profile : LinkedSet.Profile Object Name} {left right : LinkedSet.Layout Name}
    (validLeft : LinkedSet.Valid profile left) (validRight : LinkedSet.Valid profile right) :
    contents mixedKey (readerRelation profile.reader) (ofContentLayout left) =
      contents mixedKey (readerRelation profile.reader) (ofContentLayout right) ↔ left = right :=
  Proofs.Formats.Dasl.NameLinkSet.Compatibility.reindex_contents_eq_iff validLeft validRight

theorem reindex_eq_iff {profile : LinkedSet.Profile Object Name} {left right : LinkedSet.Layout Name}
    (validLeft : LinkedSet.Valid profile left) (validRight : LinkedSet.Valid profile right) :
    ofContentLayout left = ofContentLayout right ↔ left = right :=
  ⟨fun same => (reindex_contents_eq_iff validLeft validRight).mp
    (congrArg (contents mixedKey (readerRelation profile.reader)) same),
    congrArg ofContentLayout⟩

theorem reindex_normalize_member {profile : LinkedSet.Profile Object Name} {layout : LinkedSet.Layout Name}
    {input : List (LinkedSet.Item Object)} (hit : LinkedSet.normalize? profile input = some layout)
    (value : LinkedSet.Item Object) :
    value ∈ contents mixedKey (readerRelation profile.reader) (ofContentLayout layout) ↔ value ∈ input :=
  (reindex_member (LinkedSet.normalize_sound hit).1 value).trans ((LinkedSet.normalize_sound hit).2 value)

theorem singleton_contents (reader : LinkedSet.Reader Object Name) (link : Link Name) :
    contents mixedKey (readerRelation reader) (normalize [taggedKey link]) =
      { value | reader.resolve? link = some value } :=
  Proofs.Formats.Dasl.NameLinkSet.Compatibility.singleton_contents reader link

end Silmaril.Formats.Dasl.NameLinkSet
