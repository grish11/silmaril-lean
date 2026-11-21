module

public import Silmaril.Formats.Dasl.Prolly.Root.Publish.Defs
public import Silmaril.Formats.Dasl.Prolly.Root.Thms
public import Silmaril.Formats.Dasl.Prolly.Publish.Thms
import Silmaril.Proofs.Formats.Dasl.ProllyProfilePublish

public section

namespace Silmaril.Formats.Dasl.Prolly.RootProfile

open Silmaril.Semantics Silmaril.Semantics.Prolly
open Silmaril.Semantics.Naming

variable {Name Key Payload : Type} [DecidableEq Name] (profile : RootProfile Name Key Payload)
  (reader : profile.Readback)

theorem publishTree_naming_failure (tree : Semantics.Prolly.Tree Key Payload) (read : Name → Option ByteArray)
    (unavailable : tree.rootName? profile.nameBlock? = none) :
    profile.publishTree reader tree read = .error .naming := by simp [publishTree, unavailable]

theorem publishTree_spec (tree : Semantics.Prolly.Tree Key Payload) (read : Name → Option ByteArray) {root : Name}
    (named : tree.rootName? profile.nameBlock? = some root) :
    profile.PublicationSpec reader tree read root (profile.publishTree reader tree read) :=
  Proofs.Formats.Dasl.ProllyProfilePublish.publishTree_spec profile reader tree read named

/-- After naming succeeds, the only obstruction to publication is a collision
in the complete union of existing and requested bytes. -/
theorem publishTree_accepts_iff (tree : Semantics.Prolly.Tree Key Payload) (read : Name → Option ByteArray)
    {root : Name} (named : tree.rootName? profile.nameBlock? = some root) :
    (∃ staged, profile.publishTree reader tree read = .ok (root, staged)) ↔
      Binding (union (graph read) (profile.byteObservations tree (replayAddress profile.nameBlock? root))) :=
  Proofs.Formats.Dasl.ProllyProfilePublish.accepts_iff_of_spec profile reader tree read root _
    (profile.publishTree_spec reader tree read named)

/-- The canonical builder is replayed in full. On success the readback is for
the tree of this map, and existing raw bytes are retained by exact union. -/
theorem publishMap_spec [LinearOrder Key] (map : OrderedMap Key Payload) (read : Name → Option ByteArray) {root : Name}
    (named : profile.rootName? map = some root) :
    profile.PublicationSpec reader (build profile.policy map) read root (profile.publishMap reader map read) :=
  profile.publishTree_spec reader (build profile.policy map) read named

end Silmaril.Formats.Dasl.Prolly.RootProfile
