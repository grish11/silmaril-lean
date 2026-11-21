module

public import Silmaril.Formats.Dasl.Prolly.Operations.Defs
public import Silmaril.Formats.Dasl.Prolly.Root.Publish.Thms
public import Silmaril.Formats.Dasl.Prolly.Scan.Thms
public import Silmaril.Semantics.Prolly.Operations.Thms
import Silmaril.Proofs.Formats.Dasl.ProllyOperations

public section

namespace Silmaril.Formats.Dasl.Prolly

open Silmaril.Semantics Silmaril.Semantics.Prolly

variable {Name Key Payload Error : Type} [LinearOrder Key]

theorem acquire_sound {width fuel : Nat} {tree : TypedMap Key Payload width}
    {codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)} {address : Block Name Key Payload → Name}
    {store : Store Name} (stored : Stored codec address tree.val store) (bound : store.Binding)
    {read : Read Name} (sound : Read.Sound read store) {map : OrderedMap Key Payload}
    (ok : acquire codec read width fuel (tree.val.rootName address) = .ok map) :
    map = TypedMap.view tree := Proofs.Formats.Dasl.ProllyOperations.acquire_sound stored bound sound ok

/-- A complete structural snapshot and enough depth fuel suffice; no target of
a link used as a key or value is consulted. -/
theorem acquire_complete {width fuel : Nat} (tree : TypedMap Key Payload width)
    (codec : Encode.PartialCodec (Block Name Key Payload) (Shallow Name)) (read : Read Name)
    (address : Block Name Key Payload → Name) (enough : tree.val.level < fuel)
    (reads : WholeReads (readBlock codec read) address tree.val) :
    acquire codec read width fuel (tree.val.rootName address) = .ok (TypedMap.view tree) :=
  Proofs.Formats.Dasl.ProllyOperations.acquire_complete tree codec read address enough reads

namespace RootProfile

variable (profile : RootProfile Name Key Payload)

theorem validRoot_name {store : Store Name} {map : OrderedMap Key Payload} {root : Name}
    (valid : profile.ValidRoots store root map.lookup?) : profile.rootName? map = some root :=
  (profile.roots_iff map root).mp (valid.imp fun _ valid => valid.imp fun _ witness =>
    ⟨witness.1, witness.2.1, witness.2.2.1⟩)

/-- A store-backed witness gives existence; all admissible roots use the same
fixed bottom-up profile. Binding alone gives neither fact. -/
theorem validRootNames_singleton {store : Store Name} {map : OrderedMap Key Payload} {root : Name}
    (valid : profile.ValidRoots store root map.lookup?) : Naming.names (profile.ValidRoots store) map.lookup? = {root} :=
  Naming.names_eq_singleton_iff.mpr ⟨valid, fun _ other =>
    Option.some.inj ((profile.validRoot_name other).symm.trans (profile.validRoot_name valid))⟩

theorem validRoot_of_stored {store : Store Name} {map : OrderedMap Key Payload} {root : Name}
    (named : profile.rootName? map = some root)
    (stored : Stored (blockCodec profile.key profile.payload) (replayAddress profile.nameBlock? root)
      (build profile.policy map) store) : profile.ValidRoots store root map.lookup? :=
  let replay := (build profile.policy map).replayAddress_spec profile.nameBlock? root named
  ⟨map, _, fun _ => rfl, replay.1, replay.2, stored⟩

variable [DecidableEq Name] (reader : profile.Readback)

theorem published_validRoot (map : OrderedMap Key Payload) (read : Name → Option ByteArray)
    {root : Name} {staged : Name → Option ByteArray} (named : profile.rootName? map = some root)
    (published : profile.publishMap reader map read = .ok (root, staged)) :
    profile.ValidRoots (reader.objectView staged) root map.lookup? :=
  Proofs.Formats.Dasl.ProllyOperations.published_validRoot profile reader map read named published

/-- Given adequate acquisitions, the only remaining stages are the semantic
overlap policy and shared non-replacing publication. -/
theorem combineAndPublish_eq {read : Name → Option ByteArray} {fuel : Nat} {leftRoot rightRoot : Name}
    {left right : OrderedMap Key Payload} (kind : OrderedMap.Combine) (overlap : OrderedMap.Overlap Key Payload Error)
    (leftOk : acquire (blockCodec profile.key profile.payload) (reader.shallowRead read)
      profile.policy.width fuel leftRoot = .ok left)
    (rightOk : acquire (blockCodec profile.key profile.payload) (reader.shallowRead read)
      profile.policy.width fuel rightRoot = .ok right) :
    profile.combineAndPublish reader kind overlap read fuel leftRoot rightRoot = (do
      let result ← (left.combine kind overlap right).mapError (CombineFailure.overlap (Name := Name))
      (profile.publishMap reader result read).mapError CombineFailure.publish) := by
  simp [combineAndPublish, leftOk, rightOk, Except.mapError, Bind.bind, Except.bind]

/-- Success agrees with the typed/semantic operation in any binding extension
of the reference that contains the observed shallow reads and both input ASTs. -/
theorem combineAndPublish_sound {read : Name → Option ByteArray} {fuel : Nat} {reference : Store Name}
    {left right : TypedMap Key Payload profile.policy.width} {leftAddress rightAddress : Block Name Key Payload → Name}
    (leftStored : Stored (blockCodec profile.key profile.payload) leftAddress left.val reference)
    (rightStored : Stored (blockCodec profile.key profile.payload) rightAddress right.val reference)
    (bound : reference.Binding) (sound : Read.Sound (reader.shallowRead read) reference)
    (kind : OrderedMap.Combine) (overlap : OrderedMap.Overlap Key Payload Error)
    {root : Name} {staged : Name → Option ByteArray}
    (ok : profile.combineAndPublish reader kind overlap read fuel (left.val.rootName leftAddress)
      (right.val.rootName rightAddress) = .ok (root, staged)) :
    ∃ result : OrderedMap Key Payload,
      (TypedMap.view left).combine kind overlap (TypedMap.view right) = .ok result ∧
      profile.rootName? result = some root ∧
      Naming.graph staged = Naming.union (Naming.graph read)
        (profile.byteObservations (build profile.policy result) (replayAddress profile.nameBlock? root)) ∧
      WholeReads (readBlock (blockCodec profile.key profile.payload) (reader.shallowRead staged))
        (replayAddress profile.nameBlock? root) (build profile.policy result) :=
  Proofs.Formats.Dasl.ProllyOperations.combineAndPublish_sound profile reader leftStored rightStored bound sound kind overlap ok

end RootProfile
end Silmaril.Formats.Dasl.Prolly
