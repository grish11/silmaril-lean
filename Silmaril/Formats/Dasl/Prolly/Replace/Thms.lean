module

public import Silmaril.Formats.Dasl.Prolly.Replace.Defs
public import Silmaril.Formats.Dasl.Prolly.Route.Thms
public import Silmaril.Formats.Dasl.Prolly.Root.Publish.Thms
import Silmaril.Proofs.Formats.Dasl.ProllyReplace

public section

namespace Silmaril.Formats.Dasl.Prolly.RootProfile

open Silmaril.Semantics Silmaril.Semantics.Prolly Silmaril.Semantics.Naming

variable {Name Key Payload : Type} [LinearOrder Key]

theorem replacedMap_lookup (map : OrderedMap Key Payload) (key query : Key) (value : Payload) :
    (replacedMap map key value).lookup? query =
      (map.lookup? query).map (fun old => if key = query then value else old) :=
  Proofs.Formats.Dasl.ProllyReplace.replacedMap_lookup map key query value

/-- For every binding reference including the observed bytes and the old canonical
tree, a successful plan replaces exactly one value and agrees with the fixed
profile's rebuild. Binding of the proposed union is checked by admission, not assumed here. -/
theorem planReplacement_rebuild (profile : RootProfile Name Key Payload) (reader : profile.Readback)
    (map : OrderedMap Key Payload) {root : Name} (named : profile.rootName? map = some root)
    {observed : Name → Option ByteArray} {reference : Relation Name ByteArray}
    (includes : Subset (graph observed) reference) (bound : Binding reference)
    (present : Subset (profile.byteObservations (build profile.policy map)
      (replayAddress profile.nameBlock? root)) reference)
    {fuel : Nat} {key : Key} {value : Payload} {planned : Replacement Name Payload}
    (checked : profile.planReplacement (readBlock (blockCodec profile.key profile.payload) (reader.pathReader observed))
      key value fuel none root = .ok planned) :
    let next := build profile.policy (replacedMap map key value)
    map.lookup? key = some planned.previous ∧ profile.rootName? (replacedMap map key value) = some planned.root ∧
      planned.writes.length = (build profile.policy map).level + 1 ∧ profile.NodeBytes (replayAddress profile.nameBlock? root)
        (union reference (listed planned.writes)) next.level next.root :=
  Proofs.Formats.Dasl.ProllyReplace.rebuild profile reader map named includes bound present checked

/-- Success adds exactly the planned bindings, retaining every authoritative byte. -/
theorem replaceValue_exact [DecidableEq Name] (profile : RootProfile Name Key Payload)
    (reader : profile.Readback) {observed authoritative staged : Name → Option ByteArray}
    {fuel : Nat} {root : Name} {key : Key} {value : Payload} {planned : Replacement Name Payload}
    (checked : profile.replaceValue reader observed authoritative fuel root key value = .ok (planned, staged)) :
    profile.planReplacement (readBlock (blockCodec profile.key profile.payload) (reader.pathReader observed))
        key value fuel none root = .ok planned ∧
      graph staged = union (graph authoritative) (listed planned.writes) :=
  Proofs.Formats.Dasl.ProllyReplace.publish_succeeded profile reader checked

/-- Rejection witnesses two different raw byte strings at the same name. -/
theorem replaceValue_collision [DecidableEq Name] (profile : RootProfile Name Key Payload)
    (reader : profile.Readback) {observed authoritative : Name → Option ByteArray}
    {fuel : Nat} {root name : Name} {key : Key} {value : Payload}
    (checked : profile.replaceValue reader observed authoritative fuel root key value = .error (.collision name)) :
    ∃ planned, profile.planReplacement (readBlock (blockCodec profile.key profile.payload) (reader.pathReader observed))
        key value fuel none root = .ok planned ∧
      name ∈ collisions (union (graph authoritative) (listed planned.writes)) :=
  Proofs.Formats.Dasl.ProllyReplace.collided profile reader checked

/-- An authoritative snapshot already containing the old canonical tree provides
full readback of the new canonical tree, even when the path reader omits siblings. -/
theorem replaceValue_rebuild [DecidableEq Name] (profile : RootProfile Name Key Payload)
    (reader : profile.Readback) (map : OrderedMap Key Payload) {root : Name} (named : profile.rootName? map = some root)
    {observed authoritative staged : Name → Option ByteArray} (includes : Subset (graph observed) (graph authoritative))
    (present : Subset (profile.byteObservations (build profile.policy map)
      (replayAddress profile.nameBlock? root)) (graph authoritative))
    {fuel : Nat} {key : Key} {value : Payload} {planned : Replacement Name Payload}
    (checked : profile.replaceValue reader observed authoritative fuel root key value = .ok (planned, staged)) :
    let next := build profile.policy (replacedMap map key value)
    let address := replayAddress profile.nameBlock? root
    map.lookup? key = some planned.previous ∧ profile.rootName? (replacedMap map key value) = some planned.root ∧
      planned.writes.length = (build profile.policy map).level + 1 ∧
      profile.NodeBytes address (graph staged) next.level next.root ∧
      ∀ block ∈ blockOccurrences address next.level next.root, reader.readBlock? staged (address block) = some block :=
  Proofs.Formats.Dasl.ProllyReplace.publish_rebuild profile reader map named includes present checked

/-- Absence follows from the routed representation in any such binding reference;
it cannot be inferred from missing bytes, invalid blocks, or exhausted fuel. -/
theorem replaceValue_absent [DecidableEq Name] (profile : RootProfile Name Key Payload)
    (reader : profile.Readback) (map : OrderedMap Key Payload) {root : Name} (named : profile.rootName? map = some root)
    {observed authoritative : Name → Option ByteArray} {reference : Relation Name ByteArray}
    (includes : Subset (graph observed) reference) (bound : Binding reference)
    (present : Subset (profile.byteObservations (build profile.policy map)
      (replayAddress profile.nameBlock? root)) reference)
    {fuel : Nat} {key : Key} {value : Payload}
    (checked : profile.replaceValue reader observed authoritative fuel root key value = .error (.planning .absent)) :
    map.lookup? key = none :=
  Proofs.Formats.Dasl.ProllyReplace.absent_sound profile reader map named includes bound present checked

end Silmaril.Formats.Dasl.Prolly.RootProfile
