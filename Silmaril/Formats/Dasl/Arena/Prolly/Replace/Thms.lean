module

public import Silmaril.Formats.Dasl.Arena.Prolly.Replace.Defs
public import Silmaril.Formats.Dasl.Prolly.Replace.Thms
import Silmaril.Proofs.Formats.Dasl.Arena.Prolly.Replace

public section

namespace Silmaril.Formats.Dasl.Arena.Prolly.Indexed

open Silmaril.Formats.Dasl.Prolly (RootProfile readBlock blockCodec)
open Silmaril.Semantics (OrderedMap)
open Silmaril.Semantics.Prolly (build replayAddress blockOccurrences)
open Silmaril.Semantics.Naming (Subset graph union listed collisions)

variable {Name Key Payload : Type} [LinearOrder Key] [DecidableEq Name]

/-- The local edit and the named edit commit exactly the same bytes. All prior
indices and their projected names are unchanged, even when aliased. Newly
allocated blocks have backward local links and exact staged-byte witnesses. -/
theorem replaceValue_exact (arena : Indexed Name Key Payload) (profile : RootProfile Name Key Payload)
    (reader : profile.Readback) (project : Handle Name → Name)
    {observed authoritative staged : Name → Option ByteArray} {fuel root : Nat} {key : Key} {value : Payload}
    (agrees : PathAgrees arena project
      (readBlock (blockCodec profile.key profile.payload) (reader.pathReader observed)) key fuel (.local root))
    {edit : Edit Name Key Payload}
    (replaced : arena.replaceValue profile project authoritative fuel root key value = .ok (edit, staged)) :
    profile.replaceValue reader observed authoritative fuel (project (.local root)) key value = .ok (edit.named, staged) ∧
      graph staged = union (graph authoritative) (listed edit.named.writes) ∧
      edit.arena.blocks.size = arena.blocks.size + edit.named.writes.length ∧
      edit.root + 1 = edit.arena.blocks.size ∧
      (∀ index, index < arena.blocks.size → edit.arena.blocks[index]? = arena.blocks[index]?) ∧
      edit.PreservesNames arena.blocks.size project ∧ edit.project (.local edit.root) = edit.named.root ∧
      BlocksStaged profile arena.blocks.size edit.arena edit.project edit.named.writes :=
  Proofs.Formats.Dasl.Arena.Prolly.Replace.admitted arena profile reader project agrees replaced

omit [LinearOrder Key] [DecidableEq Name] in
theorem staged_readback {profile : RootProfile Name Key Payload} (reader : profile.Readback)
    {base : Nat} {arena : Indexed Name Key Payload} {project : Handle Name → Name}
    {writes : List (Name × ByteArray)} {staged : Name → Option ByteArray}
    (covered : BlocksStaged profile base arena project writes) (includes : Subset (listed writes) (graph staged))
    {index : Nat} (lower : base ≤ index) (upper : index < arena.blocks.size) :
    ∃ block, arena.blocks[index]? = some block ∧
      reader.readBlock? staged (project (.local index)) = some (relabel project block) :=
  Proofs.Formats.Dasl.Arena.Prolly.Replace.readback reader covered includes lower upper

/-- For any authoritative extension that contains the old canonical tree and
the observed path, the edit yields the same root name as a full rebuild and
readback of its entire tree, not only of the newly written route. -/
theorem replaceValue_rebuild (arena : Indexed Name Key Payload) (profile : RootProfile Name Key Payload)
    (reader : profile.Readback) (project : Handle Name → Name) (map : OrderedMap Key Payload)
    {observed authoritative staged : Name → Option ByteArray} {fuel root : Nat} {key : Key} {value : Payload}
    {edit : Edit Name Key Payload} (named : profile.rootName? map = some (project (.local root)))
    (agrees : PathAgrees arena project
      (readBlock (blockCodec profile.key profile.payload) (reader.pathReader observed)) key fuel (.local root))
    (includes : Subset (graph observed) (graph authoritative))
    (present : Subset (profile.byteObservations (build profile.policy map)
      (replayAddress profile.nameBlock? (project (.local root)))) (graph authoritative))
    (replaced : arena.replaceValue profile project authoritative fuel root key value = .ok (edit, staged)) :
    let next := build profile.policy (RootProfile.replacedMap map key value)
    let address := replayAddress profile.nameBlock? (project (.local root))
    map.lookup? key = some edit.named.previous ∧
    profile.rootName? (RootProfile.replacedMap map key value) = some (edit.project (.local edit.root)) ∧
    edit.arena.blocks.size = arena.blocks.size + (build profile.policy map).level + 1 ∧
    ∀ block ∈ blockOccurrences address next.level next.root, reader.readBlock? staged (address block) = some block :=
  Proofs.Formats.Dasl.Arena.Prolly.Replace.rebuilt arena profile reader project map named agrees includes present replaced

/-- Only the explicit absent case refines named absence. The named absence
theorem then applies against any valid binding reference. -/
theorem replaceValue_absent (arena : Indexed Name Key Payload) (profile : RootProfile Name Key Payload)
    (reader : profile.Readback) (project : Handle Name → Name)
    {observed authoritative : Name → Option ByteArray} {fuel root : Nat} {key : Key} {value : Payload}
    (agrees : PathAgrees arena project
      (readBlock (blockCodec profile.key profile.payload) (reader.pathReader observed)) key fuel (.local root))
    (rejected : arena.replaceValue profile project authoritative fuel root key value = .error (.planning .absent)) :
    profile.replaceValue reader observed authoritative fuel (project (.local root)) key value = .error (.planning .absent) :=
  Proofs.Formats.Dasl.Arena.Prolly.Replace.absent arena profile reader project agrees rejected

theorem replaceValue_collision (arena : Indexed Name Key Payload) (profile : RootProfile Name Key Payload)
    (project : Handle Name → Name) {authoritative : Name → Option ByteArray} {fuel root : Nat}
    {key : Key} {value : Payload} {name : Name}
    (rejected : arena.replaceValue profile project authoritative fuel root key value = .error (.collision name)) :
    ∃ edit, arena.planValue profile project key value fuel none (.local root) = .ok edit ∧
      name ∈ collisions (union (graph authoritative) (listed edit.named.writes)) :=
  Proofs.Formats.Dasl.Arena.Prolly.Replace.collided arena profile project rejected

end Silmaril.Formats.Dasl.Arena.Prolly.Indexed
