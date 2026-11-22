module

public import Silmaril.Formats.Git.Filesystem.Defs
public import Silmaril.Formats.Dasl.Prolly.Scan.Thms
import Silmaril.Proofs.Formats.Git.Filesystem.Basic

public section

namespace Silmaril.Formats.Git.Filesystem

open Silmaril.Semantics
open Formats.Dasl.Prolly (ByteKey)
open Arena (CasLane Read)

variable {hash : Hash} {Ref Meta : Type}

@[simp] theorem laneMatches_address (hash : Hash) (lane : CasLane) (bytes : ByteArray) :
    laneMatches lane (address hash lane bytes) = true := by
  cases lane <;> rfl

/-- Any covered relation included in this fixed addressing graph assigns the
same root after successful staging. No injectivity of `hash` is used. -/
theorem names_iff {relation : Naming.Relation Cid ByteArray} {tree : Object ByteKey Ref Meta .tree}
    {image : Image hash .tree} {name : Cid} (staged : stage hash tree = .ok image)
    (covers : ∃ cid, relation cid image.bytes)
    (agrees : ∀ cid wire, relation cid wire → cid = address hash .object wire) :
    Names hash relation name tree ↔ name = image.name :=
  Proofs.Formats.Git.Filesystem.names_iff staged covers agrees

theorem Image.publish_bindings {kind : Kind} {image : Image hash kind} {before after : Cid → Option ByteArray}
    (published : image.publish before = .ok after) :
    Naming.graph after = Naming.union (Naming.graph before) (Naming.listed (image.writes)) :=
  Naming.admit_eq_union published

theorem Image.readPublished {kind : Kind} {image : Image hash kind} {before after : Cid → Option ByteArray}
    (published : image.publish before = .ok after) :
    readVerified hash (Store.ofPublished after) (kindLane kind) (image.name) = .found image.bytes := by
  have atRoot := Proofs.Formats.Git.Filesystem.published_root published
  change after (address hash (kindLane kind) image.bytes) = some image.bytes at atRoot
  simp [readVerified, Store.ofPublished, Image.name, atRoot, Read.andThen]

theorem readVerified_found {store : Store} {lane : CasLane} {name : Cid} {bytes : ByteArray}
    (found : readVerified hash store lane name = .found bytes) :
    store lane name = .found bytes ∧ address hash lane bytes = name :=
  Proofs.Formats.Git.Filesystem.readVerified_found found

theorem checkedChild_ok {store : Store}
    {query : Cid → ByteKey → Except (Formats.Dasl.Prolly.Fault Cid) (Option (Entry Cid))}
    {root : Cid} {key : ByteKey} {result : Option (Entry Cid)}
    (checked : checkedChild store query root key = .ok result) : query root key = .ok result :=
  Proofs.Formats.Git.Filesystem.checkedChild_ok checked

/-- Under a binding reference that actually contains this canonical directory,
both returned entries and closed-view misses match the source byte-key map. -/
theorem lookupChild_sound {store : Store} {reference : Formats.Dasl.Store Cid}
    {directory : ShallowTree ByteKey Cid} {addressBlock : DirBlock → Cid}
    (stored : Formats.Dasl.Prolly.Stored dirCodec addressBlock (Prolly.build policy directory.ordered) reference)
    (binding : reference.Binding) (reader : Formats.Dasl.Prolly.Read.Sound (dirRead hash store) reference)
    {fuel : Nat} {key : ByteKey} {result : Option (Entry Cid)}
    (checked : lookupChild hash store fuel ((Prolly.build policy directory.ordered).rootName addressBlock) key = .ok result) :
    directory.ordered.lookup? key = result :=
  Formats.Dasl.Prolly.lookup_sound policy stored binding reader (checkedChild_ok checked)

end Silmaril.Formats.Git.Filesystem
