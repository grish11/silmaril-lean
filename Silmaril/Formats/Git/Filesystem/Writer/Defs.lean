module

public import Silmaril.Formats.Git.Filesystem.Defs
public import Silmaril.Formats.Dasl.Wire.Canonical.Defs
public import Silmaril.Formats.Dasl.Prolly.Route.Defs

@[expose] public section

namespace Silmaril.Formats.Git.Filesystem

open Silmaril.Semantics.Prolly (build blockOccurrences replayAddress)
open Formats.Dasl.Prolly (ByteKey)

abbrev ByteDirectory := ShallowTree ByteKey Cid

def BlockBounds (block : DirBlock) : Prop :=
  (match block with
    | .leaf _ => True
    | .branch level _ => 0 < level ∧ level < 2 ^ 63) ∧
  ∀ value, dirCodec.encode? block = some value → Formats.Dasl.Wire.BdaslEncodable value

/-- Check the blocks induced by replay with any well-tagged object fallback.
Successful bounded serialization ensures no reached block uses that fallback.
This condition is independent of CAS binding. -/
def DirectoryBounds (hash : Hash) (directory : ByteDirectory) : Prop :=
  let tree := build policy directory.ordered
  ∀ fallback, laneMatches .object fallback = true →
    let name := replayAddress (dirProfile hash).nameBlock? fallback
    ∀ block ∈ blockOccurrences name tree.level tree.root, BlockBounds block

/-- The image names the canonical root and includes the correctly addressed
serialized preimage of every Prolly block in this directory. -/
def Image.OfDirectory {hash : Hash} (image : Image hash .tree) (directory : ByteDirectory) : Prop :=
  let tree := build policy directory.ordered
  let name := replayAddress (dirProfile hash).nameBlock? image.name
  tree.rootName name = image.name ∧
    ∀ block ∈ blockOccurrences name tree.level tree.root,
      ∃ bytes, blockBytes? block = some bytes ∧ name block = address hash .object bytes ∧
        (name block, bytes) ∈ image.writes

def namedDirectory {keys : Finset ByteKey} (modes : ↥keys → EntryMode) (names : ↥keys → Cid) : ByteDirectory :=
  ⟨keys, fun child => ⟨modes child, names child⟩⟩

/-- Structural support and wire bounds, checked bottom up using the chosen
staged child names. Raw blobs do not pass through a CBOR length codec. -/
def StageBounds (hash : Hash) {Ref Meta : Type} : {kind : Kind} → Object ByteKey Ref Meta kind → Prop
  | _, .blob _ => True
  | _, .ref .. | _, .commit .. => False
  | _, .tree keys modes children =>
    (∀ child : ↥keys, Dasl.validByteComponent child.val = true ∧ modes child ≠ .gitlink ∧
      StageBounds hash (children child)) ∧
    (∀ images : (child : ↥keys) → Image hash (modes child).kind,
      (∀ child, stage hash (children child) = .ok (images child)) →
        DirectoryBounds hash (namedDirectory modes fun child => (images child).name))

def Image.Covered {hash : Hash} {kind : Kind} (image : Image hash kind) (fetch : Cid → Option ByteArray) : Prop :=
  ∀ binding ∈ image.writes, fetch binding.1 = some binding.2

/-- Every directory query agrees with its source byte-key map at sufficient
per-directory fuel, and each reached child CID recursively gives its source
directory or exact blob bytes. No source Git OID is needed by the reader. -/
def Readback (hash : Hash) (store : Store) {Ref Meta : Type} : {kind : Kind} → Object ByteKey Ref Meta kind → Cid → Prop
  | _, .blob bytes, cid => readVerified hash store .raw cid = .found bytes
  | _, .ref .., _ | _, .commit .., _ => False
  | _, .tree keys modes children, cid =>
    ∃ names : ↥keys → Cid,
      let directory := namedDirectory modes names
      (∀ key fuel, (build policy directory.ordered).level < fuel →
        Formats.Dasl.Prolly.routedLookup dirCodec (dirRead hash store) policy.width fuel cid key =
          .ok (directory.ordered.lookup? key)) ∧
      (∀ child, Dasl.validByteComponent child.val = true ∧ modes child ≠ .gitlink ∧
        laneMatches (kindLane (modes child).kind) (names child) = true ∧ Readback hash store (children child) (names child))

end Silmaril.Formats.Git.Filesystem
