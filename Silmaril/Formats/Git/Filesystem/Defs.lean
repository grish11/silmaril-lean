module

public import Silmaril.Formats.Git.Arena.Thms
public import Silmaril.Formats.Git.Translate.Graph.Defs
public import Silmaril.Formats.Dasl.Prolly.Root.Defs
public import Silmaril.Formats.Dasl.Prolly.Scan.Defs
public import Silmaril.Formats.Dasl.Wire.Profile.Defs
public import Silmaril.Semantics.Naming.Admission.Thms

@[expose] public section

namespace Silmaril.Formats.Git.Filesystem

open Silmaril.Formats.Cbor
open Silmaril.Formats.Dasl.Prolly (ByteKey)
open Silmaril.Semantics
open Arena (CasLane Read)

abbrev Cid := Formats.Dasl.Wire.BdaslCid
abbrev Digest := { bytes : List UInt8 // bytes.length = 32 }
abbrev Hash := ByteArray → Digest

def codecTag : CasLane → UInt8
  | .raw => 0x55
  | .object => 0x71

/-- Only the envelope is implemented. The supplied 32-byte function is the
abstract BLAKE3 parameter, not an implementation or a binding assumption. -/
def address (hash : Hash) (lane : CasLane) (bytes : ByteArray) : Cid :=
  ⟨1 :: codecTag lane :: 0x1e :: 0x20 :: (hash bytes).val, by
    cases lane <;> simp [codecTag, Drisl.CidProfile.accepts, Drisl.cidOk, Drisl.LinkRule.bdasl, (hash bytes).property]⟩

def laneMatches (lane : CasLane) (cid : Cid) : Bool :=
  cid.val[1]? == some (codecTag lane) && cid.val[2]? == some 0x1e

def kindLane : Kind → CasLane
  | .blob => .raw
  | .tree | .commit => .object

/-- The initial filesystem profile has width 32 and width-only cuts; raw
Git components use the existing unsigned byte-key order and codec. -/
def policy : Prolly.Policy ByteKey := ⟨32, by decide, fun _ _ => false⟩

abbrev DirBlock := Prolly.Block Cid ByteKey (Entry Cid)

def dirCodec := Formats.Dasl.Prolly.blockCodec (Name := Cid) Formats.Dasl.Prolly.byteKey Dasl.entryCodec

def dirProfile (hash : Hash) : Formats.Dasl.Prolly.RootProfile Cid ByteKey (Entry Cid) :=
  .ofTotalHash policy Formats.Dasl.Prolly.byteKey Dasl.entryCodec
    Formats.Dasl.Wire.Profile.bdasl.render? (address hash .object)

abbrev Writes := List (Cid × ByteArray)

structure Image (hash : Hash) (kind : Kind) where
  bytes : ByteArray
  descendants : Writes

def Image.name {hash : Hash} {kind : Kind} (image : Image hash kind) : Cid := address hash (kindLane kind) image.bytes

def Image.writes {hash : Hash} {kind : Kind} (image : Image hash kind) : Writes :=
  (image.name, image.bytes) :: image.descendants

def Image.publish {hash : Hash} {kind : Kind} (image : Image hash kind) (store : Cid → Option ByteArray) :
    Except Cid (Cid → Option ByteArray) := Naming.admit store (image.writes)

inductive ImportFault where
  | component (key : ByteKey)
  | gitlink (key : ByteKey)
  | external (kind : Kind)
  | commit
  | encoding
  deriving DecidableEq, Repr

def blockBytes? (block : DirBlock) : Option ByteArray :=
  (dirCodec.encode? block).bind Formats.Dasl.Wire.Profile.bdasl.render?

/-- Replay the landed bottom-up Prolly naming computation to enumerate exactly
the serialized root and auxiliary blocks. Any failed serialization aborts. -/
def stageDirectory (hash : Hash) (directory : ShallowTree ByteKey Cid) : Except ImportFault (Image hash .tree) := do
  let tree := Prolly.build policy directory.ordered
  let profile := dirProfile hash
  let some root := tree.rootName? profile.nameBlock? | .error .encoding
  let name := Prolly.replayAddress profile.nameBlock? root
  let some bytes := blockBytes? (Prolly.nodeBlock name tree.level tree.root) | .error .encoding
  if address hash .object bytes ≠ root then throw .encoding
  let blocks := (Prolly.blockOccurrences name tree.level tree.root).drop 1
  let writes ← blocks.mapM fun block => do
    let some wire := blockBytes? block | .error ImportFault.encoding
    pure (address hash .object wire, wire)
  pure ⟨bytes, writes⟩

variable {Ref Meta : Type}

/-- Admits the expanded filesystem fragment. Symlinks remain
raw bytes with symlink mode, not followed. Gitlinks and unresolved refs are
explicit unsupported cases, never dropped or read as subtrees. -/
def stage (hash : Hash) : {kind : Kind} → Object ByteKey Ref Meta kind → Except ImportFault (Image hash kind)
  | _, .blob bytes => .ok ⟨bytes, []⟩
  | _, .ref kind _ => .error (.external kind)
  | _, .commit .. => .error .commit
  | _, .tree keys modes children => do
    let order := keys.attach.sort (· ≤ ·)
    let read ← Translate.Graph.scan (Value := fun child : ↥keys => Image hash (modes child).kind) order fun child _ => do
      if !Dasl.validByteComponent child.val then throw (.component child.val)
      if modes child = .gitlink then throw (.gitlink child.val)
      stage hash (children child)
    let get := fun (child : ↥keys) => read child ((Finset.mem_sort _).mpr (Finset.mem_attach _ _))
    let directory : ShallowTree ByteKey Cid := ⟨keys, fun child => ⟨modes child, (get child).name⟩⟩
    let root ← stageDirectory hash directory
    let descendants := order.attach.flatMap fun child => (read child.val child.property).writes
    pure { root with descendants := root.descendants ++ descendants }

/-- A candidate naming relation is independent of the deterministic encoder.
Success fixes the root preimage; coverage and agreement with the address
function are separate hypotheses. -/
def Names (hash : Hash) (relation : Naming.Relation Cid ByteArray) : Naming.Relation Cid (Object ByteKey Ref Meta .tree) :=
  fun cid tree => ∃ (image : Image hash .tree), stage hash tree = .ok image ∧ relation cid image.bytes

abbrev Store := CasLane → Cid → Read ByteArray

def Store.ofArena {limit : Nat} (profile : Arena.Profile Cid ByteArray) (arena : Arena.State limit Cid ByteArray) : Store :=
  arena.readCas profile

def Store.ofPublished (store : Cid → Option ByteArray) : Store := fun lane name =>
  if !laneMatches lane name then .invalid else
    match store name with | none => .missing | some wire => .found wire

def readVerified (hash : Hash) (store : Store) (lane : CasLane) (name : Cid) : Read ByteArray :=
  if !laneMatches lane name then .invalid else (store lane name).andThen fun wire =>
    if address hash lane wire = name then .found wire else .invalid

def dirRead (hash : Hash) (store : Store) : Formats.Dasl.Prolly.Read Cid := fun cid =>
  match readVerified hash store .object cid with
  | .invalid | .conflict => .invalidWire
  | .found bytes => match Formats.Dasl.Wire.Profile.bdasl.parse? bytes with
    | some block => .found block
    | none => .invalidWire
  | _ => .missing

inductive ReadFault where
  | block (fault : Formats.Dasl.Prolly.Fault Cid)
  | deferred (cid : Cid)
  | conflict (cid : Cid)
  | unsupportedEntry (key : ByteKey)
  | component (key : ByteKey)
  | notDirectory
  deriving DecidableEq

def refineRead (store : Store) : Formats.Dasl.Prolly.Fault Cid → ReadFault
  | fault@(.missing cid) | fault@(.invalidWire cid) =>
    match store .object cid with
    | .deferred | .placeholder => .deferred cid
    | .conflict => .conflict cid
    | _ => .block fault
  | fault => .block fault

abbrev ChildLookup := Cid → ByteKey → Except ReadFault (Option (Entry Cid))

def checkedChild (store : Store)
    (query : Cid → ByteKey → Except (Formats.Dasl.Prolly.Fault Cid) (Option (Entry Cid))) : ChildLookup :=
    fun root key => do
  if !Dasl.validByteComponent key then throw (.component key)
  let result ← (query root key).mapError (refineRead store)
  match result with
  | none => .ok none
  | some entry =>
    if entry.mode = .gitlink || !laneMatches (kindLane entry.mode.kind) entry.target then throw (.unsupportedEntry key)
    else .ok (some entry)

/-- No Git metadata or OID is required to consult a tree CID. A bounded closed
Prolly scan distinguishes a missing block from a legitimately absent child. -/
def lookupChild (hash : Hash) (store : Store) (fuel : Nat) : ChildLookup :=
  checkedChild store (Formats.Dasl.Prolly.lookup dirCodec (dirRead hash store) policy.width fuel)

/-- The empty path denotes the root descriptor. This descriptor alone makes
no availability assertion. Each nonempty step uses the selected child lookup. -/
def locateWith (child : ChildLookup) : Cid → List ByteKey → Except ReadFault (Option (Entry Cid))
  | root, [] => .ok (some ⟨.directory, root⟩)
  | root, key :: rest => do
    let name ← child root key
    match name, rest with
    | none, _ | some _, [] => .ok name
    | some entry, _ :: _ =>
      if entry.mode = .directory then locateWith child entry.target rest else throw .notDirectory

def locate (hash : Hash) (store : Store) (fuel : Nat) : Cid → List ByteKey → Except ReadFault (Option (Entry Cid)) :=
  locateWith (lookupChild hash store fuel)

def locateUtf8 (hash : Hash) (store : Store) (fuel : Nat) (root : Cid) (path : Path) :
    Except ReadFault (Option (Entry Cid)) := locate hash store fuel root (path.map fun name => Dasl.utf8Key name.val)

/-- Both files and symlinks return the raw object bytes; interpretation of a
symlink target is not part of this interface. -/
def openBlob (hash : Hash) (store : Store) (entry : Entry Cid) : Read ByteArray :=
  match entry.mode with
  | .file _ => readVerified hash store .raw entry.target
  | _ => .invalid

end Silmaril.Formats.Git.Filesystem
