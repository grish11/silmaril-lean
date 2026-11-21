module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.String.Basic
public import Silmaril.Formats.Git.Defs
public import Silmaril.Formats.Dasl.Prolly.Thms

@[expose] public section

namespace Silmaril.Formats.Git

namespace Directory

variable {Key Item : Type}

def ordered [LinearOrder Key] (dir : Directory Key Item) : Semantics.OrderedMap Key Item :=
  let members := fun _ hit => (Finset.mem_sort _).mp hit
  ⟨dir.keys.sort.pmap (fun key hit => (key, dir.get ⟨key, hit⟩)) members,
    dir.keys.sortedLT_sort.pairwise.pmap members (by intros; assumption)⟩

def ofOrdered [LinearOrder Key] (dir : Semantics.OrderedMap Key Item) : Directory Key Item :=
  ⟨dir.keys.toFinset, fun key => (dir.lookup? key.val).get (by
    obtain ⟨⟨found, value⟩, present, same⟩ := List.mem_map.mp (List.mem_toFinset.mp key.property)
    change found = key.val at same
    rw [← same, dir.lookup_eq_some_iff.mpr present]
    rfl)⟩

/-- Rekey using an exact inverse on emitted keys (e.g. UTF-8). -/
def rekey {Next : Type} (dir : Directory Key Item)
    (codec : Silmaril.Formats.Dasl.Encode.TotalCodec Key Next) : Directory Next Item :=
  ⟨dir.keys.map ⟨codec.encode, codec.injective⟩, fun key =>
    let found := codec.decode? key.val
    have present : ∃ entry ∈ dir.keys, found = some entry := by
      obtain ⟨entry, hit, same⟩ := Finset.mem_map.mp key.property
      change codec.encode entry = key.val at same
      exact ⟨entry, hit, (congrArg codec.decode? same).symm.trans (codec.recovers entry)⟩
    have decoded : found.isSome = true := by obtain ⟨_, _, hit⟩ := present; simp [hit]
    dir.get ⟨found.get decoded, by obtain ⟨_, member, hit⟩ := present; simpa [hit] using member⟩⟩

end Directory

namespace Dasl

open Silmaril.Formats.Dasl
open Silmaril.Formats.Dasl.Encode (TotalCodec)

variable {Key Name Meta : Type}

/-- The usual octal Git modes, represented as numeric i64 values in this layout. -/
def modeBits : EntryMode → UInt64
  | .directory => 16384
  | .file .regular => 33188
  | .file .executable => 33261
  | .file .symlink => 40960
  | .gitlink => 57344

def parseMode : UInt64 → Option EntryMode
  | 16384 => some .directory
  | 33188 => some (.file .regular)
  | 33261 => some (.file .executable)
  | 40960 => some (.file .symlink)
  | 57344 => some .gitlink
  | _ => none

def linkFor (kind : Kind) (name : Name) : Link Name :=
  match kind with
  | .blob => .blob name
  | .tree | .commit => .obj name

def readLink : Kind → Link Name → Option Name
  | .blob, .blob name => some name
  | .tree, .obj name | .commit, .obj name => some name
  | _, _ => none

def linkCodec (kind : Kind) : TotalCodec Name (Shallow Name) :=
  (⟨linkFor kind, readLink kind, fun name => by cases kind <;> rfl⟩ : TotalCodec Name (Link Name)).then Encode.link

def entryKeys : Finset String := {"mode", "link"}

def encodeEntry (entry : Entry Name) : Shallow Name :=
  .dict entryKeys (fun key => if key.val = "mode" then .i64 (modeBits entry.mode)
    else .ref (linkFor entry.mode.kind entry.target))

def decodeEntry : Shallow Name → Option (Entry Name)
  | .dict keys fields =>
    if same : keys = entryKeys then do
      let values : ↥entryKeys → Shallow Name := same ▸ fields
      let mode ← Encode.bits.decode? (values ⟨"mode", by decide⟩) >>= parseMode
      let name ← (linkCodec mode.kind).decode? (values ⟨"link", by decide⟩)
      pure ⟨mode, name⟩
    else none
  | _ => none

def bytesKey (bytes : ByteArray) : Prolly.ByteKey := bytes.data.toList.map UInt8.toFin

/-- Exact UTF-8 only: no lossy decoding, normalization, or case folding. -/
def utf8Key (name : String) : Prolly.ByteKey := bytesKey name.toByteArray

def decodeUtf8Key (key : Prolly.ByteKey) : Option String :=
  String.fromUTF8? (key.map UInt8.ofFin).toByteArray

/-- The native path-component check does not require UTF-8. -/
def validByteComponent (key : Prolly.ByteKey) : Bool :=
  !key.isEmpty && key != [46] && key != [46, 46] && !key.contains 0 && !key.contains 47

def decodeComponent (key : Prolly.ByteKey) : Option Component := (decodeUtf8Key key).bind Component.parse?

def compatible (entry : Entry (Link Name)) : Prop := ∃ name, entry.target = linkFor entry.mode.kind name

def linkedEntry (entry : Entry Name) : Entry (Link Name) :=
  ⟨entry.mode, linkFor entry.mode.kind entry.target⟩

/-- Name assignment is explicit. No hash correctness, injectivity, or binding
property is baked into this model. -/
structure Naming (Name : Type) where
  object : Shallow Name → Name
  blob : ByteArray → Name

/-- A directory root block and any additional blocks, such as Prolly branches
and leaves. Child Git objects are accounted for separately. -/
structure Layout (Key Name : Type) where
  encode? : Naming Name → ShallowTree Key Name → Option (Shallow Name × Store Name)

def Layout.contramap (layout : Layout Key Name) {Other : Type}
    (convert : ShallowTree Other Name → ShallowTree Key Name) : Layout Other Name :=
  ⟨fun naming dir => layout.encode? naming (convert dir)⟩

structure Rendered (Name : Type) where
  root : Name
  store : Store Name

def Rendered.opaque (name : Name) : Rendered Name :=
  ⟨name, ⟨fun _ _ => False, fun _ _ => False⟩⟩

def Rendered.raw (naming : Naming Name) (bytes : ByteArray) : Rendered Name :=
  ⟨naming.blob bytes, ⟨fun _ _ => False, fun name payload => name = naming.blob bytes ∧ payload = bytes⟩⟩

def Rendered.object (naming : Naming Name) (value : Shallow Name) (children : Store Name) : Rendered Name :=
  ⟨naming.object value, ⟨fun name payload => (name = naming.object value ∧ payload = value) ∨
    children.objects name payload, children.blobs⟩⟩

def Rendered.union {Index : Type} (items : Index → Rendered Name) : Store Name :=
  ⟨fun name value => ∃ index, (items index).store.objects name value,
    fun name value => ∃ index, (items index).store.blobs name value⟩

/-- A projection to the shared DASL partial view of a root block. An absent
binding can still be represented by an opaque link and no local observations. -/
def Rendered.materializes (kind : Kind) (rendered : Rendered Name) (value : Partial Name) : Prop :=
  value.shallow = .ref (linkFor kind rendered.root) ∧ value.bindings.Subset rendered.store

def Rendered.names {Source : Type} (render : Source → Option (Rendered Name)) : Semantics.Naming.Relation Name Source :=
  fun name source => ∃ result, render source = some result ∧ result.root = name

def renderDir [DecidableEq Key] (naming : Naming Name) (layout : Layout Key Name)
    (valid : Key → Bool) (keys : Finset Key) (mode : ↥keys → EntryMode)
    (children : ↥keys → Option (Rendered Name)) : Option (Rendered Name) := do
  if ∀ key ∈ keys, valid key = true then
    if present : ∀ key (hit : key ∈ keys), (children ⟨key, hit⟩).isSome = true then
      let resolved := fun (key : ↥keys) => (children key).get (present key.val key.property)
      let (value, blocks) ← layout.encode? naming ⟨keys, fun key => ⟨mode key, (resolved key).root⟩⟩
      pure (Rendered.object naming value (blocks.union (Rendered.union resolved)))
    else none
  else none

def metadataCodec : TotalCodec Metadata (Shallow Name) :=
  (⟨fun data => (data.message, data.timestamp), fun (message, timestamp) => some ⟨message, timestamp⟩,
    fun ⟨_, _⟩ => rfl⟩ : TotalCodec Metadata (ByteArray × Int64)).then
    ((Encode.bytes.prod Encode.signed).then Encode.pairEntry)

/-- A commit is `[tree, [parents...], metadata]`. The tree and parent codecs are
independent, so this also gives a codec over richer than name-only references. -/
def commitCodec {Root Parent : Type} (tree : TotalCodec Root (Shallow Name))
    (parent : TotalCodec Parent (Shallow Name)) (metadata : TotalCodec Meta (Shallow Name)) :
    TotalCodec (Commit Root Parent Meta) (Shallow Name) where
  encode commit := Encode.list.encode [tree.encode commit.tree,
    (Encode.listOf parent).encode commit.parents, metadata.encode commit.metadata]
  decode?
    | .list 3 fields => do pure ⟨← tree.decode? (fields 0), ← (Encode.listOf parent).decode? (fields 1),
        ← metadata.decode? (fields 2)⟩
    | _ => none
  recovers commit := by
    change (do pure ⟨← tree.decode? (tree.encode commit.tree),
      ← (Encode.listOf parent).decode? ((Encode.listOf parent).encode commit.parents),
      ← metadata.decode? (metadata.encode commit.metadata)⟩) = some commit
    cases commit; simp [tree.recovers, (Encode.listOf parent).recovers, metadata.recovers]

def namedCommit (metadata : TotalCodec Meta (Shallow Name)) : TotalCodec (Commit Name Name Meta) (Shallow Name) :=
  commitCodec (linkCodec .tree) (linkCodec .commit) metadata

def renderCommit (naming : Naming Name) (codec : TotalCodec Meta (Shallow Name))
    (tree : Rendered Name) (parents : List (Rendered Name)) (metadata : Meta) : Rendered Name :=
  let value := (namedCommit codec).encode ⟨tree.root, parents.map Rendered.root, metadata⟩
  Rendered.object naming value (tree.store.union (Rendered.union parents.get))

def renderTree (naming : Naming Name) (layout : Layout String Name) : Git.Tree → Option (Rendered Name)
  | .file _ bytes => some (Rendered.raw naming bytes)
  | .dir keys children => renderDir naming layout validComponent keys
      (fun key => (children key).tag.entryMode) (fun key => renderTree naming layout (children key))

def renderObject [DecidableEq Key] (naming : Naming Name) (layout : Layout Key Name) (valid : Key → Bool)
    (codec : TotalCodec Meta (Shallow Name)) : {kind : Kind} → Object Key Name Meta kind → Option (Rendered Name)
  | _, .ref _ name => some (Rendered.opaque name)
  | _, .blob bytes => some (Rendered.raw naming bytes)
  | _, .tree keys modes children => renderDir naming layout valid keys modes
      (fun key => renderObject naming layout valid codec (children key))
  | _, .commit tree _ parents metadata => do
    let target ← renderObject naming layout valid codec tree
    let ancestors ← (List.ofFn (fun index => renderObject naming layout valid codec (parents index))).mapM id
    pure (renderCommit naming codec target ancestors metadata)

end Dasl
end Silmaril.Formats.Git
