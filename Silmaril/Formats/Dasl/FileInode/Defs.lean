module

public import Silmaril.Formats.Dasl.Wire.Profile.Defs
public import Mathlib.Data.List.Forall2

/-! An ordered DASL file DAG, not the UnixFS wire format. Internal links target
tagged inode objects; terminal links target raw byte pages. -/

@[expose] public section

namespace Silmaril.Formats.Dasl.FileInode

variable {Name : Type}

structure Limits where
  fanout : Nat
  pageSize : Nat
  fanout_pos : 0 < fanout
  pageSize_pos : 0 < pageSize

structure Child (Name : Type) where
  link : Link Name
  length : Int64
  deriving DecidableEq

def Child.size (child : Child Name) : Nat := child.length.toInt.toNat

abbrev Inode (Name : Type) := List (Child Name)
abbrev Bytes := List UInt8

def size (inode : Inode Name) : Nat := (inode.map Child.size).sum

def fits (limits : Limits) (inode : Inode Name) : Bool :=
  decide (inode.length ≤ limits.fanout) && inode.all (fun child => 0 < child.size)

def encodeChild (child : Child Name) : Shallow Name :=
  Encode.list.encode [Encode.link.encode child.link, Encode.signed.encode child.length]

def decodeChild (tree : Shallow Name) : Option (Child Name) := do
  let [.ref link, .i64 bits] ← Encode.list.decode? tree | none
  return ⟨link, bits.toInt64⟩

private theorem childRecovers (child : Child Name) : decodeChild (encodeChild child) = some child := by
  cases child
  simp [encodeChild, decodeChild, Encode.list.recovers, Encode.link, Encode.signed]

private theorem childrenRecover (inode : Inode Name) :
    (inode.map encodeChild).mapM decodeChild = some inode := by
  induction inode with
  | nil => rfl
  | cons child rest ih => simp [List.mapM_cons, childRecovers, ih]

def decodeEntries : List (Shallow Name) → Option (Inode Name)
  | [.string tag, children] =>
    if tag = "file-v1" then (Encode.list.decode? children).bind (List.mapM decodeChild) else none
  | _ => none

def codec : Encode.TotalCodec (Inode Name) (Shallow Name) where
  encode inode := Encode.list.encode [.string "file-v1", Encode.list.encode (inode.map encodeChild)]
  decode? tree := (Encode.list.decode? tree).bind decodeEntries
  recovers inode := by
    simp only [Encode.list.recovers, Option.bind_some, decodeEntries]
    exact childrenRecover inode

structure Snapshot (Name : Type) where
  objects : Name → Wire.ReadResult (Inode Name)
  blobs : Name → Wire.ReadResult ByteArray

/-- Successful observations cannot change in an extension. Neither missing nor invalid
observations assert that the extension has no binding. -/
structure Snapshot.Agrees (observed extension : Snapshot Name) : Prop where
  objects : ∀ ⦃name inode⦄, observed.objects name = .found inode → extension.objects name = .found inode
  blobs : ∀ ⦃name page⦄, observed.blobs name = .found page → extension.blobs name = .found page

/-- Adapt raw bytes with separate object and raw-page eligibility. This checks syntax
and link kind, not content hashes or the presence of all descendants. -/
def snapshot (profile : Wire.Profile Name) (blobName : Name → Bool)
    (read : Name → Option ByteArray) : Snapshot Name where
  objects name :=
    if profile.objectName name then
      match read name with
      | none => .missing
      | some raw => match profile.decode? codec raw with
        | none => .invalidWire
        | some inode => .found inode
    else .invalidWire
  blobs name :=
    if blobName name then
      match read name with
      | none => .missing
      | some page => .found page
    else .invalidWire

def daslSnapshot (read : Wire.Cid → Option ByteArray) : Snapshot Wire.Cid :=
  snapshot .dasl (fun cid => Wire.linkSupported (.blob cid)) read

def bdaslSnapshot (read : Wire.BdaslCid → Option ByteArray) : Snapshot Wire.BdaslCid :=
  snapshot .bdasl (fun cid => Wire.linkSupported (.blob cid)) read

/-- Independent full-content semantics. The depth bound is on link visits along a
path, not on the number of pages. Each child contributes exactly its declared length. -/
def Resolves (limits : Limits) (store : Snapshot Name) : Nat → Link Name → Nat → Bytes → Prop
  | 0, _, _, _ => False
  | _ + 1, .blob name, length, bytes =>
    ∃ page, store.blobs name = .found page ∧ page.size = length ∧
      page.size ≤ limits.pageSize ∧ bytes = page.data.toList
  | depth + 1, .obj name, length, bytes =>
    ∃ (inode : Inode Name) (chunks : List Bytes), store.objects name = .found inode ∧
      fits limits inode = true ∧ size inode = length ∧
      List.Forall₂ (fun child chunk => Resolves limits store depth child.link child.size chunk) inode chunks ∧
      bytes = chunks.flatten

inductive Error (Name : Type) where
  | missing (link : Link Name)
  | invalid (link : Link Name)
  | fuel (link : Link Name)
  | outOfBounds (length : Nat)
  deriving DecidableEq

def slice (bytes : Bytes) (offset count : Nat) : Bytes := (bytes.drop offset).take count

def fetch {Payload : Type} (link : Link Name) (result : Wire.ReadResult Payload) : Except (Error Name) Payload :=
  match result with
  | .missing => .error (.missing link)
  | .invalidWire => .error (.invalid link)
  | .found item => .ok item

def scan (visit : Child Name → Nat → Nat → Except (Error Name) Bytes) :
    Inode Name → Nat → Nat → Except (Error Name) Bytes
  | [], _, _ => .ok []
  | child :: rest, offset, count =>
    let here := min count (child.size - offset)
    let action := if here = 0 then .ok [] else visit child offset here
    do
      let head ← action
      let tail ← scan visit rest (offset - child.size) (count - here)
      .ok (head ++ tail)

/-- Visit just a child span, checking the expected size against what is fetched. -/
def visit (limits : Limits) (store : Snapshot Name) :
    Nat → Child Name → Nat → Nat → Except (Error Name) Bytes
  | 0, child, _, _ => .error (.fuel child.link)
  | depth + 1, child, offset, count =>
    match child.link with
    | .blob name => do
      let page ← fetch child.link (store.blobs name)
      if page.size = child.size ∧ page.size ≤ limits.pageSize then
        .ok (slice page.data.toList offset count)
      else .error (.invalid child.link)
    | .obj name => do
      let inode ← fetch child.link (store.objects name)
      if fits limits inode && decide (size inode = child.size) then
        scan (visit limits store depth) inode offset count
      else .error (.invalid child.link)

/-- Ranges are exact, not clipped. `none` requests the entire file; an empty range
at EOF succeeds without fetching children. The root is always an object. -/
def read (limits : Limits) (store : Snapshot Name) (fuel : Nat) (root : Name)
    (range : Option (Nat × Nat)) : Except (Error Name) Bytes :=
  match fuel with
  | 0 => .error (.fuel (.obj root))
  | depth + 1 => do
    let inode ← fetch (.obj root) (store.objects root)
    if fits limits inode then
      let (offset, count) := range.getD (0, size inode)
      if offset + count ≤ size inode then scan (visit limits store depth) inode offset count
      else .error (.outOfBounds (size inode))
    else .error (.invalid (.obj root))

end Silmaril.Formats.Dasl.FileInode
