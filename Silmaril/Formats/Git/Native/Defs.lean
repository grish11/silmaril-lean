module

public import Silmaril.Formats.Git.Dasl.Thms

/-! The uncompressed native Git object bytes (the hash preimage), not a pack
format or the zlib-compressed loose file. The commit profile is deliberately narrow. -/

@[expose] public section

namespace Silmaril.Formats.Git.Native

inductive Algorithm where
  | sha1 | sha256
  deriving DecidableEq, Repr

def Algorithm.width : Algorithm → Nat
  | .sha1 => 20
  | .sha256 => 32

abbrev NameBytes (algorithm : Algorithm) := {bytes : ByteArray // bytes.size = algorithm.width}
abbrev NameCodec (algorithm : Algorithm) (Name : Type) :=
  Silmaril.Formats.Dasl.Encode.TotalCodec Name (NameBytes algorithm)

def nameBytes? (algorithm : Algorithm) (bytes : ByteArray) : Option (NameBytes algorithm) :=
  if width : bytes.size = algorithm.width then some ⟨bytes, width⟩ else none

def nameBytesCodec (algorithm : Algorithm) : NameCodec algorithm (NameBytes algorithm) :=
  ⟨id, some, fun _ => rfl⟩

def kindText : Kind → String
  | .blob => "blob"
  | .tree => "tree"
  | .commit => "commit"

def header (kind : Kind) (size : Nat) : ByteArray :=
  (kindText kind ++ " " ++ toString size).toByteArray.push 0

def loose (kind : Kind) (payload : ByteArray) : ByteArray := header kind payload.size ++ payload

def modeText : EntryMode → String
  | .directory => "40000"
  | .file .regular => "100644"
  | .file .executable => "100755"
  | .file .symlink => "120000"
  | .gitlink => "160000"

open Silmaril.Formats.Dasl.Prolly (ByteKey)
open Silmaril.Formats.Dasl.Encode (TotalCodec)

variable {Name Key : Type} {algorithm : Algorithm}

/-- Git compares unsigned basename bytes, with slash as the virtual terminator
only for directories; gitlinks and symlinks use NUL like regular files. -/
def orderKey (entry : ByteKey × Entry Name) : ByteKey :=
  entry.1 ++ [if entry.2.mode = .directory then 47 else 0]

def treeOrder (entries : List (ByteKey × Entry Name)) : List (ByteKey × Entry Name) :=
  entries.mergeSort (fun left right => decide (orderKey left ≤ orderKey right))

def treeRecord (names : NameCodec algorithm Name) (entry : ByteKey × Entry Name) : ByteArray :=
  (modeText entry.2.mode ++ " ").toByteArray ++ ((entry.1.map UInt8.ofFin).toByteArray.push 0) ++
    (names.encode entry.2.target).val

def treePayload? (names : NameCodec algorithm Name) (dir : ShallowTree ByteKey Name) : Option ByteArray :=
  let entries := dir.ordered.entries
  if entries.all (fun entry => Dasl.validByteComponent entry.1) then
    some ((treeOrder entries).foldl (fun bytes entry => bytes ++ treeRecord names entry) ByteArray.empty)
  else none

structure Person where
  displayName : String
  email : String
  seconds : Nat

def Person.valid (person : Person) : Bool :=
  let printable := fun (char : Char) => decide (32 ≤ char.toNat ∧ char.toNat < 127) && char != '<' && char != '>'
  !person.displayName.isEmpty && person.displayName.toList.all printable &&
    !person.displayName.startsWith " " && !person.displayName.endsWith " " &&
    !person.email.isEmpty && person.email.toList.all (fun char => printable char && char != ' ') &&
    decide (person.seconds < 2^63)

def Person.line (label : String) (person : Person) : String :=
  label ++ " " ++ person.displayName ++ " <" ++ person.email ++ "> " ++ toString person.seconds ++ " +0000\n"

structure CommitMetadata where
  author : Person
  committer : Person
  message : String

def oidText (names : NameCodec algorithm Name) (name : Name) : String :=
  let digit := fun value : Nat => Char.ofNat (if value < 10 then 48 + value else 87 + value)
  String.ofList ((names.encode name).val.data.toList.flatMap fun byte =>
    [digit (byte.toNat / 16), digit (byte.toNat % 16)])

/-- Ordered `tree` and `parent` lines, then one author and one committer line,
a blank LF line, and exact UTF-8 message text (no NUL, no normalization). -/
def commitPayload? (names : NameCodec algorithm Name) (commit : Commit Name Name CommitMetadata) : Option ByteArray :=
  let data := commit.metadata
  if data.author.valid && data.committer.valid && !data.message.contains (Char.ofNat 0) then
    let header := "tree " ++ oidText names commit.tree ++ "\n"
    let parents := String.join (commit.parents.map fun parent => "parent " ++ oidText names parent ++ "\n")
    some ((header ++ parents ++ data.author.line "author" ++ data.committer.line "committer" ++ "\n" ++
      data.message).toByteArray)
  else none

/-- Serialize the full native preimage of an already named commit. -/
def commitBytes? (names : NameCodec algorithm Name) (commit : Commit Name Name CommitMetadata) : Option ByteArray :=
  (commitPayload? names commit).map (loose .commit)

/-- An opaque reference retains its name, but does not supply an object preimage. -/
inductive View (Name : Type) where
  | opaque (name : Name)
  | encoded (bytes : ByteArray)

def View.target (assign : ByteArray → Name) : View Name → Name
  | .opaque name => name
  | .encoded bytes => assign bytes

def View.Matches (rel : Semantics.Naming.Relation Name ByteArray) (name : Name) : View Name → Prop
  | .opaque target => target = name
  | .encoded bytes => rel name bytes

/-- The choice of a name for each emitted child is fixed by `assign`; a caller
using a reference naming relation can require that choice to satisfy the relation. -/
structure Profile (algorithm : Algorithm) (Key Name : Type) where
  key : TotalCodec Key ByteKey
  names : NameCodec algorithm Name
  assign : ByteArray → Name

def Profile.Compatible (profile : Profile algorithm Key Name) (rel : Semantics.Naming.Relation Name ByteArray) : Prop :=
  ∀ bytes, rel (profile.assign bytes) bytes

def renderDir (profile : Profile algorithm Key Name) (keys : Finset Key) (modes : ↥keys → EntryMode)
    (children : ↥keys → Option (View Name)) : Option (View Name) := do
  if ready : ∀ key (hit : key ∈ keys), (children ⟨key, hit⟩).isSome = true then
    let dir : ShallowTree Key Name := ⟨keys, fun key =>
      ⟨modes key, ((children key).get (ready key.val key.property)).target profile.assign⟩⟩
    let payload ← treePayload? profile.names (dir.rekey profile.key)
    pure (.encoded (loose .tree payload))
  else none

def renderTree (profile : Profile algorithm String Name) : Tree → Option (View Name)
  | .file _ payload => some (.encoded (loose .blob payload))
  | .dir keys children => renderDir profile keys (fun key => (children key).tag.entryMode)
      (fun key => renderTree profile (children key))

def renderObject (profile : Profile algorithm Key Name) :
    {kind : Kind} → Object Key Name CommitMetadata kind → Option (View Name)
  | _, .ref _ name => some (.opaque name)
  | _, .blob payload => some (.encoded (loose .blob payload))
  | _, .tree keys modes children => renderDir profile keys modes (fun key => renderObject profile (children key))
  | _, .commit root _ parents metadata => do
    let tree ← renderObject profile root
    let ancestors ← (List.ofFn (fun index => renderObject profile (parents index))).mapM id
    let bytes ← commitBytes? profile.names ⟨tree.target profile.assign,
      ancestors.map (View.target profile.assign), metadata⟩
    pure (.encoded bytes)

def names {Source : Type} (rel : Semantics.Naming.Relation Name ByteArray) (render : Source → Option (View Name)) :
    Semantics.Naming.Relation Name Source :=
  fun name source => ∃ view, render source = some view ∧ view.Matches rel name

end Silmaril.Formats.Git.Native
