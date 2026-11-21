module

public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Insert

/-! Finite Git object syntax. File permissions are edge labels, not blob properties.
The filesystem view keeps those labels on file nodes for convenient editing. -/

@[expose] public section

namespace Silmaril.Formats.Git

inductive Mode where
  | regular | executable | symlink
  deriving DecidableEq, Repr

inductive Tag where
  | file (mode : Mode)
  | directory
  deriving DecidableEq, Repr

/-- A path component, not a pathspec or a platform checkout check. -/
def validComponent (name : String) : Bool :=
  name != "" && name != "." && name != ".." && !name.contains '/' && !name.contains (Char.ofNat 0)

abbrev Component := {name : String // validComponent name = true}
abbrev Path := List Component

def Component.parse? (name : String) : Option Component :=
  if valid : validComponent name = true then some ⟨name, valid⟩ else none

structure Directory (Key Item : Type) where
  keys : Finset Key
  get : ↥keys → Item

namespace Directory

variable {Key Item Out : Type} [DecidableEq Key]

def lookup (dir : Directory Key Item) (key : Key) : Option Item :=
  if found : key ∈ dir.keys then some (dir.get ⟨key, found⟩) else none

def insert (dir : Directory Key Item) (key : Key) (item : Item) : Directory Key Item :=
  ⟨Insert.insert key dir.keys, fun entry =>
    if same : entry.val = key then item
    else dir.get ⟨entry.val, (Finset.mem_insert.mp entry.property).resolve_left same⟩⟩

def remove (dir : Directory Key Item) (key : Key) : Directory Key Item :=
  ⟨dir.keys.erase key, fun entry => dir.get ⟨entry.val, Finset.mem_of_mem_erase entry.property⟩⟩

omit [DecidableEq Key] in
def map (dir : Directory Key Item) (convert : Item → Out) : Directory Key Out :=
  ⟨dir.keys, fun key => convert (dir.get key)⟩

end Directory

inductive Tree where
  | file (mode : Mode) (bytes : ByteArray)
  | dir (names : Finset String) (children : ↥names → Tree)

inductive Indexed : Tag → Type where
  | blob (mode : Mode) (bytes : ByteArray) : Indexed (.file mode)
  | tree (names : Finset String) (modes : ↥names → Tag)
      (children : (name : ↥names) → Indexed (modes name)) : Indexed .directory

def Tree.tag : Tree → Tag
  | .file mode _ => .file mode
  | .dir .. => .directory

def Tree.indexed : (tree : Tree) → Indexed tree.tag
  | .file mode bytes => .blob mode bytes
  | .dir names children => .tree names (fun name => (children name).tag)
      (fun name => (children name).indexed)

def Indexed.erase : {tag : Tag} → Indexed tag → Tree
  | _, .blob mode bytes => .file mode bytes
  | _, .tree names _ children => .dir names (fun name => (children name).erase)

def Tree.Valid : Tree → Prop
  | .file .. => True
  | .dir _ children => ∀ name, validComponent name.val = true ∧ (children name).Valid

def Tree.lookup : Tree → Path → Option Tree
  | tree, [] => some tree
  | .file .., _ :: _ => none
  | .dir names children, name :: rest =>
    if found : name.val ∈ names then lookup (children ⟨name.val, found⟩) rest else none

/-- Insert or replace one immediate child; a file is not converted to a directory. -/
def Tree.insert (directory : Tree) (name : Component) (child : Tree) : Option Tree :=
  match directory with
  | .file .. => none
  | .dir names children =>
    let dir := (Directory.mk names children).insert name.val child
    some (.dir dir.keys dir.get)

def Tree.remove (directory : Tree) (name : Component) : Option Tree :=
  match directory with
  | .file .. => none
  | .dir names children =>
    let dir := (Directory.mk names children).remove name.val
    some (.dir dir.keys dir.get)

def Indexed.mapBytes (convert : Mode → ByteArray → ByteArray) : {tag : Tag} → Indexed tag → Indexed tag
  | _, .blob mode bytes => .blob mode (convert mode bytes)
  | _, .tree names modes children => .tree names modes (fun name => (children name).mapBytes convert)

inductive Kind where
  | blob | tree | commit
  deriving DecidableEq, Repr

inductive EntryMode where
  | file (mode : Mode)
  | directory
  | gitlink
  deriving DecidableEq, Repr

def EntryMode.kind : EntryMode → Kind
  | .file _ => .blob
  | .directory => .tree
  | .gitlink => .commit

def Tag.entryMode : Tag → EntryMode
  | .file mode => .file mode
  | .directory => .directory

structure Entry (Target : Type) where
  mode : EntryMode
  target : Target
  deriving DecidableEq, Repr

def Entry.map {From To : Type} (convert : From → To) (entry : Entry From) : Entry To :=
  ⟨entry.mode, convert entry.target⟩

abbrev ShallowTree (Key Target : Type) := Directory Key (Entry Target)

def ShallowTree.mapTargets {Key From To : Type} (dir : ShallowTree Key From) (convert : From → To) :
    ShallowTree Key To := dir.map (Entry.map convert)

/-- Parents are ordered, not a set. Tree and parent carriers can differ. -/
structure Commit (Root Parent Meta : Type) where
  tree : Root
  parents : List Parent
  metadata : Meta
  deriving DecidableEq, Repr

def Commit.map {Root Parent Meta Root' Parent' Meta' : Type}
    (root : Root → Root') (parent : Parent → Parent') (metadata : Meta → Meta')
    (commit : Commit Root Parent Meta) : Commit Root' Parent' Meta' :=
  ⟨root commit.tree, commit.parents.map parent, metadata commit.metadata⟩

/-- One DASL metadata profile; not a parser for Git commit headers. -/
structure Metadata where
  message : ByteArray
  timestamp : Int64
  deriving DecidableEq

/-- Finite unfolding of an object graph. Names can represent shared objects;
stopping at a reference makes no availability assertion (including gitlinks).
Use `Empty` for an entirely expanded finite graph. -/
inductive Object (Key Ref Meta : Type) : Kind → Type where
  | ref (kind : Kind) (name : Ref) : Object Key Ref Meta kind
  | blob (bytes : ByteArray) : Object Key Ref Meta .blob
  | tree (names : Finset Key) (modes : ↥names → EntryMode)
      (children : (name : ↥names) → Object Key Ref Meta (modes name).kind) : Object Key Ref Meta .tree
  | commit (tree : Object Key Ref Meta .tree) (count : Nat)
      (parents : Fin count → Object Key Ref Meta .commit) (metadata : Meta) : Object Key Ref Meta .commit

abbrev Expanded (Key Meta : Type) := Object Key Empty Meta

def Object.treeEntries? {Key Ref Meta Target : Type}
    (child : {kind : Kind} → Object Key Ref Meta kind → Target) :
    Object Key Ref Meta .tree → Option (ShallowTree Key Target)
  | .ref .. => none
  | .tree names modes children => some ⟨names, fun name => ⟨modes name, child (children name)⟩⟩

def Object.commitParts? {Key Ref Meta Root Parent : Type}
    (treeView : Object Key Ref Meta .tree → Root) (parentView : Object Key Ref Meta .commit → Parent) :
    Object Key Ref Meta .commit → Option (Commit Root Parent Meta)
  | .ref .. => none
  | .commit root _ parents metadata => some ⟨treeView root, List.ofFn (parentView ∘ parents), metadata⟩

def Tree.toObject {Ref Meta : Type} : (tree : Tree) → Object String Ref Meta tree.tag.entryMode.kind
  | .file _ bytes => .blob bytes
  | .dir names children => .tree names (fun name => (children name).tag.entryMode)
      (fun name => (children name).toObject)

end Silmaril.Formats.Git
