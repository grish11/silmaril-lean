module

public import Silmaril.Formats.Dasl.Encode.Map.Defs
public import Silmaril.Formats.Dasl.Resolve.Defs
public import Silmaril.Formats.SExp.Proper

/-! Decoded DASL profiles for the proper and dotted S-expression types. A syntax root
is always inline (and can be stored as an object). Placement applies only to children.
The atom dictionary boxes opaque bytes, including bytes that happen to spell a CID. -/

@[expose] public section

namespace Silmaril.Formats.Dasl.SExp

variable {Atom Name Ref Item Target : Type}

/-- Application-supplied atom payload codec. No text or hash convention is imposed. -/
abbrev Payload (Atom : Type) := Encode.TotalCodec Atom ByteArray

def Payload.bytes : Payload ByteArray := ⟨id, some, fun _ => rfl⟩

def Payload.utf8 : Payload String :=
  ⟨String.toUTF8, String.fromUTF8?, fun text => by
    simp [String.fromUTF8?, text.isValidUTF8]⟩

/-- Zero-based child indices, nearest ancestor first. Car is 0 and cdr is 1. -/
abbrev Path := List Nat

abbrev Placement (Expr Name : Type) := Path → Expr → Option Name

def edge (put : Placement Item Name) (path : Path) (item : Item) (tree : Tree Ref Name) : Tree Ref Name :=
  match put path item with
  | none => tree
  | some name => .obj name tree

def inlineAll : Placement Item Name := fun _ _ => none

def linkAll (name : Path → Item → Name) : Placement Item Name := fun path item => some (name path item)

def properNonAtoms (name : Path → Formats.SExp Atom → Name) : Placement (Formats.SExp Atom) Name
  | _, .atom _ => none
  | path, item@(.list ..) => some (name path item)

/-- Nil is a syntactic child too: it is not an atom. -/
def dottedNonAtoms (name : Path → SExp2 Atom → Name) : Placement (SExp2 Atom) Name
  | _, .atom _ => none
  | path, item => some (name path item)

def atomKeys : Finset String := {"sexp:atom"}

def atomNode (payload : Payload Atom) (atom : Atom) : Tree Ref Name :=
  .dict atomKeys (fun _ => .bytes (payload.encode atom))

def readAtom (payload : Payload Atom) : Tree Ref Name → Option Atom
  | .bytes bytes => payload.decode? bytes
  | _ => none

def readAtomFields (payload : Payload Atom) (keys : Finset String)
    (values : ↥keys → Tree Ref Name) : Option Atom :=
  if hit : keys = atomKeys then readAtom payload (values ⟨"sexp:atom", hit.symm ▸ by simp [atomKeys]⟩)
  else none

def collect {len : Nat} (items : Fin len → Option Item) : Option (Fin len → Item) :=
  if ready : ∀ index, (items index).isSome then some (fun index => (items index).get (ready index))
  else none

namespace Proper

def writeAt (payload : Payload Atom) (put : Placement (Formats.SExp Atom) Name) (path : Path) :
    Formats.SExp Atom → Tree Ref Name
  | .atom atom => atomNode payload atom
  | .list len items => .list len fun index =>
      let childPath := index.val :: path
      edge put childPath (items index) (writeAt payload put childPath (items index))

def write (payload : Payload Atom) (put : Placement (Formats.SExp Atom) Name) (item : Formats.SExp Atom) :
    Tree Ref Name := writeAt payload put [] item

/-- Opens a resolved object only in a child slot. A missing child is not defaulted. -/
def readAt (payload : Payload Atom) : Bool → Tree Ref Name → Option (Formats.SExp Atom)
  | _, .dict keys values => (readAtomFields payload keys values).map .atom
  | _, .list len values => (collect fun index => readAt payload true (values index)).map (.list len)
  | child, .obj _ target => if child then readAt payload false target else none
  | _, _ => none

def read (payload : Payload Atom) : Tree Ref Name → Option (Formats.SExp Atom) := readAt payload false

end Proper

namespace Dotted

inductive Layout where
  | dict | array
  deriving DecidableEq

def pairKeys : Finset String := {"car", "cdr"}

def pair (layout : Layout) (car cdr : Tree Ref Name) : Tree Ref Name :=
  match layout with
  | .dict => .dict pairKeys (fun key => if key.val = "car" then car else cdr)
  | .array => Encode.pairEntry.encode (car, cdr)

def writeAt (layout : Layout) (payload : Payload Atom) (put : Placement (SExp2 Atom) Name) (path : Path) :
    SExp2 Atom → Tree Ref Name
  | .nil => .null
  | .atom atom => atomNode payload atom
  | .cons car cdr => pair layout
      (edge put (0 :: path) car (writeAt layout payload put (0 :: path) car))
      (edge put (1 :: path) cdr (writeAt layout payload put (1 :: path) cdr))

def write (layout : Layout) (payload : Payload Atom) (put : Placement (SExp2 Atom) Name) (item : SExp2 Atom) :
    Tree Ref Name := writeAt layout payload put [] item

def readAt (layout : Layout) (payload : Payload Atom) : Bool → Tree Ref Name → Option (SExp2 Atom)
  | _, .null => some .nil
  | _, .dict keys values =>
    if hit : layout = .dict ∧ keys = pairKeys then do
      let car ← readAt layout payload true (values ⟨"car", hit.2.symm ▸ by simp [pairKeys]⟩)
      let cdr ← readAt layout payload true (values ⟨"cdr", hit.2.symm ▸ by simp [pairKeys]⟩)
      pure (.cons car cdr)
    else (readAtomFields payload keys values).map .atom
  | _, .list 2 values =>
    if layout = .array then do
      let car ← readAt layout payload true (values 0)
      let cdr ← readAt layout payload true (values 1)
      pure (.cons car cdr)
    else none
  | child, .obj _ target => if child then readAt layout payload false target else none
  | _, _ => none

def read (layout : Layout) (payload : Payload Atom) : Tree Ref Name → Option (SExp2 Atom) :=
  readAt layout payload false

end Dotted

/-- Forget placement and existing aliases, then write the requested normal form.
This is not a store mutation or a procedure for allocating names. -/
def normalize (read : Tree Ref Name → Option Item) (write : Item → Target) (value : Tree Ref Name) :
    Option Target := (read value).map write

/-- A root observation for a pullback: use the repository's finite full expansion followed
by syntax recovery. In particular, the name relation is not asserted to have unique names. -/
def Names (store : Store Name) (read : Partial Name → Option Item) (root : Name) (item : Item) : Prop :=
  ∃ tree, FullNames store root tree ∧ read tree.embed = some item

/-- Successful recovery from a partial observation of the same root. The observation is
still available separately as a `Partial Name` when recovery is blocked by opaque links. -/
def Observes (store : Store Name) (read : Partial Name → Option Item) (root : Name) (item : Item) : Prop :=
  ∃ tree, PartialNames store root tree ∧ read tree = some item

/-- Two roots alias when they both resolve finitely to the same syntax. Equality of
opaque CIDs, shallow trees, encoded bytes or partial observations is not required. -/
def Aliases (store : Store Name) (read : Partial Name → Option Item) (left right : Name) : Prop :=
  ∃ item, Names store read left item ∧ Names store read right item

namespace Dotted

/-- Change representation (and optionally placement) without changing the datum. -/
def transcode (source target : Layout) (payload : Payload Atom) (put : Placement (SExp2 Atom) Name)
    (tree : Tree Ref Name) : Option (Tree Ref Name) :=
  normalize (read source payload) (write target payload put) tree

end Dotted

end Silmaril.Formats.Dasl.SExp
