module
public import Silmaril.Formats.Dasl.Defs
public import Silmaril.Formats.PER.Congruence.Thms

@[expose] public section
namespace Silmaril.Formats.Dasl.Tree
variable {Ref Name : Type}

/-- A nonrecursive DASL constructor, including references and resolved blobs.
Labels and payloads are part of the shape, not related child positions. -/
inductive Leaf (Ref Name : Type) where
  | ref (link : Ref)
  | blob (name : Name) (payload : ByteArray)
  | i64 (bits : UInt64)
  | bytes (payload : ByteArray)
  | string (text : String)
  | bool (value : Bool)
  | null

def Leaf.tree : Leaf Ref Name → Tree Ref Name
  | .ref link => .ref link
  | .blob name payload => .blob name payload
  | .i64 bits => .i64 bits
  | .bytes payload => .bytes payload
  | .string text => .string text
  | .bool value => .bool value
  | .null => .null

inductive Shape (Ref Name : Type) where
  | leaf (leaf : Leaf Ref Name)
  | obj (name : Name)
  | dict (keys : Finset String)
  | list (len : Nat)

def Shape.Pos : Shape Ref Name → Type
  | .leaf _ => Empty
  | .obj _ => Unit
  | .dict keys => ↥keys
  | .list len => Fin len

def Shape.make : (shape : Shape Ref Name) → (shape.Pos → Tree Ref Name) → Tree Ref Name
  | .leaf terminal, _ => terminal.tree
  | .obj name, child => .obj name (child ())
  | .dict keys, children => .dict keys children
  | .list len, children => .list len children

/-- Shared signature for `Value`, `Named`, `Partial`, `Mixed` and `Shallow`.
`Empty` in the relevant parameter makes references or resolved links impossible. -/
def constructors (enabled : Shape Ref Name → Prop) : PER.Constructors (Tree Ref Name) where
  Shape := Shape Ref Name
  Pos := Shape.Pos
  make := Shape.make
  enabled shape _ := enabled shape

/-- Explicitly choose all constructors for the distinguished signature.
For a genuinely partial domain, use `constructors` with an explicit guard instead. -/
instance : PER.HasConstructors (Tree Ref Name) := ⟨constructors (fun _ => True)⟩

/-- Direct rules with the actual constructor indices. There is no name-change rule. -/
structure Rules (enabled : Shape Ref Name → Prop) (R : PER (Tree Ref Name)) : Prop where
  leaf (leaf : Leaf Ref Name) : enabled (.leaf leaf) → R.Dom leaf.tree
  obj (name : Name) {left right : Tree Ref Name} :
    enabled (.obj name) → R.rel left right → R.rel (.obj name left) (.obj name right)
  dict (keys : Finset String) {left right : ↥keys → Tree Ref Name} :
    enabled (.dict keys) → (∀ key, R.rel (left key) (right key)) → R.rel (.dict keys left) (.dict keys right)
  list (len : Nat) {left right : Fin len → Tree Ref Name} :
    enabled (.list len) → (∀ index, R.rel (left index) (right index)) → R.rel (.list len left) (.list len right)

def Leaf.map {NextRef NextName : Type} (refs : Ref → NextRef) (names : Name → NextName) :
    Leaf Ref Name → Leaf NextRef NextName
  | .ref link => .ref (refs link)
  | .blob name payload => .blob (names name) payload
  | .i64 bits => .i64 bits
  | .bytes payload => .bytes payload
  | .string text => .string text
  | .bool value => .bool value
  | .null => .null

def Shape.map {NextRef NextName : Type} (refs : Ref → NextRef) (names : Name → NextName) :
    Shape Ref Name → Shape NextRef NextName
  | .leaf terminal => .leaf (terminal.map refs names)
  | .obj name => .obj (names name)
  | .dict keys => .dict keys
  | .list len => .list len

def Shape.shallow : Shape (Link Name) Name → Shape (Link Name) Empty
  | .obj name => .leaf (.ref (.obj name))
  | .leaf (.blob name _) => .leaf (.ref (.blob name))
  | .leaf (.ref link) => .leaf (.ref link)
  | .leaf (.i64 bits) => .leaf (.i64 bits)
  | .leaf (.bytes payload) => .leaf (.bytes payload)
  | .leaf (.string text) => .leaf (.string text)
  | .leaf (.bool value) => .leaf (.bool value)
  | .leaf .null => .leaf .null
  | .dict keys => .dict keys
  | .list len => .list len

end Silmaril.Formats.Dasl.Tree
