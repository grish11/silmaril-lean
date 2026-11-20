module

public import Silmaril.Semantics.OrderedMap.Defs
public import Silmaril.Semantics.Naming.Defs

@[expose] public section

namespace Silmaril.Semantics.Prolly

variable {Key Payload Name Item : Type}

/-- Cut on a bucket hit after at least two items, or at the width limit.
The bucketer sees only the level and final key; values and names do not affect chunk boundaries. -/
structure Policy (Key : Type) where
  width : Nat
  minWidth : 2 ≤ width
  bucket : Nat → Key → Bool

def Policy.cut (policy : Policy Key) (level count : Nat) (key : Key) : Bool :=
  decide (policy.width ≤ count) || (decide (2 ≤ count) && policy.bucket level key)

def chunkFrom (cut : Nat → Item → Bool) (current : List Item) : List Item → List (List Item)
  | [] => if current.isEmpty then [] else [current]
  | head :: tail =>
    if cut (current.length + 1) head then (current ++ [head]) :: chunkFrom cut [] tail
    else chunkFrom cut (current ++ [head]) tail

def chunk (cut : Nat → Item → Bool) (items : List Item) : List (List Item) := chunkFrom cut [] items

/-- A node at a positive level has children at exactly the immediately preceding level. -/
@[reducible] def Content (Key Payload : Type) : Nat → Type
  | 0 => Payload
  | level + 1 => List (Key × Content Key Payload level)

abbrev Node (Key Payload : Type) (level : Nat) := List (Key × Content Key Payload level)

structure Tree (Key Payload : Type) where
  level : Nat
  root : Node Key Payload level

def flatten : (level : Nat) → Node Key Payload level → List (Key × Payload)
  | 0, entries => entries
  | level + 1, children => children.flatMap fun child => flatten level child.2

def Tree.entries (tree : Tree Key Payload) : List (Key × Payload) := flatten tree.level tree.root

/-- Each separator is the maximum key of its child if keys are in ascending order.
This lifts nonempty chunks and ignores only empty lists. -/
def lift (chunks : List (List (Key × Item))) : List (Key × List (Key × Item)) :=
  chunks.filterMap fun
    | [] => none
    | first :: rest => some ((rest.getLastD first).1, first :: rest)

def grow (policy : Policy Key) : (fuel level : Nat) → Node Key Payload level → Tree Key Payload
  | 0, level, node => ⟨level, node⟩
  | fuel + 1, level, node =>
    if node.length ≤ policy.width then ⟨level, node⟩
    else grow policy fuel (level + 1) (lift (chunk (fun count pair => policy.cut level count pair.1) node))

/-- Stop at one root once it fits; internal grouping is deterministic for fixed policy. -/
def build [LinearOrder Key] (policy : Policy Key) (map : OrderedMap Key Payload) : Tree Key Payload :=
  grow policy map.entries.length 0 map.entries

def Node.Bounded (width : Nat) : (level : Nat) → Node Key Payload level → Prop
  | 0, node => node.length ≤ width
  | level + 1, node => node.length ≤ width ∧ ∀ child ∈ node, Node.Bounded width level child.2

def Node.ChildrenBounded (width : Nat) : (level : Nat) → Node Key Payload level → Prop
  | 0, _ => True
  | level + 1, node => ∀ child ∈ node, Node.Bounded width level child.2

def Tree.Bounded (width : Nat) (tree : Tree Key Payload) : Prop := Node.Bounded width tree.level tree.root

inductive Block (Name Key Payload : Type) where
  | leaf (entries : List (Key × Payload))
  | branch (level : Nat) (children : List (Key × Name))
  deriving DecidableEq, Repr

def nodeBlock (address : Block Name Key Payload → Name) : (level : Nat) → Node Key Payload level →
    Block Name Key Payload
  | 0, node => .leaf node
  | level + 1, node => .branch (level + 1) (node.map fun child => (child.1, address (nodeBlock address level child.2)))

def blockOccurrences (address : Block Name Key Payload → Name) : (level : Nat) → Node Key Payload level →
    List (Block Name Key Payload)
  | 0, node => [nodeBlock address 0 node]
  | level + 1, node => nodeBlock address (level + 1) node :: node.flatMap fun child => blockOccurrences address level child.2

def Tree.rootName (tree : Tree Key Payload) (address : Block Name Key Payload → Name) : Name :=
  address (nodeBlock address tree.level tree.root)

/-- Compute all child names before forming the parent block. Failure at any
reachable block prevents a root name from being returned. -/
def nameNode? (nameBlock? : Block Name Key Payload → Option Name) :
    (level : Nat) → Node Key Payload level → Option Name
  | 0, node => nameBlock? (.leaf node)
  | level + 1, node => do
    let children ← node.mapM fun child => (nameNode? nameBlock? level child.2).map (child.1, ·)
    nameBlock? (.branch (level + 1) children)

def Tree.rootName? (tree : Tree Key Payload) (nameBlock? : Block Name Key Payload → Option Name) : Option Name :=
  nameNode? nameBlock? tree.level tree.root

/-- Replay through APIs that take a total address. After successful naming, no
reached block uses the off-domain value. -/
def replayAddress (nameBlock? : Block Name Key Payload → Option Name) (offDomain : Name) :
    Block Name Key Payload → Name := fun block => (nameBlock? block).getD offDomain

/-- An address assignment is tested at each block it induces, not merely at its root. -/
def Tree.Admits (tree : Tree Key Payload) (nameBlock? : Block Name Key Payload → Option Name)
    (address : Block Name Key Payload → Name) : Prop :=
  ∀ block ∈ blockOccurrences address tree.level tree.root, nameBlock? block = some (address block)

/-- The least relation containing the observations of the encoded tree. A supplied
address determines the name of each block but is not presumed collision free. -/
def Tree.observations (tree : Tree Key Payload) (address : Block Name Key Payload → Name) :
    Naming.Relation Name (Block Name Key Payload) :=
  fun name block => name = address block ∧ block ∈ blockOccurrences address tree.level tree.root

end Silmaril.Semantics.Prolly
