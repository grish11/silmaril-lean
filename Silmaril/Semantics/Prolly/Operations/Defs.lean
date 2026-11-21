module

public import Silmaril.Semantics.OrderedMap.Operations.Defs
public import Silmaril.Semantics.Prolly.Routing.Thms

@[expose] public section

namespace Silmaril.Semantics.Prolly

variable {Key Payload Error : Type} [LinearOrder Key]

/-- Shape, strict key order, separators and width; independent of canonical cuts. -/
def Tree.Valid (tree : Tree Key Payload) (width : Nat) : Prop := tree.Routable ∧ tree.Bounded width

/-- A typed finite map backed by the existing Prolly AST, with no naming dependency. -/
abbrev TypedMap (Key Payload : Type) [LinearOrder Key] (width : Nat) := { tree : Tree Key Payload // tree.Valid width }

abbrev TypedSet (Key : Type) [LinearOrder Key] (width : Nat) := TypedMap Key Unit width

namespace TypedMap

variable {width : Nat}

def view (tree : TypedMap Key Payload width) : OrderedMap Key Payload :=
  ⟨tree.val.entries, tree.property.1.1⟩

def ofMap (policy : Policy Key) (map : OrderedMap Key Payload) : TypedMap Key Payload policy.width :=
  ⟨build policy map, build_routable policy map, build_bounded policy map⟩

/-- Baseline semantics: interpret both maps, combine them, and rebuild the entire
result with the chosen policy. No locality is promised. -/
def combine (policy : Policy Key) (kind : OrderedMap.Combine) (overlap : OrderedMap.Overlap Key Payload Error)
    (left right : TypedMap Key Payload width) : Except Error (TypedMap Key Payload policy.width) :=
  ((view left).combine kind overlap (view right)).map (ofMap policy)

end TypedMap
end Silmaril.Semantics.Prolly
