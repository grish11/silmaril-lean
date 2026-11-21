module

public import Silmaril.Semantics.Rope.Defs
import Silmaril.Proofs.Semantics.Rope

public section

namespace Silmaril.Semantics.Rope

variable {Cell : Type}

theorem flatten_concat (left right : Tree Cell) : (left.concat right).flatten = left.flatten ++ right.flatten := by
  rw [Tree.flatten, Tree.concat, Proofs.Semantics.Rope.ofChildren_pages]
  simp [Tree.flatten]

theorem size_eq (tree : Tree Cell) : tree.size = tree.flatten.length := by
  rw [Tree.flatten, List.length_flatten, Tree.size]

theorem fromList_pages (geometry : Geometry) (cells : List Cell) : (fromList geometry cells).pages = geometry.pages cells :=
  Proofs.Semantics.Rope.fromList_pages geometry cells

theorem page_lengths (geometry : Geometry) (cells : List Cell) :
    ((fromList geometry cells).pages.map List.length) = sizes .left geometry.pageSize cells.length := by
  rw [fromList_pages]; exact Proofs.Semantics.Rope.payload_lengths geometry cells

theorem fromList_bound (geometry : Geometry) (cells : List Cell) : (fromList geometry cells).WidthBound geometry.fanout :=
  Proofs.Semantics.Rope.fromList_bound geometry cells

theorem fromList_level (geometry : Geometry) (cells : List Cell) : ∃ height, (fromList geometry cells).AtLevel height :=
  Proofs.Semantics.Rope.fromList_level geometry cells

@[simp] theorem flatten_fromList (geometry : Geometry) (cells : List Cell) : (fromList geometry cells).flatten = cells := by
  rw [Tree.flatten, fromList_pages]; exact Proofs.Semantics.Rope.payload_recovers geometry cells

@[simp] theorem flatten_normalize (geometry : Geometry) (tree : Tree Cell) :
    (normalize geometry tree).flatten = tree.flatten := flatten_fromList geometry tree.flatten

theorem normalize_eq_iff (geometry : Geometry) (left right : Tree Cell) :
    normalize geometry left = normalize geometry right ↔ left.flatten = right.flatten :=
  ⟨fun same => by simpa using congrArg Tree.flatten same, congrArg (fromList geometry)⟩

@[simp] theorem normalize_idempotent (geometry : Geometry) (tree : Tree Cell) :
    normalize geometry (normalize geometry tree) = normalize geometry tree :=
  (normalize_eq_iff geometry _ _).mpr (flatten_normalize geometry tree)

/-- Only the selected geometry's normal forms are equivalent to lists. -/
def equiv (geometry : Geometry) : {tree : Tree Cell // Normal geometry tree} ≃ List Cell where
  toFun tree := tree.val.flatten
  invFun cells := ⟨fromList geometry cells, by simp [Normal, normalize]⟩
  left_inv tree := Subtype.ext tree.property
  right_inv := flatten_fromList geometry

@[simp] theorem toBytes_ofBytes (geometry : Geometry) (bytes : ByteArray) :
    toBytes (ofBytes geometry bytes) = bytes := by cases bytes; simp [ofBytes, toBytes]

@[simp] theorem toString_ofString (geometry : Geometry) (text : String) :
    toString (ofString geometry text) = text := by simp [ofString, toString]

end Silmaril.Semantics.Rope
