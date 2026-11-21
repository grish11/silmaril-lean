module

public import Silmaril.Semantics.Prolly.Operations.Defs
public import Silmaril.Semantics.OrderedMap.Operations.Thms

public section

namespace Silmaril.Semantics.Prolly.TypedMap

open Silmaril.Semantics.Prolly

variable {Key Payload Error : Type} [LinearOrder Key] {width : Nat}

@[simp] theorem view_ofMap (policy : Policy Key) (map : OrderedMap Key Payload) :
    view (ofMap policy map) = map := OrderedMap.ext (build_entries policy map)

/-- The typed AST operation commutes with interpretation to finite maps. -/
theorem view_combine (policy : Policy Key) (kind : OrderedMap.Combine) (overlap : OrderedMap.Overlap Key Payload Error)
    (left right : TypedMap Key Payload width) :
    (combine policy kind overlap left right).map view = (view left).combine kind overlap (view right) := by
  unfold combine
  cases (view left).combine kind overlap (view right) <;> simp [Except.map]

theorem ofMap_canonical (policy : Policy Key) {left right : OrderedMap Key Payload}
    (same : ∀ key, left.lookup? key = right.lookup? key) : ofMap policy left = ofMap policy right :=
  congrArg (ofMap policy) (OrderedMap.eq_of_lookup same)

end Silmaril.Semantics.Prolly.TypedMap
