module

public import Mathlib.Logic.Equiv.Defs
public import Silmaril.Semantics.MeasuredSequence.Defs
import Silmaril.Proofs.Semantics.MeasuredSequence

public section

namespace Silmaril.Semantics.MeasuredSequence

variable {Item : Type} {tree left right : Tree Item}

theorem size_spec (valid : Valid tree) : size tree = (flatten tree).length :=
  Proofs.Semantics.MeasuredSequence.sizeSpec valid

theorem append_valid (validLeft : Valid left) (validRight : Valid right) : Valid (append left right) :=
  Proofs.Semantics.MeasuredSequence.appendValid validLeft validRight

theorem flatten_append (left right : Tree Item) : flatten (append left right) = flatten left ++ flatten right :=
  Proofs.Semantics.MeasuredSequence.flattenAppend left right

theorem get_spec (valid : Valid tree) (index : Nat) : get? tree index = (flatten tree)[index]? :=
  Proofs.Semantics.MeasuredSequence.getSpec valid index

theorem set_valid (valid : Valid tree) (index : Nat) (item : Item) : Valid (set tree index item) :=
  Proofs.Semantics.MeasuredSequence.setValid valid index item

theorem set_spec (valid : Valid tree) (index : Nat) (item : Item) :
    flatten (set tree index item) = (flatten tree).set index item :=
  Proofs.Semantics.MeasuredSequence.setSpec valid index item

theorem split_valid (valid : Valid tree) (index : Nat) :
    Valid (splitAt tree index).1 ∧ Valid (splitAt tree index).2 :=
  Proofs.Semantics.MeasuredSequence.splitValid valid index

theorem split_spec (valid : Valid tree) (index : Nat) :
    flatten (splitAt tree index).1 = (flatten tree).take index ∧
      flatten (splitAt tree index).2 = (flatten tree).drop index :=
  Proofs.Semantics.MeasuredSequence.splitSpec valid index

theorem splice_valid (valid : Valid tree) (validInsert : Valid right) (index count : Nat) :
    Valid (splice tree index count right) :=
  Proofs.Semantics.MeasuredSequence.spliceValid valid validInsert index count

theorem splice_spec (valid : Valid tree) (index count : Nat) (inserted : Tree Item) :
    flatten (splice tree index count inserted) =
      (flatten tree).take index ++ (flatten inserted ++ ((flatten tree).drop index).drop count) :=
  Proofs.Semantics.MeasuredSequence.spliceSpec valid index count inserted

theorem of_list_valid (items : List Item) : Valid (ofList items) :=
  Proofs.Semantics.MeasuredSequence.ofListValid items

theorem of_list_spec (items : List Item) : flatten (ofList items) = items :=
  Proofs.Semantics.MeasuredSequence.ofListSpec items

theorem of_list_bisected (items : List Item) : Bisected (ofList items) :=
  Proofs.Semantics.MeasuredSequence.ofListBisected items

theorem normalize_spec (tree : Tree Item) : flatten (normalize tree) = flatten tree :=
  of_list_spec (flatten tree)

theorem normalize_valid (tree : Tree Item) : Valid (normalize tree) := of_list_valid (flatten tree)

theorem normalize_bisected (tree : Tree Item) : Bisected (normalize tree) := of_list_bisected (flatten tree)

theorem of_list_normal (items : List Item) : Normal (ofList items) := by
  change ofList (flatten (ofList items)) = ofList items
  rw [of_list_spec]

theorem normalize_idempotent (tree : Tree Item) : Normal (normalize tree) := of_list_normal (flatten tree)

theorem normalize_eq_iff {left right : Tree Item} : normalize left = normalize right ↔ flatten left = flatten right :=
  ⟨fun same => (normalize_spec left).symm.trans ((congrArg flatten same).trans (normalize_spec right)),
    congrArg ofList⟩

/-- Lists correspond to the normalized representations, not to all mutable shapes. -/
def normalEquiv : { tree : Tree Item // Normal tree } ≃ List Item where
  toFun tree := flatten tree.val
  invFun items := ⟨ofList items, of_list_normal items⟩
  left_inv tree := Subtype.ext tree.property
  right_inv := of_list_spec

end Silmaril.Semantics.MeasuredSequence
