module

public import Silmaril.Formats.Dasl.Encode.Thms
public import Silmaril.Semantics.MeasuredSequence.Thms

/-! The editable layout preserves joins; the normalized layout stores only the
elements. Neither serializes cached lengths. The caller selects the layout. -/

@[expose] public section

namespace Silmaril.Formats.Dasl.MeasuredSequence

variable {Item Name : Type}

abbrev Editable (Item : Type) := { tree : Semantics.MeasuredSequence.Tree Item // Semantics.MeasuredSequence.Valid tree }

abbrev Normalized (Item : Type) := { tree : Semantics.MeasuredSequence.Tree Item // Semantics.MeasuredSequence.Normal tree }

def branchShape (left right : Shallow Name) : Shallow Name :=
  .list 2 (fun index => if index = 0 then left else right)

def encodeShape (item : Encode.TotalCodec Item (Shallow Name)) : Semantics.MeasuredSequence.Tree Item → Shallow Name
  | .empty => .null
  | .one value => .list 1 (fun _ => item.encode value)
  | .branch _ left right => branchShape (encodeShape item left) (encodeShape item right)

def join? (left right : Editable Item) : Option (Editable Item) :=
  let leftSize := Semantics.MeasuredSequence.size left.val
  let rightSize := Semantics.MeasuredSequence.size right.val
  if positive : 0 < leftSize ∧ 0 < rightSize then
    some ⟨.branch (leftSize + rightSize) left.val right.val,
      left.property, right.property, positive.1, positive.2, rfl⟩
  else none

/-- Null is empty, a singleton array is a leaf, and a pair is a join. An object
link can stand for a subtree already decoded by the caller; a blob link cannot.
Leaf payloads (including any links they contain) are delegated to `item`. -/
def decodeShape? (item : Encode.TotalCodec Item (Shallow Name)) (resolve : Name → Option (Editable Item)) :
    Shallow Name → Option (Editable Item)
  | .null => some ⟨.empty, trivial⟩
  | .list 1 children => (item.decode? (children 0)).map (fun value => ⟨.one value, trivial⟩)
  | .list 2 children => do
    let left ← decodeShape? item resolve (children 0)
    let right ← decodeShape? item resolve (children 1)
    join? left right
  | .ref (.obj name) => resolve name
  | _ => none

/-- The normalized shape is an ordered array, not a serialized midpoint tree.
Decoding explicitly rebuilds that tree. -/
def normalizedCodec (item : Encode.TotalCodec Item (Shallow Name)) :
    Encode.TotalCodec (Normalized Item) (Shallow Name) :=
  let normal := Semantics.MeasuredSequence.normalEquiv (Item := Item)
  let contents : Encode.TotalCodec (Normalized Item) (List Item) :=
    ⟨normal.toFun, some ∘ normal.symm.toFun, fun tree => congrArg some (normal.left_inv tree)⟩
  let payloads : Encode.TotalCodec (List Item) (List (Shallow Name)) :=
    ⟨(·.map item.encode), (·.mapM item.decode?), fun items => by
      induction items with
      | nil => rfl
      | cons head tail ih => simp [item.recovers, ih]⟩
  contents.then (payloads.then Encode.list)

def rebuild (tree : Semantics.MeasuredSequence.Tree Item) : Normalized Item :=
  ⟨Semantics.MeasuredSequence.normalize tree, Semantics.MeasuredSequence.normalize_idempotent tree⟩

def encodeNormalized (item : Encode.TotalCodec Item (Shallow Name))
    (tree : Semantics.MeasuredSequence.Tree Item) : Shallow Name :=
  (normalizedCodec item).encode (rebuild tree)

def normalizeShape? (item : Encode.TotalCodec Item (Shallow Name)) (resolve : Name → Option (Editable Item))
    (shape : Shallow Name) : Option (Shallow Name) :=
  (decodeShape? item resolve shape).map (fun tree => encodeNormalized item tree.val)

end Silmaril.Formats.Dasl.MeasuredSequence
