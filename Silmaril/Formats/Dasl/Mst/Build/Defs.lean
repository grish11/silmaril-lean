module

public import Silmaril.Formats.Dasl.Mst.Route.Thms
public import Silmaril.Formats.Dasl.Mst.Atproto.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Mst

abbrev Record (Name : Type) := Key × Name

/-- A leading open gap, then each selected record with the open gap to its right. -/
structure LayerSplit (Name : Type) where
  left : List (Record Name)
  pivots : List (Record Name × List (Record Name))

variable {Name : Type}

def LayerSplit.flatten (split : LayerSplit Name) : List (Record Name) :=
  split.left ++ split.pivots.flatMap fun (pivot, gap) => pivot :: gap

def splitLayer (layerOf : Key → Nat) (layer : Nat) : List (Record Name) → LayerSplit Name
  | [] => ⟨[], []⟩
  | record :: tail =>
    let rest := splitLayer layerOf layer tail
    if layerOf record.1 = layer then ⟨[], (record, rest.left) :: rest.pivots⟩
    else {rest with left := record :: rest.left}

def maxLayer (layerOf : Key → Nat) (records : List (Record Name)) : Nat :=
  records.foldr (fun record layer => max (layerOf record.1) layer) 0

/-- The canonical layout consumes a strictly ordered map without silently sorting,
deduplicating, or accepting an empty ATProto key. -/
def OrderedRecords (records : List (Record Name)) : Prop :=
  records.Pairwise (fun left right => left.1.before right.1) ∧
  ∀ record ∈ records, record.1.isEmpty = false

instance (records : List (Record Name)) : Decidable (OrderedRecords records) := by
  unfold OrderedRecords
  infer_instance

/-- The finite observations of a bottom-up naming pass. Record payload links
are not dereferenced, and only reached nodes enter the trace. -/
structure Built (Name : Type) where
  root : Name
  blocks : List (Name × Node Name)

def Built.observed (built : Built Name) (name : Name) (node : Node Name) : Prop :=
  (name, node) ∈ built.blocks

def buildGap (descend : List (Record Name) → Option (Built Name)) :
    List (Record Name) → Option (Option Name × List (Name × Node Name))
  | [] => some (none, [])
  | head :: tail => (descend (head :: tail)).map fun child => (some child.root, child.blocks)

def assemble (descend : List (Record Name) → Option (Built Name)) (left : List (Record Name)) :
    List (Record Name × List (Record Name)) → Option (Node Name × List (Name × Node Name))
  | [] => (buildGap descend left).map fun gap => (⟨gap.1, []⟩, gap.2)
  | (pivot, right) :: rest => do
    let gap ← buildGap descend left
    let tail ← assemble descend right rest
    pure (⟨gap.1, ⟨pivot.1, pivot.2, tail.1.left⟩ :: tail.1.entries⟩, gap.2 ++ tail.2)

def buildLayer (nameNode : Node Name → Option Name) (descend : List (Record Name) → Option (Built Name))
    (split : LayerSplit Name) : Option (Built Name) := do
  let filled ← assemble descend split.left split.pivots
  let name ← nameNode filled.1
  pure ⟨name, (name, filled.1) :: filled.2⟩

/-- The decision to omit a child is based on an empty interval, not on a
failed read or failed naming operation. Nonempty gaps descend one layer even
when the next level has no pivot. -/
def buildAt (layerOf : Key → Nat) (nameNode : Node Name → Option Name) :
    Nat → List (Record Name) → Option (Built Name)
  | layer, records =>
    let descend := match layer with
      | 0 => fun _ => none
      | next + 1 => buildAt layerOf nameNode next
    buildLayer nameNode descend (splitLayer layerOf layer records)

def build (layerOf : Key → Nat) (nameNode : Node Name → Option Name) (records : List (Record Name)) :
    Option (Built Name) :=
  if OrderedRecords records then buildAt layerOf nameNode (maxLayer layerOf records) records else none

def Atproto.build (nameNode : Node Name → Option Name) (records : List (Record Name)) : Option (Built Name) :=
  Mst.build keyLayer nameNode records

end Silmaril.Formats.Dasl.Mst
