module

public import Silmaril.Formats.Dasl.Mst.Thms

@[expose] public section

namespace Silmaril.Formats.Dasl.Mst

open Silmaril.Semantics.Naming (Relation)

variable {Name : Type}

def Context.Contains (ctx : Context) (key : Key) : Prop :=
  (∀ lower ∈ ctx.lower, lower.before key) ∧ (∀ upper ∈ ctx.upper, key.before upper)

instance (ctx : Context) (key : Key) : Decidable (ctx.Contains key) := by
  unfold Context.Contains
  cases ctx.lower <;> cases ctx.upper <;> simp <;> infer_instance

inductive Slot (Name : Type) where
  | gap (ctx : Context) (child : Option Name)
  | record (key : Key) (name : Name)

def Slot.Covers (slot : Slot Name) (key : Key) : Prop :=
  match slot with
  | .gap ctx _ => ctx.Contains key
  | .record entry _ => key = entry

instance (slot : Slot Name) (key : Key) : Decidable (slot.Covers key) := by
  cases slot <;> unfold Slot.Covers <;> infer_instance

/-- In-order alternating open gaps and singleton records. Every named gap is
at exactly the preceding layer and preserves the parent bounds not cut by a key. -/
def slotsFrom (ctx : Context) (child : Option Name) : List (Entry Name) → List (Slot Name)
  | [] => [.gap ctx child]
  | entry :: tail =>
    .gap {ctx with upper := some entry.key} child :: .record entry.key entry.record ::
      slotsFrom {ctx with lower := some entry.key} entry.right tail

def Node.slots (node : Node Name) (ctx : Context) : List (Slot Name) :=
  slotsFrom {ctx with layer := ctx.layer - 1, root := false} node.left node.entries

def matchingSlot (node : Node Name) (ctx : Context) (key : Key) : Option (Slot Name) :=
  (node.slots ctx).find? fun slot => decide (slot.Covers key)

abbrev SlotEntries (Name : Type) := Slot Name × List (Key × Name)

/-- A finite rooted representation in a reference node relation. Each slot
contributes only entries in its interval; null gaps contribute none. Child
contexts, including their levels, are fixed by the parent, not by the reader. -/
inductive Realizes (layerOf : Key → Nat) (reference : Relation Name (Node Name)) :
    Option Context → Name → List (Key × Name) → Prop where
  | step {expected : Option Context} {name : Name} {node : Node Name} {groups : List (SlotEntries Name)}
      (present : reference name node)
      (valid : (expected.getD (node.rootContext layerOf)).Valid layerOf node)
      (slots : groups.map Prod.fst = node.slots (expected.getD (node.rootContext layerOf)))
      (bounded : ∀ group ∈ groups, ∀ entry ∈ group.2, group.1.Covers entry.1)
      (records : ∀ group ∈ groups, ∀ key record, group.1 = .record key record → group.2 = [(key, record)])
      (pruned : ∀ group ∈ groups, ∀ ctx, group.1 = .gap ctx none → group.2 = [])
      (child : ∀ group ∈ groups, ∀ ctx child, group.1 = .gap ctx (some child) →
        Realizes layerOf reference (some ctx) child group.2) :
      Realizes layerOf reference expected name (groups.flatMap Prod.snd)

inductive RouteError (Name : Type) where
  | fuel (name : Name)
  | missing (name : Name)
  | invalidWire (name : Name)
  | invalidNode (name : Name)
  deriving DecidableEq, Repr

def ReadSound (read : Name → Wire.ReadResult (Shallow Name)) (reference : Relation Name (Node Name)) : Prop :=
  ∀ ⦃name value node⦄, read name = .found value → decodeNode? value = some node → reference name node

/-- Read only the selected branch. Record links are returned, not dereferenced. -/
def route (layerOf : Key → Nat) (read : Name → Wire.ReadResult (Shallow Name)) (key : Key) :
    (fuel : Nat) → Option Context → Name → Except (RouteError Name) (Option Name)
  | 0, _, name => .error (.fuel name)
  | fuel + 1, expected, name =>
    let valid := fun node : Node Name => (expected.getD (node.rootContext layerOf)).Valid layerOf node
    match readChecked (valid := valid) (read name) with
    | .missing => .error (.missing name)
    | .invalidWire => .error (.invalidWire name)
    | .invalidNode => .error (.invalidNode name)
    | .found node _ =>
      match matchingSlot node (expected.getD (node.rootContext layerOf)) key with
      | none => .error (.invalidNode name)
      | some (.record _ record) => .ok (some record)
      | some (.gap _ none) => .ok none
      | some (.gap ctx (some child)) => route layerOf read key fuel (some ctx) child

end Silmaril.Formats.Dasl.Mst
