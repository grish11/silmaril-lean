module

import Silmaril.Formats.Dasl.Mst.Route.Thms
meta import Silmaril.Formats.Dasl.Mst.Route.Thms

open Silmaril Silmaril.Formats.Dasl

private def layerOf (key : Mst.Key) : Nat := if key = [10] then 1 else 0

private def emit (node : Mst.Node Nat) : Wire.ReadResult (Shallow Nat) :=
  match Mst.encodeNode? node with | some value => .found value | none => .invalidWire

private def rootNode : Mst.Node Nat := ⟨some 1, [⟨[10], 20, none⟩]⟩
private def leafNode : Mst.Node Nat := ⟨none, [⟨[6], 21, none⟩]⟩

private def readRoot (childRead : Wire.ReadResult (Shallow Nat)) : Nat → Wire.ReadResult (Shallow Nat)
  | 0 => emit rootNode
  | 1 => childRead
  | _ => .missing

private def reference (name : Nat) (node : Mst.Node Nat) : Prop :=
  (name = 0 ∧ node = rootNode) ∨ (name = 1 ∧ node = leafNode)

private theorem onlyRoot {expected : Option Mst.Context} {name : Nat}
    (request : Mst.Reaches layerOf (readRoot .missing) [10] 0 expected name) : expected = none ∧ name = 0 := by
  induction request with
  | start => exact ⟨rfl, rfl⟩
  | @step _ _ _ _ node value _ found decoded _ selected ih =>
    obtain ⟨rfl, rfl⟩ := ih
    change emit rootNode = .found value at found
    have rootDecoded : Mst.decodeNode? value = some rootNode := by
      unfold emit at found
      split at found
      · rename_i encoded
        cases found
        exact Mst.node_roundtrip encoded
      · contradiction
    have same := Option.some.inj (decoded.symm.trans rootDecoded)
    subst node
    have inline : Mst.matchingSlot rootNode (rootNode.rootContext layerOf) [10] = some (.record [10] 20) := by
      simp [Mst.matchingSlot, Mst.Node.slots, Mst.Node.rootContext, rootNode, Mst.slotsFrom, Mst.Slot.Covers,
        Mst.Context.Contains, Mst.Key.before]
    rw [show (none : Option Mst.Context).getD (rootNode.rootContext layerOf) = rootNode.rootContext layerOf from rfl,
      inline] at selected
    cases selected

example : Mst.PathCovers layerOf (readRoot .missing) [10] 0 reference := by
  intro _ _ node request known
  obtain ⟨rfl, rfl⟩ := onlyRoot request
  rcases known with ⟨_, rfl⟩ | ⟨impossible, _⟩
  · have encoded : (Mst.encodeNode? rootNode).isSome = true := by decide
    obtain ⟨value, rendered⟩ := Option.isSome_iff_exists.mp encoded
    exact ⟨value, by simp [readRoot, emit, rendered], Mst.node_roundtrip rendered⟩
  · contradiction

private def emptyNode : Mst.Node Nat := ⟨none, []⟩

private theorem emptyRoot : Mst.Realizes layerOf (fun name node => name = 0 ∧ node = emptyNode) none 0 [] := by
  let next : Mst.Context := ⟨0, none, none, false⟩
  let part : Mst.SlotEntries Nat := (.gap next none, [])
  change Mst.Realizes layerOf _ none 0 ([part].flatMap Prod.snd)
  apply Mst.Realizes.step (node := emptyNode) (groups := [part]) ⟨rfl, rfl⟩
  · decide
  · rfl
  · intro group hit
    obtain rfl := List.mem_singleton.mp hit
    simp [part]
  · intro group hit key record slot
    obtain rfl := List.mem_singleton.mp hit
    cases slot
  · intro group hit ctx slot
    obtain rfl := List.mem_singleton.mp hit
    rfl
  · intro group hit ctx child slot
    obtain rfl := List.mem_singleton.mp hit
    cases slot

example : (emptyNode.rootContext layerOf).layer = 0 := by
  have maximum := emptyRoot.rootLayer_spec (fun {_ _ _} left right => left.2.trans right.2.symm) ⟨rfl, rfl⟩
  simpa using maximum.2

example {ctx : Mst.Context} (notRoot : ctx.root = false)
    (invalid : Mst.Realizes layerOf reference (some ctx) 1 []) : False := invalid.nonroot_nonempty notRoot rfl

public def main : IO Unit := do
  let leaf := emit leafNode
  let lookup := fun child key fuel => Mst.route layerOf (readRoot child) key fuel none 0
  match lookup .missing [10] 1, lookup .missing [14] 1, lookup .missing [6] 2,
      lookup leaf [6] 2, lookup leaf [7] 2, lookup leaf [6] 1 with
  | .ok (some 20), .ok none, .error (.missing 1), .ok (some 21), .ok none, .error (.fuel 1) => pure ()
  | _, _, _, _, _, _ => throw (IO.userError "MST must distinguish inline hits, null gaps and unread children")
  let outside := emit ⟨none, [⟨[12], 21, none⟩]⟩
  match lookup .invalidWire [6] 2, lookup (.found .null) [6] 2, lookup outside [6] 2 with
  | .error (.invalidWire 1), .error (.invalidNode 1), .error (.invalidNode 1) => pure ()
  | _, _, _ => throw (IO.userError "MST must reject invalid encoding or a child outside its inherited gap")
