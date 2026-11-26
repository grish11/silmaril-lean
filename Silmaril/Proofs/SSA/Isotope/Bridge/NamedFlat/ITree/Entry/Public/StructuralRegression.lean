module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Witness.Thms
meta import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Witness.Thms
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.SSA.LambdaRTL (CFG upd)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

private abbrev Name := ULift.{1} Nat
private abbrev bit : PacketType := .coprod .unit .unit
private def signature : PrimitiveSignature Unit := ⟨fun _ => bit, fun _ => bit⟩
private def shared : Name := ⟨4⟩
private def leftRead : Name := ⟨5⟩
private def rightRead : Name := ⟨6⟩
private def liveOut : Name := ⟨9⟩
private def exits : List Name := [⟨22⟩, ⟨11⟩]
private def fields (_ : Name) : List Name := [liveOut]
private def outputs (_ : Fin exits.length) : PacketType := .product .unit (.product bit .unit)

private def graph (first second : Name) : CFG Name Name Unit :=
  ⟨.term (.br ⟨12⟩ (.pair (.var first) (.var second))),
    [(⟨12⟩, ⟨⟨7⟩, .let2 ⟨8⟩ liveOut (.val (.var ⟨7⟩)) (.term (.br ⟨11⟩ .unit))⟩)]⟩

private def build (first second : Name) (firstType : PacketType) :
    Option (StructuralEntry signature (graph first second) exits fields (.product firstType bit) outputs) :=
  constructStructural signature (graph first second) exits fields (.product firstType bit)
    (fun _ => .product firstType bit) outputs

private def left := (build shared leftRead bit).get (by decide)
private def right := (build shared rightRead bit).get (by decide)

private theorem leftFootprint : left.footprint = [(shared, bit), (leftRead, bit)] := by decide
example : right.footprint = [(shared, bit), (rightRead, bit)] := by decide

-- Three independently chosen bits, with one shared register written only
-- when its two occurrences demand the same value.
example : (left.jointStores right).length = 8 := by decide

private def original : Name → Value Atom :=
  upd (upd (upd (fun _ => .unit) shared (.inl .unit)) leftRead (.inr .unit)) rightRead (.inl .unit)

private def leftPacket : Denote (.product bit bit) := (.inl ⟨⟩, .inr ⟨⟩)
private def rightPacket : Denote (.product bit bit) := (.inl ⟨⟩, .inl ⟨⟩)

example : left.entry.observe (fun _ => .unit) (packetRecord (inputType := .product bit bit) leftPacket) =
    LiveOut.observeRaw signature.primitive exits fields (graph shared leftRead) original :=
  left.observe_eq original leftPacket (fun _ => .unit) (by decide)

example : ∃ initial ∈ left.jointStores right,
    ∀ field ∈ left.footprint ++ right.footprint, initial field.1 = original field.1 :=
  left.jointStores_cover right original ⟨leftPacket, by decide⟩ ⟨rightPacket, by decide⟩

private def changedLiveOut : Name → Value Atom := upd original liveOut (.pair .unit .unit)

example : LiveOut.observeRaw signature.primitive exits fields (graph shared leftRead) original =
    LiveOut.observeRaw signature.primitive exits fields (graph shared leftRead) changedLiveOut := by
  apply left.observe_eq_of_capture_agree _ ⟨leftPacket, by decide⟩
  intro field mem
  simp only [leftFootprint, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl <;> decide

-- Repeating a name with disjoint raw encodings empties the domain.
private def conflicting := (build shared shared .unit).get (by decide)
example : (conflicting.jointAssignments right).isEmpty = true := by decide

example : (conflicting.refinementOverCaptures right).emptyDomain = true := by decide
example : (conflicting.refinementOverCaptures right).verdict = some true :=
  conflicting.refinementOverCaptures_vacuous right (by decide)

-- Unequal types with a common encoding still admit exactly the compatible stores.
private def overlapping := (build shared shared (.coprod .unit .empty)).get (by decide)
example : (overlapping.jointStores right).length = 2 := by decide

example : (overlapping.refinementOverCaptures right).emptyDomain = false := by decide
example : overlapping.refinementFromStore? right (fun _ => .unit) = none := by decide

-- Both rows take the same ordered exit. The common value of the repeated
-- capture is the left live-out, while the right live-out uses the other bit.
private def mismatchingStore : Name → Value Atom := upd original rightRead (.inr .unit)
private def overlapPacket : Denote (.product (.coprod .unit .empty) bit) := (.inl ⟨⟩, .inl ⟨⟩)
private def mismatchingPacket : Denote (.product bit bit) := (.inl ⟨⟩, .inr ⟨⟩)

set_option maxHeartbeats 1000000 in
private theorem actualMismatch :
    overlapping.program.refinementBetween? right.program 0 overlapPacket 0 mismatchingPacket = false := by cbv

private theorem storeMismatch :
    overlapping.refinementFromStore? right mismatchingStore = some false := by
  have leftSeed : overlapping.seed? mismatchingStore = some overlapPacket := by decide
  have rightSeed : right.seed? mismatchingStore = some mismatchingPacket := by decide
  change ((overlapping.seed? mismatchingStore).bind fun a => (right.seed? mismatchingStore).bind fun b =>
    some (overlapping.program.refinementBetween? right.program 0 a 0 b)) = some false
  rw [leftSeed, rightSeed]
  exact congrArg some actualMismatch

private theorem overlapFails : (overlapping.refinementOverCaptures right).verdict = some false := by
  have spec := (overlapping.refinementFromStore?_eq_some_iff right mismatchingStore false).mp storeMismatch
  apply (overlapping.refinementOverCaptures_eq_some_iff right false).mpr
  exact ⟨fun impossible => Bool.noConfusion impossible, fun all => spec.2.2.mpr (all mismatchingStore spec.1 spec.2.1)⟩

example : (overlapping.refinementCounterexample? right).isSome = true :=
  (overlapping.refinementCounterexample?_isSome_iff right).mpr overlapFails

private def expectedOverlapWitness : Bool :=
  match overlapping.refinementCounterexample? right with
  | none => false
  | some checked =>
    match checked.val.trace with
    | .result packet =>
      decide (checked.val.initial shared = Value.inl .unit ∧ checked.val.initial rightRead = Value.inr .unit ∧
        packet = (0, Value.inr (.inl (.pair .unit (.pair (.inl .unit) .unit)))))
    | _ => false

#guard expectedOverlapWitness

example : (conflicting.refinementCounterexample? right).isSome = false :=
  Bool.eq_false_iff.mpr fun found => by
    have rejected := (conflicting.refinementCounterexample?_isSome_iff right).mp found
    rw [conflicting.refinementOverCaptures_vacuous right (by decide)] at rejected
    cases rejected

-- This target selects the first unpacked field. The two fields coincide
-- on the one jointly typed capture assignment.
private def matchingGraph : CFG Name Name Unit :=
  {graph shared shared with
    blocks := [(⟨12⟩, ⟨⟨7⟩, .let2 liveOut ⟨8⟩ (.val (.var ⟨7⟩)) (.term (.br ⟨11⟩ .unit))⟩)]}

private def matching : StructuralEntry signature matchingGraph exits fields (.product bit bit) outputs :=
  (constructStructural signature matchingGraph exits fields (.product bit bit) (fun _ => .product bit bit)
    outputs).get (by decide)

private def matchingAssignment : List (Name × Value Atom) := List.replicate 4 (shared, .inl .unit)
private def matchingStore := StructuralSeed.assignmentStore matchingAssignment
private theorem matchingAssignments : overlapping.jointAssignments matching = [matchingAssignment] := by decide

set_option maxHeartbeats 1000000 in
private theorem actualSuccess :
    overlapping.program.refinementBetween? matching.program 0 overlapPacket 0 rightPacket = true := by cbv

private theorem matchingStorePasses : overlapping.refinementFromStore? matching matchingStore = some true := by
  have leftSeed : overlapping.seed? matchingStore = some overlapPacket := by decide
  have rightSeed : matching.seed? matchingStore = some rightPacket := by decide
  change ((overlapping.seed? matchingStore).bind fun a => (matching.seed? matchingStore).bind fun b =>
    some (overlapping.program.refinementBetween? matching.program 0 a 0 b)) = some true
  rw [leftSeed, rightSeed]
  exact congrArg some actualSuccess

private theorem matchingVerdict : (overlapping.refinementOverCaptures matching).verdict = some true := by
  change combineStoreVerdicts ((overlapping.jointStores matching).map
    (overlapping.refinementFromStore? matching)) = some true
  simp only [StructuralEntry.jointStores, matchingAssignments, List.map_cons, List.map_nil]
  change combineStoreVerdicts [overlapping.refinementFromStore? matching matchingStore] = some true
  simp [matchingStorePasses, combineStoreVerdicts]

example : (overlapping.refinementOverCaptures matching).emptyDomain = false := by decide
example : (overlapping.refinementCounterexample? matching).isSome = false :=
  Bool.eq_false_iff.mpr fun found => by
    have rejected := (overlapping.refinementCounterexample?_isSome_iff matching).mp found
    rw [matchingVerdict] at rejected
    cases rejected

#guard !(overlapping.refinementCounterexample? matching).isSome

-- Existing named elaboration can express an injection as an instruction,
-- but the structural public readback takes the operand of a direct jump.
example :
    (constructStructural signature
      {graph shared leftRead with
        entry := .let1 ⟨8⟩ (.inl .unit) (.term (.br ⟨12⟩ (.pair (.var ⟨8⟩) (.var leftRead))))}
      exits fields (.product bit bit) (fun _ => .product bit bit) outputs).isNone = true := by decide

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
