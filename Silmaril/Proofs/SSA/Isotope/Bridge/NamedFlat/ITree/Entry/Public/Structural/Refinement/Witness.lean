module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Witness.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Refinement.Witness

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut (observeRaw)
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open LambdaSSA (FiniteCFG)
open Silmaril.Elgot.ITree (HandledTrace Trace)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type} [DecidableEq F]
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  (left : StructuralEntry signature source exits fields inputType outputs)
  (right : StructuralEntry signature target exits fields rightType outputs)

private theorem store_sound {initial : V → Value Atom} {trace : Program.ObservationTrace signature}
    (found : left.explainRefinementFromStore? right initial = some trace) :
    HandledTrace signature.traceModel.step ()
      (observeRaw signature.primitive exits fields source initial) trace ∧
    ¬ HandledTrace signature.traceModel.step ()
      (observeRaw signature.primitive exits fields target initial) trace := by
  change ((left.seed? initial).bind fun leftPacket => (right.seed? initial).bind fun rightPacket =>
    (left.program.explainRefinementBetween? right.program 0 leftPacket 0 rightPacket).map
      (Trace.map FiniteCFG.packedTreeOutput)) = some trace at found
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at found
  obtain ⟨leftPacket, leftSeed, rightPacket, rightSeed, rawTrace, extracted, rfl⟩ := found
  have leftChecked := (decodeSeed?_eq_some_iff _ _ _).mp leftSeed
  have rightChecked := (decodeSeed?_eq_some_iff _ _ _).mp rightSeed
  have packed := left.program.explainRefinementBetween?_sound_packed extracted left.entry right.entry
    (fun _ => .unit) (fun _ => .unit) (packetRecord leftPacket) (packetRecord rightPacket)
    (recordAgrees_packetRecord left.entry left.publicCaptures leftPacket)
    (recordAgrees_packetRecord right.entry right.publicCaptures rightPacket)
  rw [left.observe_eq initial leftPacket _ leftChecked, right.observe_eq initial rightPacket _ rightChecked] at packed
  exact ⟨(signature.handledTrace_iff _ _).mpr packed.1, fun seen => packed.2 ((signature.handledTrace_iff _ _).mp seen)⟩

private theorem store_exists {initial : V → Value Atom} (failed : left.refinementFromStore? right initial = some false) :
    ∃ trace, left.explainRefinementFromStore? right initial = some trace := by
  change ((left.seed? initial).bind fun leftPacket => (right.seed? initial).bind fun rightPacket =>
    some (left.program.refinementBetween? right.program 0 leftPacket 0 rightPacket)) = some false at failed
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at failed
  obtain ⟨leftPacket, leftSeed, rightPacket, rightSeed, rejected⟩ := failed
  cases extracted : left.program.explainRefinementBetween? right.program 0 leftPacket 0 rightPacket with
  | none =>
    have passed := (left.program.explainRefinementBetween?_spec right.program 0 leftPacket 0 rightPacket).1.mp extracted
    rw [rejected] at passed
    cases passed
  | some trace =>
    refine ⟨trace.map FiniteCFG.packedTreeOutput, ?_⟩
    change ((left.seed? initial).bind fun a => (right.seed? initial).bind fun b =>
      (left.program.explainRefinementBetween? right.program 0 a 0 b).map
        (Trace.map FiniteCFG.packedTreeOutput)) = _
    simp [leftSeed, rightSeed, extracted]

theorem sound {witness : CaptureTraceWitness V signature}
    (found : left.explainRefinementOverCaptures? right = some witness) :
    witness.Refutes left right := by
  unfold StructuralEntry.explainRefinementOverCaptures? at found
  obtain ⟨initial, selected, explained⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨trace, atStore, rfl⟩ := Option.map_eq_some_iff.mp explained
  exact ⟨List.mem_of_find?_eq_some selected, store_sound left right atStore⟩

theorem has_witness :
    (left.explainRefinementOverCaptures? right).isSome = true ↔
      (left.refinementOverCaptures right).verdict = some false := by
  rw [left.refinementOverCaptures_eq_false_iff right]
  unfold StructuralEntry.explainRefinementOverCaptures?
  cases selected : (left.jointStores right).find?
      (fun initial => left.refinementFromStore? right initial == some false) with
  | none =>
    simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨initial, mem, failed⟩
    exact (List.find?_eq_none.mp selected initial mem) (beq_iff_eq.mpr failed)
  | some initial =>
    have rejects := List.find?_some
      (p := fun store => left.refinementFromStore? right store == some false) selected
    have bad : left.refinementFromStore? right initial = some false := beq_iff_eq.mp rejects
    obtain ⟨trace, found⟩ := store_exists left right bad
    have failure : ∃ s ∈ left.jointStores right, left.refinementFromStore? right s = some false :=
      ⟨initial, List.mem_of_find?_eq_some selected, bad⟩
    simp [found, failure]

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Refinement.Witness
