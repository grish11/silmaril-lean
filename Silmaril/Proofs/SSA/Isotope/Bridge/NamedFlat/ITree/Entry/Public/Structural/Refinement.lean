module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Refinement.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Structural.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Stores.Thms
import Silmaril.Semantics.ITree.Reindex.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Refinement

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut (observeRaw)
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
open Silmaril.Elgot.ITree (HandledTrace Tree)
open Silmaril.Elgot.ITree.Finite (Event)

variable {V K : Type 1} [DecidableEq V] [DecidableEq K] {F : Type} [DecidableEq F]
  {signature : PrimitiveSignature F} {source target : CFG V K F} {exits : List K} {fields : K → List V}
  {inputType rightType : PacketType} {outputs : Fin exits.length → PacketType}
  (left : StructuralEntry signature source exits fields inputType outputs)
  (right : StructuralEntry signature target exits fields rightType outputs)

private abbrev handledLE (signature : PrimitiveSignature F)
    (source target : Tree (Event signature.Request signature.Reply) (Nat × Value Atom)) : Prop :=
  ∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
    ∀ x, policy.initial x → ∀ trace,
      HandledTrace policy.step x source trace → HandledTrace policy.step x target trace

private theorem compare_at (initial : V → Value Atom) (leftPacket : Denote inputType) (rightPacket : Denote rightType)
    (leftChecked : left.evalSeed initial = PacketType.encode inputType leftPacket)
    (rightChecked : right.evalSeed initial = PacketType.encode rightType rightPacket) :
    left.program.refinementBetween? right.program 0 leftPacket 0 rightPacket = true ↔
      handledLE signature (observeRaw signature.primitive exits fields source initial)
        (observeRaw signature.primitive exits fields target initial) := by
  rw [left.program.refinementBetween?_iff_packed right.program leftPacket rightPacket left.entry right.entry
    (fun _ => .unit) (fun _ => .unit) (packetRecord leftPacket) (packetRecord rightPacket)
    (recordAgrees_packetRecord left.entry left.publicCaptures leftPacket)
    (recordAgrees_packetRecord right.entry right.publicCaptures rightPacket),
    left.observe_eq initial leftPacket _ leftChecked, right.observe_eq initial rightPacket _ rightChecked]
  refine ⟨fun included _ _ _ _ seen => included.handledTrace seen, fun valid trace seen => ?_⟩
  exact (signature.handledTrace_iff _ trace).mp <|
    valid signature.traceModel () trivial trace ((signature.handledTrace_iff _ trace).mpr seen)

theorem store_eq_some (initial : V → Value Atom) (verdict : Bool) :
    left.refinementFromStore? right initial = some verdict ↔
      (∃ a, left.evalSeed initial = PacketType.encode inputType a) ∧
      (∃ b, right.evalSeed initial = PacketType.encode rightType b) ∧
      (verdict = true ↔
        ∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
          ∀ x, policy.initial x → ∀ trace,
            HandledTrace policy.step x (observeRaw signature.primitive exits fields source initial) trace →
            HandledTrace policy.step x (observeRaw signature.primitive exits fields target initial) trace) := by
  change ((left.seed? initial).bind fun leftPacket => (right.seed? initial).bind fun rightPacket =>
    some (left.program.refinementBetween? right.program 0 leftPacket 0 rightPacket)) = some verdict ↔ _
  simp only [Option.bind_eq_some_iff, Option.some.injEq, StructuralEntry.seed?, decodeSeed?_eq_some_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, compare_at left right initial a b ha hb⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, valid⟩
    exact ⟨a, ha, b, hb, Bool.eq_iff_iff.mpr ((compare_at left right initial a b ha hb).trans valid.symm)⟩

private theorem listed_verdict_typed (initial : V → Value Atom) (mem : initial ∈ left.jointStores right) :
    (left.refinementFromStore? right initial).isSome = true := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := left.jointStores_typed right mem
  change ((left.seed? initial).bind fun leftPacket => (right.seed? initial).bind fun rightPacket =>
    some (left.program.refinementBetween? right.program 0 leftPacket 0 rightPacket)).isSome = true
  have leftSeed : left.seed? initial = some a := (decodeSeed?_eq_some_iff _ _ _).mpr ha
  have rightSeed : right.seed? initial = some b := (decodeSeed?_eq_some_iff _ _ _).mpr hb
  rw [leftSeed, rightSeed]
  rfl

theorem domain_has_verdict : (left.refinementOverCaptures right).verdict.isSome = true := by
  let verdicts := (left.jointStores right).map (left.refinementFromStore? right)
  have typed : verdicts.all Option.isSome = true := by
    rw [List.all_eq_true, List.forall_mem_map]
    exact listed_verdict_typed left right
  change (combineStoreVerdicts verdicts).isSome = true
  simp [combineStoreVerdicts, typed]

theorem domain_eq_false :
    (left.refinementOverCaptures right).verdict = some false ↔
      ∃ initial ∈ left.jointStores right, left.refinementFromStore? right initial = some false := by
  classical
  change combineStoreVerdicts ((left.jointStores right).map (left.refinementFromStore? right)) = some false ↔ _
  simp only [combineStoreVerdicts_eq_some_iff, List.forall_mem_map]
  constructor
  · rintro ⟨typed, failure⟩
    by_contra noFailure
    apply Bool.noConfusion (failure.mpr ?_)
    intro initial mem
    obtain ⟨verdict, checked⟩ := Option.isSome_iff_exists.mp (typed initial mem)
    cases verdict
    · exact (noFailure ⟨initial, mem, checked⟩).elim
    · exact checked
  · rintro ⟨initial, mem, failed⟩
    refine ⟨listed_verdict_typed left right, ⟨fun impossible => Bool.noConfusion impossible, fun passes => ?_⟩⟩
    have passed := passes initial mem
    rw [failed] at passed
    cases passed

theorem domain_eq_some (verdict : Bool) :
    (left.refinementOverCaptures right).verdict = some verdict ↔
      (verdict = true ↔
        ∀ initial, (∃ a, left.evalSeed initial = PacketType.encode inputType a) →
          (∃ b, right.evalSeed initial = PacketType.encode rightType b) →
          ∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
            ∀ x, policy.initial x → ∀ trace,
              HandledTrace policy.step x (observeRaw signature.primitive exits fields source initial) trace →
              HandledTrace policy.step x (observeRaw signature.primitive exits fields target initial) trace) := by
  change combineStoreVerdicts ((left.jointStores right).map (left.refinementFromStore? right)) = some verdict ↔ _
  simp only [combineStoreVerdicts_eq_some_iff, List.forall_mem_map]
  have checked :
      (∀ initial ∈ left.jointStores right, left.refinementFromStore? right initial = some true) ↔
      (∀ initial ∈ left.jointStores right,
        handledLE signature (observeRaw signature.primitive exits fields source initial)
          (observeRaw signature.primitive exits fields target initial)) := by
    refine forall_congr' fun initial => forall_congr' fun mem => ?_
    have typed := left.jointStores_typed right mem
    exact ⟨fun h => ((store_eq_some left right initial true).mp h).2.2.mp rfl,
      fun h => (store_eq_some left right initial true).mpr ⟨typed.1, typed.2, ⟨fun _ => h, fun _ => rfl⟩⟩⟩
  rw [checked, left.jointStores_forall_observe_iff right (handledLE signature)]
  exact ⟨And.right, fun h => ⟨listed_verdict_typed left right, h⟩⟩

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.Public.Structural.Refinement
