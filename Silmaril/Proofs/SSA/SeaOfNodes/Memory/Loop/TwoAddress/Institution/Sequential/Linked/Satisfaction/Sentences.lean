module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.Observation
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Institution.RuntimeEntry.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.Proofs

open CategoryTheory
open RVSDG (Tuple)
open RVSDG.NestedTheta.Institution
open CarriedAddress.Institution.RuntimeEntry (decodePayload encode_decodePayload)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P : EntrySignature} {cells : Nat}

set_option backward.isDefEq.respectTransparency false

private theorem forall_entry (holds : Tuple (WireVal cells) (carrier P.args) → Prop) :
    (∀ raw, holds raw) ↔ ∀ (input : Tuple (Val cells) P.args) (heap : Heap cells), holds (encodeInput heap input) := by
  constructor
  · intro all input heap
    exact all (encodeInput heap input)
  · intro all raw
    let entry := decodePayload raw
    exact (encode_decodePayload raw) ▸ all entry.input entry.heap

theorem equation_satisfaction (p q : Program P) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) (p.equation q) ↔
      ∀ input : Tuple (Val cells) P.args, Agrees (p.nativeReturns ⟨cells, input⟩) (q.nativeReturns ⟨cells, input⟩) := by
  change (∀ raw, RuntimeObservation.observe (thetaRuntime cells) p.emitNumbered.graph raw =
    RuntimeObservation.observe (thetaRuntime cells) q.emitNumbered.graph raw) ↔ _
  exact (forall_entry (P := P) (fun raw => RuntimeObservation.observe (thetaRuntime cells) p.emitNumbered.graph raw =
    RuntimeObservation.observe (thetaRuntime cells) q.emitNumbered.graph raw)).trans
    (forall_congr' fun input => numbered_agrees p q ⟨cells, input⟩)

theorem termination_satisfaction (p : Program P) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) p.terminates ↔
      ∀ input : Tuple (Val cells) P.args, Terminates (p.nativeReturns ⟨cells, input⟩) := by
  change (∀ raw, (RuntimeObservation.observe (thetaRuntime cells) p.emitNumbered.graph raw).Dom) ↔ _
  exact (forall_entry (P := P) (fun raw => (RuntimeObservation.observe (thetaRuntime cells) p.emitNumbered.graph raw).Dom)).trans
    (forall_congr' fun input => forall_congr' fun initial => numbered_dom p ⟨cells, input⟩ initial)

theorem memref_absent (p : Program P) (model : EntryModel P) (initial : Heap model.cells) :
    (∀ fuel, p.runMemRef model fuel ⟨initial⟩ = none) ↔ ¬ ∃ out, p.nativeReturns model initial out := by
  constructor
  · rintro absent ⟨⟨word, nextWord, final⟩, returned⟩
    obtain ⟨fuel, observed⟩ := (memref_returns_iff p model initial (word, nextWord, final)).mpr returned
    change p.runMemRef model fuel ⟨initial⟩ = some (word, nextWord, ⟨final⟩) at observed
    rw [absent fuel] at observed
    cases observed
  · intro absent fuel
    cases observed : p.runMemRef model fuel ⟨initial⟩ with
    | none => rfl
    | some out =>
      obtain ⟨word, nextWord, ⟨final⟩⟩ := out
      exact False.elim (absent ⟨(word, nextWord, final), (memref_returns_iff p model initial _).mp ⟨fuel, observed⟩⟩)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.Proofs
