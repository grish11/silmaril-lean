module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction.Correctness
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.MemRef.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms

/-! Satisfaction transfer for the actual emitted three-loop programs. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction

open CategoryTheory
open RVSDG (Tuple)
open RVSDG.NestedTheta.Institution
open Silmaril.MLIR.MemRef (Buffer)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q : EntrySignature}

theorem Program.numbered_eq_some_iff (p : Program P) (model : EntryModel P) (initial : Heap model.cells)
    (out : Triple.Result model.cells) :
    p.numberedObserve model initial = Part.some (resultCodec model.cells out) ↔
      p.numberedReturns model initial out :=
  Proofs.numbered_eq_some_iff p model initial out

/-- Compare all three words and the full final buffer, with independent witnesses. -/
theorem Program.memref_returns_iff (p : Program P) (model : EntryModel P) (initial : Heap model.cells)
    (out : Triple.Result model.cells) : p.memrefReturns model initial out ↔ p.numberedReturns model initial out := by
  obtain ⟨firstWord, secondWord, thirdWord, final⟩ := out
  exact MemRef.returns_iff_numbered p.pair.first p.pair.second p.third p.pair.wiring p.wiring model initial final
    firstWord secondWord thirdWord

theorem Program.coloured_returns_iff (p : Program P) (model : EntryModel P) (initial : Heap model.cells)
    (out : Triple.Result model.cells) : p.colouredReturns model initial out ↔ p.numberedReturns model initial out :=
  RVSDG.NestedTheta.Petri.finishes_iff _ _ _ _

theorem Program.numbered_returns_map (h : P ⟶ Q) (p : Program P) (model : EntryModel Q)
    (initial : Heap model.cells) (out : Triple.Result model.cells) :
    (p.map h).numberedReturns model initial out ↔ p.numberedReturns (reduct h model) initial out :=
  Proofs.numbered_returns_map h p model initial out

theorem Program.numbered_observe_map (h : P ⟶ Q) (p : Program P) (model : EntryModel Q)
    (initial : Heap model.cells) :
    (p.map h).numberedObserve model initial = p.numberedObserve (reduct h model) initial :=
  Proofs.numbered_observe_map h p model initial

theorem Program.runMemRef_map (h : P ⟶ Q) (p : Program P) (model : EntryModel Q)
    (fuel : Nat) (initial : Buffer model.cells) :
    (p.map h).runMemRef model fuel initial = p.runMemRef (reduct h model) fuel initial :=
  MemRef.runFuel_map h p.pair.first p.pair.second p.third p.pair.wiring p.wiring model fuel initial

/-- At one typed valuation, both sentence forms transfer over all initialized heaps. -/
theorem Sentence.memref_satisfaction (s : Sentence P) (model : EntryModel P) :
    s.MemRefHolds model ↔ s.NumberedHolds model :=
  Proofs.holdsWith_congr s _ _ (fun p => p.memref_returns_iff model)

theorem Sentence.coloured_satisfaction (s : Sentence P) (model : EntryModel P) :
    s.ColouredHolds model ↔ s.NumberedHolds model :=
  Proofs.holdsWith_congr s _ _ (fun p => p.coloured_returns_iff model)

/-- A map from source to target ports pulls a target valuation back to the source. -/
theorem Sentence.satisfaction_map (h : P ⟶ Q) (s : Sentence P) (model : EntryModel Q) :
    (s.map h).NumberedHolds model ↔ s.NumberedHolds (reduct h model) :=
  Proofs.satisfaction_map h s model

theorem Sentence.memref_satisfaction_map (h : P ⟶ Q) (s : Sentence P) (model : EntryModel Q) :
    (s.map h).MemRefHolds model ↔ s.NumberedHolds (reduct h model) :=
  ((s.map h).memref_satisfaction model).trans (s.satisfaction_map h model)

theorem Sentence.coloured_satisfaction_map (h : P ⟶ Q) (s : Sentence P) (model : EntryModel Q) :
    (s.map h).ColouredHolds model ↔ s.NumberedHolds (reduct h model) :=
  ((s.map h).coloured_satisfaction model).trans (s.satisfaction_map h model)

/-- The existing room's truth at the canonical runtime quantifies over
every typed input at this cell count. -/
theorem Sentence.room_satisfaction (s : Sentence P) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) s.numbered ↔
      ∀ input : Tuple (Val cells) P.args, s.NumberedHolds ⟨cells, input⟩ :=
  Proofs.room_satisfaction s cells

/-- Room truth after re-emission ranges over the source valuations in the reduct image. -/
theorem Sentence.room_satisfaction_map (h : P ⟶ Q) (s : Sentence P) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) (s.map h).numbered ↔
      ∀ input : Tuple (Val cells) Q.args, s.NumberedHolds (reduct h ⟨cells, input⟩) :=
  ((s.map h).room_satisfaction cells).trans (forall_congr' fun input => s.satisfaction_map h ⟨cells, input⟩)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Triple.Satisfaction
