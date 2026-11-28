module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Boundary.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.MemRef.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.Observation
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.Sentences
import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Reindex.Thms

/-! Exact whole-result observation and satisfaction in the existing runtime room. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction

open CategoryTheory
open RVSDG (Tuple)
open RVSDG.NestedTheta.Institution
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q R : EntrySignature}

/-- The linked numbered observation is exactly the encoded sequential result. -/
theorem Program.numbered_observe (p : Program P) (model : EntryModel P) (initial : Heap model.cells) :
    p.numberedObserve model initial = (p.sequentialObserve model initial).map (resultCodec model.cells) :=
  Linked.observe_eq_numbered p.first p.second p.wiring model initial

theorem Program.sequential_eq_some_iff (p : Program P) (model : EntryModel P) (initial : Heap model.cells)
    (out : Result model.cells) :
    p.sequentialObserve model initial = Part.some out ↔ p.nativeReturns model initial out :=
  Proofs.sequential_eq_some_iff p model initial out

theorem Program.numbered_eq_some_iff (p : Program P) (model : EntryModel P) (initial : Heap model.cells)
    (out : Result model.cells) :
    p.numberedObserve model initial = Part.some (resultCodec model.cells out) ↔ p.nativeReturns model initial out :=
  Proofs.numbered_eq_some_iff p model initial out

theorem Program.memref_returns_iff (p : Program P) (model : EntryModel P) (initial : Heap model.cells)
    (out : Result model.cells) : p.memrefReturns model initial out ↔ p.nativeReturns model initial out :=
  Proofs.memref_returns_iff p model initial out

theorem Program.coloured_returns_iff (p : Program P) (model : EntryModel P) (initial : Heap model.cells)
    (out : Result model.cells) : p.colouredReturns model initial out ↔ p.nativeReturns model initial out :=
  Proofs.coloured_returns_iff p model initial out

theorem Program.native_returns_map (h : P ⟶ Q) (p : Program P) (model : EntryModel Q)
    (initial : Heap model.cells) (out : Result model.cells) :
    (p.map h).nativeReturns model initial out ↔ p.nativeReturns (reduct h model) initial out :=
  Proofs.native_returns_map h p model initial out

theorem Program.numbered_observe_map (h : P ⟶ Q) (p : Program P) (model : EntryModel Q) (initial : Heap model.cells) :
    (p.map h).numberedObserve model initial = p.numberedObserve (reduct h model) initial :=
  Proofs.numbered_observe_map h p model initial

theorem numbered_agrees (p q : Program P) (model : EntryModel P) :
    (∀ initial, p.numberedObserve model initial = q.numberedObserve model initial) ↔
      Agrees (p.nativeReturns model) (q.nativeReturns model) :=
  Proofs.numbered_agrees p q model

theorem Program.numbered_dom (p : Program P) (model : EntryModel P) (initial : Heap model.cells) :
    (p.numberedObserve model initial).Dom ↔ ∃ out, p.nativeReturns model initial out :=
  Proofs.numbered_dom p model initial

theorem equation_satisfaction (p q : Program P) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) (p.equation q) ↔
      ∀ input : Tuple (Val cells) P.args, Agrees (p.nativeReturns ⟨cells, input⟩) (q.nativeReturns ⟨cells, input⟩) :=
  Proofs.equation_satisfaction p q cells

theorem termination_satisfaction (p : Program P) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) p.terminates ↔
      ∀ input : Tuple (Val cells) P.args, Terminates (p.nativeReturns ⟨cells, input⟩) :=
  Proofs.termination_satisfaction p cells

theorem Program.memref_absent (p : Program P) (model : EntryModel P) (initial : Heap model.cells) :
    (∀ fuel, p.runMemRef model fuel ⟨initial⟩ = none) ↔ ¬ ∃ out, p.nativeReturns model initial out :=
  Proofs.memref_absent p model initial

theorem Program.map_id (p : Program P) : p.map (𝟙 P) = p := by
  cases p with
  | mk next first second wiring =>
    simp only [Program.map, mapGraph_id]
    exact congrArg (Program.mk next first second) wiring.map_id

theorem Program.map_comp (h : P ⟶ Q) (k : Q ⟶ R) (p : Program P) :
    p.map (h ≫ k) = (p.map h).map k := by
  cases p with
  | mk next first second wiring =>
    simp only [Program.map, mapGraph_comp]
    exact congrArg (Program.mk next (mapGraph k (mapGraph h first)) second)
      (wiring.map_comp (EntrySignature.Hom.port h) (EntrySignature.Hom.port k))

theorem Program.memref_returns_map (h : P ⟶ Q) (p : Program P) (model : EntryModel Q)
    (initial : Heap model.cells) (out : Result model.cells) :
    (p.map h).memrefReturns model initial out ↔ p.memrefReturns (reduct h model) initial out :=
  ((p.map h).memref_returns_iff model initial out).trans
    ((p.native_returns_map h model initial out).trans (p.memref_returns_iff (reduct h model) initial out).symm)

theorem Program.coloured_returns_map (h : P ⟶ Q) (p : Program P) (model : EntryModel Q)
    (initial : Heap model.cells) (out : Result model.cells) :
    (p.map h).colouredReturns model initial out ↔ p.colouredReturns (reduct h model) initial out :=
  ((p.map h).coloured_returns_iff model initial out).trans
    ((p.native_returns_map h model initial out).trans (p.coloured_returns_iff (reduct h model) initial out).symm)

theorem Program.numbered_absent (p : Program P) (model : EntryModel P) (initial : Heap model.cells) :
    p.numberedObserve model initial = Part.none ↔ ¬ ∃ out, p.nativeReturns model initial out :=
  Part.eq_none_iff'.trans (not_congr (p.numbered_dom model initial))

theorem Program.coloured_absent (p : Program P) (model : EntryModel P) (initial : Heap model.cells) :
    (∀ out, ¬ p.colouredReturns model initial out) ↔ ¬ ∃ out, p.nativeReturns model initial out := by
  simp only [p.coloured_returns_iff, not_exists]

theorem memref_agrees (p q : Program P) (model : EntryModel P) :
    Agrees (p.memrefReturns model) (q.memrefReturns model) ↔
      Agrees (p.nativeReturns model) (q.nativeReturns model) := by
  simp only [Agrees, p.memref_returns_iff, q.memref_returns_iff]

theorem coloured_agrees (p q : Program P) (model : EntryModel P) :
    Agrees (p.colouredReturns model) (q.colouredReturns model) ↔
      Agrees (p.nativeReturns model) (q.nativeReturns model) := by
  simp only [Agrees, p.coloured_returns_iff, q.coloured_returns_iff]

theorem memref_terminates (p : Program P) (model : EntryModel P) :
    Terminates (p.memrefReturns model) ↔ Terminates (p.nativeReturns model) := by
  simp only [Terminates, p.memref_returns_iff]

theorem coloured_terminates (p : Program P) (model : EntryModel P) :
    Terminates (p.colouredReturns model) ↔ Terminates (p.nativeReturns model) := by
  simp only [Terminates, p.coloured_returns_iff]

/-- Re-emitted global truth ranges over target valuations and therefore
only over their reduct image on the source side. -/
theorem equation_satisfaction_map (h : P ⟶ Q) (p q : Program P) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) ((p.map h).equation (q.map h)) ↔
      ∀ input : Tuple (Val cells) Q.args, Agrees (p.nativeReturns (reduct h ⟨cells, input⟩))
        (q.nativeReturns (reduct h ⟨cells, input⟩)) := by
  rw [equation_satisfaction]
  exact forall_congr' fun input => forall_congr' fun initial => forall_congr' fun out =>
    iff_congr (p.native_returns_map h ⟨cells, input⟩ initial out) (q.native_returns_map h ⟨cells, input⟩ initial out)

theorem termination_satisfaction_map (h : P ⟶ Q) (p : Program P) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) (p.map h).terminates ↔
      ∀ input : Tuple (Val cells) Q.args, Terminates (p.nativeReturns (reduct h ⟨cells, input⟩)) := by
  rw [termination_satisfaction]
  exact forall_congr' fun input => forall_congr' fun initial => exists_congr fun out =>
    p.native_returns_map h ⟨cells, input⟩ initial out

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction
