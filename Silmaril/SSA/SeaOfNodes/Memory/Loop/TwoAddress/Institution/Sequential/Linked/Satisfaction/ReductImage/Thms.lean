module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction.ReductImage.Correctness

/-! Composition and truth reflection for the existing linked runtime sentences. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction

open CategoryTheory
open RVSDG (Tuple)
open RVSDG.NestedTheta.Institution
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q R : EntrySignature} {cells : Nat}

theorem forall_reduct_image (h : P ⟶ Q) (holds : EntryModel P → Prop) :
    (∀ input : Tuple (Val cells) Q.args, holds (reduct h ⟨cells, input⟩)) ↔
      ∀ input : Tuple (Val cells) P.args, InReductImage h input → holds ⟨cells, input⟩ :=
  ReductImageProofs.forall_reduct_image h holds

theorem in_image_comp (h : P ⟶ Q) (k : Q ⟶ R) (input : Tuple (Val cells) P.args) :
    InReductImage (h ≫ k) input ↔
      ∃ between : Tuple (Val cells) Q.args, InReductImage k between ∧ reduct h ⟨cells, between⟩ = ⟨cells, input⟩ :=
  ReductImageProofs.in_image_comp h k input

/-- A typed port map with a retraction covers every source input at every cell count. -/
theorem in_image_of_retraction (h : P ⟶ Q) (back : Q ⟶ P) (split : h ≫ back = 𝟙 P)
    (input : Tuple (Val cells) P.args) : InReductImage h input :=
  ReductImageProofs.in_image_of_retraction h back split input

/-- A surjective second reduct leaves the first reduct's image unchanged. -/
theorem in_image_comp_iff_of_surjective (h : P ⟶ Q) (k : Q ⟶ R)
    (covers : ∀ between : Tuple (Val cells) Q.args, InReductImage k between)
    (input : Tuple (Val cells) P.args) : InReductImage (h ≫ k) input ↔ InReductImage h input :=
  (in_image_comp h k input).trans
    ⟨fun ⟨between, _, equal⟩ => ⟨between, equal⟩, fun ⟨between, equal⟩ => ⟨between, covers between, equal⟩⟩

theorem Program.numbered_observe_comp (h : P ⟶ Q) (k : Q ⟶ R) (p : Program P)
    (model : EntryModel R) (initial : Heap model.cells) :
    ((p.map h).map k).numberedObserve model initial = p.numberedObserve (reduct h (reduct k model)) initial :=
  ((p.map h).numbered_observe_map k model initial).trans (p.numbered_observe_map h (reduct k model) initial)

theorem Program.memref_returns_comp (h : P ⟶ Q) (k : Q ⟶ R) (p : Program P)
    (model : EntryModel R) (initial : Heap model.cells) (out : Result model.cells) :
    ((p.map h).map k).memrefReturns model initial out ↔ p.memrefReturns (reduct h (reduct k model)) initial out :=
  ((p.map h).memref_returns_map k model initial out).trans (p.memref_returns_map h (reduct k model) initial out)

theorem Program.coloured_returns_comp (h : P ⟶ Q) (k : Q ⟶ R) (p : Program P)
    (model : EntryModel R) (initial : Heap model.cells) (out : Result model.cells) :
    ((p.map h).map k).colouredReturns model initial out ↔ p.colouredReturns (reduct h (reduct k model)) initial out :=
  ((p.map h).coloured_returns_map k model initial out).trans (p.coloured_returns_map h (reduct k model) initial out)

/-- All-target truth is source truth restricted to the typed reduct image. -/
theorem equation_satisfaction_image (h : P ⟶ Q) (p q : Program P) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) ((p.map h).equation (q.map h)) ↔
      ∀ input : Tuple (Val cells) P.args, InReductImage h input →
        Agrees (p.nativeReturns ⟨cells, input⟩) (q.nativeReturns ⟨cells, input⟩) :=
  (equation_satisfaction_map h p q cells).trans
    (forall_reduct_image h fun model => Agrees (p.nativeReturns model) (q.nativeReturns model))

theorem termination_satisfaction_image (h : P ⟶ Q) (p : Program P) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) (p.map h).terminates ↔
      ∀ input : Tuple (Val cells) P.args, InReductImage h input → Terminates (p.nativeReturns ⟨cells, input⟩) :=
  (termination_satisfaction_map h p cells).trans (forall_reduct_image h fun model => Terminates (p.nativeReturns model))

theorem equation_satisfaction_comp (h : P ⟶ Q) (k : Q ⟶ R) (p q : Program P) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells))
        (((p.map h).map k).equation ((q.map h).map k)) ↔
      ∀ input : Tuple (Val cells) P.args, InReductImage (h ≫ k) input →
        Agrees (p.nativeReturns ⟨cells, input⟩) (q.nativeReturns ⟨cells, input⟩) := by
  rw [← p.map_comp h k, ← q.map_comp h k]
  exact equation_satisfaction_image (h ≫ k) p q cells

theorem termination_satisfaction_comp (h : P ⟶ Q) (k : Q ⟶ R) (p : Program P) (cells : Nat) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells))
        ((p.map h).map k).terminates ↔
      ∀ input : Tuple (Val cells) P.args, InReductImage (h ≫ k) input → Terminates (p.nativeReturns ⟨cells, input⟩) := by
  rw [← p.map_comp h k]
  exact termination_satisfaction_image (h ≫ k) p cells

theorem equation_satisfaction_iff_of_surjective (h : P ⟶ Q) (p q : Program P) (cells : Nat)
    (covers : ∀ input : Tuple (Val cells) P.args, InReductImage h input) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) ((p.map h).equation (q.map h)) ↔
      (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) (p.equation q) := by
  rw [equation_satisfaction_image, equation_satisfaction]
  exact ⟨fun satisfy input => satisfy input (covers input), fun satisfy input _ => satisfy input⟩

theorem termination_satisfaction_iff_of_surjective (h : P ⟶ Q) (p : Program P) (cells : Nat)
    (covers : ∀ input : Tuple (Val cells) P.args, InReductImage h input) :
    (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) (p.map h).terminates ↔
      (RuntimeObservation.room.{0, 0, 0} target).Sat (Discrete.mk (thetaRuntime cells)) p.terminates := by
  rw [termination_satisfaction_image, termination_satisfaction]
  exact ⟨fun satisfy input => satisfy input (covers input), fun satisfy input _ => satisfy input⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.Sequential.Linked.Satisfaction
