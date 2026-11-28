module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellEmbedding.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellEmbedding.Composition.Correctness

/-! Typed capture reducts and composition of framed observations across cell counts. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution

open CategoryTheory
open RVSDG (Tuple)
open Silmaril.MLIR.MemRef (Buffer)
open CellEmbedding (Embedding extend restrict SameFrame)
open Memory.Diamond.Institution (PortMap pullInput reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {small middle large : Nat} {P Q : EntrySignature}

/-- Pulling typed captures back along any port map, including address
bindings, commutes with embedding the cell values. -/
theorem pullInput_embed {args target : List ValueSort} (rename : PortMap args target)
    (e : Embedding small large) (inputs : Tuple (Val small) target) :
    pullInput rename (CellEmbedding.input e inputs) = CellEmbedding.input e (pullInput rename inputs) :=
  CellEmbeddingProofs.pullInput_embed rename e inputs

theorem reduct_embed (h : P ⟶ Q) (model : EntryModel Q) (e : Embedding model.cells large) :
    reduct h (embedModel model e) = embedModel (reduct h model) e :=
  CellEmbeddingProofs.reduct_embed h model e

theorem embedModel_trans (model : EntryModel Q) (e : Embedding model.cells middle)
    (f : Embedding middle large) :
    embedModel model (e.trans f) = embedModel (embedModel model e) f :=
  CellEmbeddingProofs.embedModel_trans model e f

/-- The two frames assemble into the frame of the composite embedding. -/
theorem embedOutput_trans (e : Embedding small middle) (f : Embedding middle large)
    (inner : Heap middle) (outer : Heap large) :
    embedOutput (e.trans f) (extend f outer inner) =
      embedOutput f outer ∘ embedOutput e inner :=
  CellEmbeddingProofs.embedOutput_trans e f inner outer

/-- Re-emit along the typed map and evaluate at the composite embedded
model, or run at the source reduct and extend the partial result twice. -/
theorem RuntimeRoom.GeneratedProgram.observe_map_embed_trans (h : P ⟶ Q)
    (p : RuntimeRoom.GeneratedProgram P.args) (model : EntryModel Q)
    (e : Embedding model.cells middle) (f : Embedding middle large) (initial : Heap large) :
    (p.map h).observe (embedModel model (e.trans f)) initial =
      (((p.observe (reduct h model) (restrict e (restrict f initial))).map
        (embedOutput e (restrict f initial))).map (embedOutput f initial)) :=
  CellEmbeddingProofs.observe_map_embed_trans h p model e f initial

theorem RuntimeRoom.GeneratedProgram.petriObserve_map_embed_trans (h : P ⟶ Q)
    (p : RuntimeRoom.GeneratedProgram P.args) (model : EntryModel Q)
    (e : Embedding model.cells middle) (f : Embedding middle large) (initial : Heap large) :
    (p.map h).petriObserve (embedModel model (e.trans f)) initial =
      (((p.petriObserve (reduct h model) (restrict e (restrict f initial))).map
        (embedOutput e (restrict f initial))).map (embedOutput f initial)) :=
  ((p.map h).petriObserve_eq_numbered (embedModel model (e.trans f)) initial).trans
    ((p.observe_map_embed_trans h model e f initial).trans
      (congrArg (fun observed => (observed.map (embedOutput e (restrict f initial))).map (embedOutput f initial))
        (p.petriObserve_eq_numbered (reduct h model) (restrict e (restrict f initial))).symm))

/-- Compare exact returns from the re-emitted CFG, retaining the two
disjoint parts of the frame at their respective interfaces. -/
theorem MemRefRoom.GeneratedProgram.returns_map_embed_trans_iff (h : P ⟶ Q)
    (p : MemRefRoom.GeneratedProgram P.args) (model : EntryModel Q)
    (e : Embedding model.cells middle) (f : Embedding middle large)
    (initial : Buffer large) (word : Word) (final : Buffer large) :
    (MemRefRoom.GeneratedProgram.lower (mapGraph h p.source)).Returns (embedModel model (e.trans f))
        initial (word, final) ↔
      p.Returns (reduct h model) ⟨restrict e (restrict f initial.cell)⟩ (word, ⟨restrict e (restrict f final.cell)⟩) ∧
        SameFrame f initial.cell final.cell ∧ SameFrame e (restrict f initial.cell) (restrict f final.cell) :=
  CellEmbeddingProofs.memRef_returns_map_embed_trans_iff h p model e f initial word final

/-- Quantify over all heaps at the embedded target valuation and at the
source reduct, for either equations or universal finite termination. -/
theorem Sentence.holds_map_embed (h : P ⟶ Q) (s : Sentence P) (model : EntryModel Q)
    (e : Embedding model.cells large) : (s.map h).Holds (embedModel model e) ↔ s.Holds (reduct h model) := by
  rw [s.satisfaction_map, reduct_embed]
  exact s.holds_embed (reduct h model) e

theorem RuntimeRoom.Sentence.holds_map_embed (h : P ⟶ Q) (s : RuntimeRoom.Sentence P) (model : EntryModel Q)
    (e : Embedding model.cells large) : (s.map h).Holds (embedModel model e) ↔ s.Holds (reduct h model) := by
  rw [s.satisfaction_map, reduct_embed]
  exact s.holds_embed (reduct h model) e

theorem MemRefRoom.Sentence.holds_map_embed (h : P ⟶ Q) (s : MemRefRoom.Sentence P) (model : EntryModel Q)
    (e : Embedding model.cells large) : (s.map h).Holds (embedModel model e) ↔ s.Holds (reduct h model) := by
  rw [s.satisfaction_map, reduct_embed]
  exact s.holds_embed (reduct h model) e

theorem PetriRoom.holds_map_embed (h : P ⟶ Q) (s : RuntimeRoom.Sentence P) (model : EntryModel Q)
    (e : Embedding model.cells large) : PetriRoom.Holds (s.map h) (embedModel model e) ↔ PetriRoom.Holds s (reduct h model) := by
  rw [holds_map, reduct_embed]
  exact holds_embed s (reduct h model) e

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution
