module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellEmbedding.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.CellEmbedding.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.PetriRoom.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellEmbedding.Observation

/-! Framed observations in the three generated backends. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution

open CellEmbedding (Embedding extend restrict SameFrame)
open Silmaril.MLIR.MemRef (Buffer)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P : EntrySignature} {large : Nat}

theorem embedOutput_encode {small : Nat} (e : Embedding small large) (frame : Heap large)
    (word : Word) (final : Heap small) :
    embedOutput e frame (encodeResult word final) = encodeResult word (extend e frame final) :=
  CellEmbeddingProofs.embedOutput_encode e frame word final

theorem nativeReturns_embed_iff (graph : Graph P.args) (model : EntryModel P)
    (e : Embedding model.cells large) (initial : Heap large) (word : Word) (final : Heap large) :
    nativeReturns graph (embedModel model e) initial word final ↔
      nativeReturns graph model (restrict e initial) word (restrict e final) ∧ SameFrame e initial final :=
  CellEmbeddingProofs.nativeReturns_embed_iff graph model e initial word final

/-- The valuation is fixed before embedding. Each side quantifies over all initial heaps at its own count. -/
theorem Sentence.holds_embed (s : Sentence P) (model : EntryModel P) (e : Embedding model.cells large) :
    s.Holds (embedModel model e) ↔ s.Holds model :=
  CellEmbeddingProofs.holds_embed s model e

/-- The numbered observer returns the embedded full result or has no finite observation. -/
theorem RuntimeRoom.GeneratedProgram.observe_embed (p : RuntimeRoom.GeneratedProgram P.args)
    (model : EntryModel P) (e : Embedding model.cells large) (initial : Heap large) :
    p.observe (embedModel model e) initial =
      (p.observe model (restrict e initial)).map (embedOutput e initial) :=
  CellEmbeddingProofs.observe_embed p model e initial

theorem RuntimeRoom.GeneratedProgram.petriObserve_embed (p : RuntimeRoom.GeneratedProgram P.args)
    (model : EntryModel P) (e : Embedding model.cells large) (initial : Heap large) :
    p.petriObserve (embedModel model e) initial =
      (p.petriObserve model (restrict e initial)).map (embedOutput e initial) :=
  (p.petriObserve_eq_numbered (embedModel model e) initial).trans
    ((p.observe_embed model e initial).trans
      (congrArg (Part.map (embedOutput e initial)) (p.petriObserve_eq_numbered model (restrict e initial)).symm))

theorem MemRefRoom.GeneratedProgram.returns_embed_iff (p : MemRefRoom.GeneratedProgram P.args)
    (model : EntryModel P) (e : Embedding model.cells large) (initial : Buffer large)
    (word : Word) (final : Buffer large) :
    p.Returns (embedModel model e) initial (word, final) ↔
      p.Returns model ⟨restrict e initial.cell⟩ (word, ⟨restrict e final.cell⟩) ∧
        SameFrame e initial.cell final.cell :=
  (p.returns_iff_native (embedModel model e) initial word final).trans
    ((nativeReturns_embed_iff p.source model e initial.cell word final.cell).trans
      (and_congr (p.returns_iff_native model ⟨restrict e initial.cell⟩ word ⟨restrict e final.cell⟩).symm Iff.rfl))

theorem MemRefRoom.GeneratedProgram.no_return_embed (p : MemRefRoom.GeneratedProgram P.args)
    (model : EntryModel P) (e : Embedding model.cells large) (initial : Buffer large) :
    (∀ word final, ¬ p.Returns (embedModel model e) initial (word, final)) ↔
      ∀ word final, ¬ p.Returns model ⟨restrict e initial.cell⟩ (word, final) :=
  CellEmbeddingProofs.memRef_no_return_embed p model e initial

theorem RuntimeRoom.Sentence.holds_embed (s : RuntimeRoom.Sentence P) (model : EntryModel P)
    (e : Embedding model.cells large) : s.Holds (embedModel model e) ↔ s.Holds model :=
  (s.satisfaction (embedModel model e)).trans ((s.source.holds_embed model e).trans (s.satisfaction model).symm)

theorem MemRefRoom.Sentence.holds_embed (s : MemRefRoom.Sentence P) (model : EntryModel P)
    (e : Embedding model.cells large) : s.Holds (embedModel model e) ↔ s.Holds model :=
  (s.satisfaction (embedModel model e)).trans ((s.source.holds_embed model e).trans (s.satisfaction model).symm)

theorem PetriRoom.holds_embed (s : RuntimeRoom.Sentence P) (model : EntryModel P)
    (e : Embedding model.cells large) : PetriRoom.Holds s (embedModel model e) ↔ PetriRoom.Holds s model :=
  (holds_iff_numbered s (embedModel model e)).trans
    ((s.holds_embed model e).trans (holds_iff_numbered s model).symm)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution
