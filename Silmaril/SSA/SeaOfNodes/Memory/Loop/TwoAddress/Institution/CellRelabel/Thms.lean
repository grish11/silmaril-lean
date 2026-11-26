module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellRelabel.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.CellRelabel.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.MemRefRoom.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.PetriRoom.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution.CellRelabel.Observation

/-! Complete result and satisfaction transport in the three generated observers. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution

open CellRelabel (Permutation heap)
open Silmaril.MLIR.MemRef (Buffer)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P : EntrySignature}

theorem relabelOutput_encode {cells : Nat} (σ : Permutation cells) (word : Word) (final : Heap cells) :
    relabelOutput σ (encodeResult word final) = encodeResult word (heap σ final) :=
  rfl

theorem nativeReturns_relabel (graph : Graph P.args) (model : EntryModel P) (σ : Permutation model.cells)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    nativeReturns graph (relabelModel model σ) (heap σ initial) word (heap σ final) ↔
      nativeReturns graph model initial word final :=
  CellRelabelProofs.nativeReturns_relabel graph model σ initial word final

/-- A model relabeling preserves equations and universal finite
termination over all initialized heaps. -/
theorem Sentence.holds_relabel (s : Sentence P) (model : EntryModel P) (σ : Permutation model.cells) :
    s.Holds (relabelModel model σ) ↔ s.Holds model :=
  CellRelabelProofs.holds_relabel s model σ

/-- The actual numbered observer transports both full results and absence. -/
theorem RuntimeRoom.GeneratedProgram.observe_relabel (p : RuntimeRoom.GeneratedProgram P.args)
    (model : EntryModel P) (σ : Permutation model.cells) (initial : Heap model.cells) :
    p.observe (relabelModel model σ) (heap σ initial) =
      (p.observe model initial).map (relabelOutput σ) :=
  CellRelabelProofs.observe_relabel p model σ initial

theorem RuntimeRoom.GeneratedProgram.petriObserve_relabel (p : RuntimeRoom.GeneratedProgram P.args)
    (model : EntryModel P) (σ : Permutation model.cells) (initial : Heap model.cells) :
    p.petriObserve (relabelModel model σ) (heap σ initial) =
      (p.petriObserve model initial).map (relabelOutput σ) :=
  (p.petriObserve_eq_numbered (relabelModel model σ) (heap σ initial)).trans
    ((p.observe_relabel model σ initial).trans
      (congrArg (Part.map (relabelOutput σ)) (p.petriObserve_eq_numbered model initial).symm))

theorem MemRefRoom.GeneratedProgram.returns_relabel (p : MemRefRoom.GeneratedProgram P.args)
    (model : EntryModel P) (σ : Permutation model.cells) (initial : Buffer model.cells)
    (word : Word) (final : Buffer model.cells) :
    p.Returns (relabelModel model σ) ⟨heap σ initial.cell⟩ (word, ⟨heap σ final.cell⟩) ↔
      p.Returns model initial (word, final) :=
  CellRelabelProofs.memRef_returns_relabel p model σ initial word final

/-- Relabeling preserves the absence of a finite return from the generated CFG. -/
theorem MemRefRoom.GeneratedProgram.no_return_relabel (p : MemRefRoom.GeneratedProgram P.args)
    (model : EntryModel P) (σ : Permutation model.cells) (initial : Buffer model.cells) :
    (∀ word final, ¬ p.Returns (relabelModel model σ) ⟨heap σ initial.cell⟩ (word, final)) ↔
      ∀ word final, ¬ p.Returns model initial (word, final) :=
  CellRelabelProofs.memRef_no_return_relabel p model σ initial

theorem RuntimeRoom.Sentence.holds_relabel (s : RuntimeRoom.Sentence P) (model : EntryModel P)
    (σ : Permutation model.cells) : s.Holds (relabelModel model σ) ↔ s.Holds model :=
  (s.satisfaction (relabelModel model σ)).trans ((s.source.holds_relabel model σ).trans (s.satisfaction model).symm)

theorem MemRefRoom.Sentence.holds_relabel (s : MemRefRoom.Sentence P) (model : EntryModel P)
    (σ : Permutation model.cells) : s.Holds (relabelModel model σ) ↔ s.Holds model :=
  (s.satisfaction (relabelModel model σ)).trans ((s.source.holds_relabel model σ).trans (s.satisfaction model).symm)

theorem PetriRoom.holds_relabel (s : RuntimeRoom.Sentence P) (model : EntryModel P) (σ : Permutation model.cells) :
    PetriRoom.Holds s (relabelModel model σ) ↔ PetriRoom.Holds s model :=
  (holds_iff_numbered s (relabelModel model σ)).trans
    ((s.holds_relabel model σ).trans (holds_iff_numbered s model).symm)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Institution
