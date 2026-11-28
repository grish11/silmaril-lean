module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Activation.Defs
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Institution.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Activation.Reindex

/-! Compose typed operand wiring with emitted Petri and MemRef activations. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Activation

open CategoryTheory
open RVSDG (Port)
open RVSDG.NestedTheta.Petri (Finishes)
open MLIR.MemRef.CF (Label)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P Q R : EntrySignature}

theorem bindAddress_comp (address : Port Q.args .address) (wiring : P ⟶ Q) (h : Q ⟶ R) :
    bindAddress address wiring ≫ h = bindAddress (EntrySignature.Hom.port h address) (wiring ≫ h) := by
  apply congrArg EntrySignature.Hom.mk
  funext sort port
  cases port <;> rfl

/-- The emitted terminator and buffer implement one native activation. -/
theorem memrefHeader_step (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    memrefHeader graph model initial = match graph.step model.input initial with
    | .inl (word, final) => (.inl ⟨Label.exit, .cons word .nil⟩, ⟨final⟩)
    | .inr next => (.inl ⟨Label.header, .nil⟩, ⟨next⟩) :=
  Proofs.memrefHeader_step graph model initial

/-- Typed re-emission and evaluation at the reduct choose the same ordered
successor, result operands and post-store buffer. -/
theorem memrefHeader_map (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (initial : Heap model.cells) :
    memrefHeader (mapGraph h graph) model initial = memrefHeader graph (reduct h model) initial :=
  Proofs.memrefHeader_map h graph model initial

/-- The Petri arm with rewired operands and the MemRef header with
pulled-back operands agree at the full word/heap boundary. -/
theorem petri_map_iff_memref_header (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (initial next : Heap model.cells) (restart : Bool) :
    petriActivation (mapGraph h graph) model initial next restart ↔
      memrefHeader graph (reduct h model) initial = successor graph (reduct h model) next restart :=
  Proofs.petri_map_iff_memref_header h graph model initial next restart

/-- Selecting several activation operands and then reindexing the
captured inputs composes by typed port substitution. -/
theorem petri_comp_iff_memref_header (wiring : P ⟶ Q) (h : Q ⟶ R) (graph : Graph P.args)
    (model : EntryModel R) (initial next : Heap model.cells) (restart : Bool) :
    petriActivation (mapGraph (wiring ≫ h) graph) model initial next restart ↔
      memrefHeader graph (reduct wiring (reduct h model)) initial =
        successor graph (reduct wiring (reduct h model)) next restart :=
  Proofs.petri_comp_iff_memref_header wiring h graph model initial next restart

/-- With one fixed wiring for the whole loop, compare finite Petri
completion to the actual partial MemRef observation at the reduct. -/
theorem petri_completion_map_iff_memref (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    Finishes (thetaRuntime model.cells) (mapGraph h graph).lowerTheta (encodeInput initial model.input)
      (encodeResult word final) ↔
      MLIR.MemRef.CF.Institution.observe graph (reduct h model) initial = Part.some (word, final) := by
  rw [← MLIR.MemRef.CF.Institution.observe_mapGraph h graph model initial]
  exact petri_completion_iff_memref (mapGraph h graph) model initial word final

theorem petri_no_completion_map_iff_memref (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (initial : Heap model.cells) :
    (∀ output, ¬ Finishes (thetaRuntime model.cells) (mapGraph h graph).lowerTheta
      (encodeInput initial model.input) output) ↔
      MLIR.MemRef.CF.Institution.observe graph (reduct h model) initial = Part.none := by
  rw [← MLIR.MemRef.CF.Institution.observe_mapGraph h graph model initial]
  exact petri_no_completion_iff_memref (mapGraph h graph) model initial

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Activation
