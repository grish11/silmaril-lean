module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Activation.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Activation.Proofs

open CategoryTheory
open Silmaril.MLIR.MemRef (Buffer)
open MLIR.MemRef.CF (Label)
open Memory.Diamond.Institution (reduct pullInput_get)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

set_option backward.isDefEq.respectTransparency false

variable {P Q R : EntrySignature}

theorem memrefHeader_step (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) :
    memrefHeader graph model initial = match graph.step model.input initial with
    | .inl (word, final) => (.inl ⟨Label.exit, .cons word .nil⟩, ⟨final⟩)
    | .inr next => (.inl ⟨Label.header, .nil⟩, ⟨next⟩) := by
  rw [memrefHeader, MLIR.MemRef.CF.header_transition, MLIR.MemRef.observeActivation_eq_step]
  rcases graph.step model.input initial with ⟨word, final⟩ | next <;> rfl

theorem memrefHeader_map (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (initial : Heap model.cells) :
    memrefHeader (mapGraph h graph) model initial = memrefHeader graph (reduct h model) initial := by
  rw [memrefHeader_step, memrefHeader_step, step_mapGraph]
  rcases graph.step (reduct h model).input initial with ⟨word, final⟩ | next <;> rfl

private theorem successor_map (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (next : Heap model.cells) (restart : Bool) :
    successor (mapGraph h graph) model next restart = successor graph (reduct h model) next restart := by
  have word : (mapGraph h graph).stopWord model.input = graph.stopWord (reduct h model).input :=
    (pullInput_get (EntrySignature.Hom.port h) model.input graph.stop).symm
  cases restart with
  | true => rfl
  | false =>
    unfold successor
    rw [word]

theorem petri_map_iff_memref_header (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q)
    (initial next : Heap model.cells) (restart : Bool) :
    petriActivation (mapGraph h graph) model initial next restart ↔
      memrefHeader graph (reduct h model) initial = successor graph (reduct h model) next restart := by
  have observed := petri_activation_iff_memref_header (mapGraph h graph) model.input initial next restart
  change petriActivation (mapGraph h graph) model initial next restart ↔
    memrefHeader (mapGraph h graph) model initial = successor (mapGraph h graph) model next restart at observed
  rw [memrefHeader_map, successor_map] at observed
  exact observed

theorem petri_comp_iff_memref_header (wiring : P ⟶ Q) (h : Q ⟶ R) (graph : Graph P.args)
    (model : EntryModel R) (initial next : Heap model.cells) (restart : Bool) :
    petriActivation (mapGraph (wiring ≫ h) graph) model initial next restart ↔
      memrefHeader graph (reduct wiring (reduct h model)) initial =
        successor graph (reduct wiring (reduct h model)) next restart := by
  have observed := petri_map_iff_memref_header h (mapGraph wiring graph) model initial next restart
  rw [← mapGraph_comp wiring h graph, memrefHeader_map wiring, successor_map wiring] at observed
  exact observed

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Activation.Proofs
