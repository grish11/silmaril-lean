module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Institution.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Institution.Observation

/-! Full partial observations and equations of the emitted MemRef CFGs. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Institution

open CategoryTheory
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Loop.Institution (Equation mapGraph denote_mapGraph)

variable {P Q : EntrySignature}

/-- The emitted CFG observes the native word and every final cell, or
has no finite return exactly when the native partial value is absent. -/
theorem observe_eq (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    observe graph model initial = graph.denote model.input initial :=
  Proofs.observe_eq graph model initial

/-- Re-emission at renamed typed ports agrees with the native model reduct. -/
theorem observe_mapGraph (h : P ⟶ Q) (graph : Graph P.args) (model : EntryModel Q) (initial : Heap model.cells) :
    observe (mapGraph h graph) model initial = observe graph (reduct h model) initial :=
  (observe_eq _ _ _).trans ((denote_mapGraph h graph model initial).trans (observe_eq _ _ _).symm)

/-- Equality of observations over all heaps preserves and reflects
native satisfaction at the model's cell count and typed valuation. -/
theorem satisfaction (e : Equation P) (model : EntryModel P) : Holds e model ↔ e.Holds model := by
  simp only [Holds, Equation.Holds, observe_eq]

theorem satisfaction_reindex (h : P ⟶ Q) (e : Equation P) (model : EntryModel Q) :
    Holds (e.map h) model ↔ Holds e (reduct h model) :=
  (satisfaction _ _).trans ((e.satisfaction h model).trans (satisfaction _ _).symm)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Institution
