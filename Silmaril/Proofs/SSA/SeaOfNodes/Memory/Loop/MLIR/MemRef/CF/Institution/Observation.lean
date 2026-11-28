module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Institution.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Institution.Proofs

open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel

variable {P : EntrySignature}

theorem observe_eq (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    observe graph model initial = graph.denote model.input initial := by
  let adequacy (result : Word × Heap model.cells) :=
    exists_run_eq_some_iff_mem_denote graph model.input initial result.1 result.2
  refine Part.ext' ?_ ?_
  · rw [Part.dom_iff_mem (o := graph.denote model.input initial)]
    exact exists_congr adequacy
  · intro observed defined
    let result := Classical.choose observed
    have member := (adequacy result).mp (Classical.choose_spec observed)
    exact Part.mem_unique member ⟨defined, rfl⟩

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Institution.Proofs
