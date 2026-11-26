module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Institution.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Institution.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Observation

/-! Compare emitted λSSA, numbered θ, scalar CF, and MemRef CF
observations at a shared native typed valuation and initialized heap. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends

open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Memory.Diamond.LambdaSSA (Atom packet)
open Memory.Diamond.MLIR.Finite (Profile evalOp)
open Memory.Diamond.MLIR.Finite renaming encodeResult → encodeCFResult
open Silmaril.MLIR.CF.SwitchAssert (Outcome)
open Isotope (Value)

variable {P : EntrySignature}

/-- A partial CF return with the encoded word and all cells is witnessed
by a finite execution of the actual emitted CFG. -/
theorem mlir_observation_iff_run (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    MLIR.Institution.observe graph model initial =
      Part.some (.returned (encodeCFResult (Profile.ofCells model.cells) word final)) ↔
      ∃ fuel, (MLIR.lower (Profile.ofCells model.cells) graph).run evalOp fuel
        (MLIR.encodeEntry (Profile.ofCells model.cells) model.input initial) =
          some (encodeCFResult (Profile.ofCells model.cells) word final) :=
  Proofs.mlir_observation_iff_run graph model initial word final

theorem mlir_observation_iff (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    MLIR.Institution.observe graph model initial =
      Part.some (.returned (encodeCFResult (Profile.ofCells model.cells) word final)) ↔
      (word, final) ∈ graph.denote model.input initial :=
  (mlir_observation_iff_run graph model initial word final).trans
    ((MLIR.lower_returns_iff (Profile.ofCells model.cells) graph model.input initial word final).symm.trans
      (graph.returns_iff_mem_denote model.input initial word final))

/-- Every λSSA return has exit label zero and the packed word observed by
MLIR CF, with exactly the same whole final heap. -/
theorem lambda_observation_iff_mlir (graph : Graph P.args) (model : EntryModel P)
    (initial final : Heap model.cells) (label : Nat) (payload : Value (Atom model.cells)) :
    lambdaReturns (lowerLambda graph) model initial label payload final ↔
      ∃ word, MLIR.Institution.observe graph model initial =
        Part.some (.returned (encodeCFResult (Profile.ofCells model.cells) word final)) ∧
          label = 0 ∧ payload = packet word :=
  (lambda_observation_iff graph model initial final label payload).trans
    (exists_congr fun word => and_congr (mlir_observation_iff graph model initial word final).symm Iff.rfl)

/-- The two partial observations differ only in how they encode the
returned word and heap. A missing θ return maps to a missing CF return. -/
theorem mlir_observation_eq_map_theta (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    MLIR.Institution.observe graph model initial =
      (thetaObservation graph model initial).map (fun result =>
        Outcome.returned (encodeCFResult (Profile.ofCells model.cells)
          (result.get .head) (result.get (.tail .head)))) :=
  Proofs.mlir_observation_eq_map_theta graph model initial

theorem theta_observation_iff_mlir (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    thetaObservation graph model initial = Part.some (Memory.encodeResult word final) ↔
      MLIR.Institution.observe graph model initial =
        Part.some (.returned (encodeCFResult (Profile.ofCells model.cells) word final)) :=
  (theta_observation_iff graph model initial word final).trans
    (mlir_observation_iff graph model initial word final).symm

/-- Pack a MemRef CFG's returned word and all cells into the scalar CF
observation. Absence of a finite return is preserved by the same map. -/
theorem mlir_observation_eq_map_memref (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    MLIR.Institution.observe graph model initial =
      (MLIR.MemRef.CF.Institution.observe graph model initial).map (fun result =>
        Outcome.returned (encodeCFResult (Profile.ofCells model.cells) result.1 result.2)) := by
  rw [MLIR.MemRef.CF.Institution.observe_eq, MLIR.Institution.observe_eq]

theorem mlir_no_return_iff (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    MLIR.Institution.observe graph model initial = Part.none ↔ graph.denote model.input initial = Part.none :=
  Proofs.mlir_no_return_iff graph model initial

/-- No finite λSSA execution returns exactly when the CF observation is absent. -/
theorem lambda_no_return_iff_mlir (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    (∀ label payload final, ¬ lambdaReturns (lowerLambda graph) model initial label payload final) ↔
      MLIR.Institution.observe graph model initial = Part.none :=
  (lambda_no_return_iff graph model initial).trans (mlir_no_return_iff graph model initial).symm

theorem theta_no_return_iff_mlir (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    thetaObservation graph model initial = Part.none ↔ MLIR.Institution.observe graph model initial = Part.none :=
  (theta_no_return_iff graph model initial).trans (mlir_no_return_iff graph model initial).symm

theorem lambda_satisfaction_iff_mlir (e : Equation P) (model : EntryModel P) :
    lambdaHolds e model ↔ MLIR.Institution.Holds e model :=
  (lambda_satisfaction e model).trans (MLIR.Institution.satisfaction e model).symm

theorem theta_satisfaction_iff_mlir (e : Equation P) (model : EntryModel P) :
    thetaHolds e model ↔ MLIR.Institution.Holds e model :=
  (theta_satisfaction e model).trans (MLIR.Institution.satisfaction e model).symm

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends
