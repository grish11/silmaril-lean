module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Institution.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Institution.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Theta.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Observation

/-! Compare emitted λSSA, numbered θ, coloured Petri completion,
scalar CF, and MemRef CF at a shared typed valuation and initialized heap. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends

open CategoryTheory
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Memory.Diamond.LambdaSSA (Atom packet)
open Memory.Diamond.MLIR.Finite (Profile evalOp)
open Memory.Diamond.MLIR.Finite renaming encodeResult → encodeCFResult
open RVSDG.NestedTheta.Petri (Finishes finishes_iff)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)
open Isotope (Value)

variable {P Q : EntrySignature}

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

/-- Decode the emitted θ tuple's word and whole heap wire into the
MemRef CFG's partial observation. -/
theorem memref_observation_eq_map_theta (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) :
    MLIR.MemRef.CF.Institution.observe graph model initial =
      (thetaObservation graph model initial).map (fun result => (result.get .head, result.get (.tail .head))) := by
  erw [MLIR.MemRef.CF.Institution.observe_eq, theta_observation, Part.map_map]
  exact (Part.map_id' (fun _ => rfl) _).symm

/-- A complete MemRef observation is equivalent to a finite execution
of the numbered program with the same word and final heap wire. -/
theorem memref_observation_iff_theta_returns (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    MLIR.MemRef.CF.Institution.observe graph model initial = Part.some (word, final) ↔
      graph.lowerTheta.Returns (thetaRuntime model.cells) (Memory.encodeInput initial model.input)
        (Memory.encodeResult word final) := by
  rw [MLIR.MemRef.CF.Institution.observe_eq, Part.eq_some_iff, ← graph.returns_iff_mem_denote]
  exact graph.lowerTheta_returns_iff model.input initial word final

/-- A successful run determines a matching finite witness for the other
backend. A native return after `k` backedges supplies `k + 3` CF blocks
or `k + 1` θ activations. -/
theorem memref_run_iff_theta_run (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    (∃ fuel, (MLIR.MemRef.CF.lower model.cells graph).run (MLIR.MemRef.CF.evalBody model.input)
      fuel .nil ⟨initial⟩ = (some (.cons word .nil), ⟨final⟩)) ↔
    ∃ fuel, graph.lowerTheta.run (thetaRuntime model.cells) fuel (Memory.encodeInput initial model.input) =
      some (Memory.encodeResult word final) :=
  Proofs.memref_run_iff_theta_run graph model initial word final

/-- A finite coloured completion observes exactly the same word and
whole final heap as the emitted MemRef CFG. -/
theorem petri_completion_iff_memref (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    Finishes (thetaRuntime model.cells) graph.lowerTheta (Memory.encodeInput initial model.input)
        (Memory.encodeResult word final) ↔
      MLIR.MemRef.CF.Institution.observe graph model initial = Part.some (word, final) :=
  (finishes_iff _ _ _ _).trans (memref_observation_iff_theta_returns graph model initial word final).symm

/-- A completed firing trace and a successful run of the emitted CFG
witness the same complete return. -/
theorem petri_completion_iff_memref_run (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    Finishes (thetaRuntime model.cells) graph.lowerTheta (Memory.encodeInput initial model.input)
        (Memory.encodeResult word final) ↔
      ∃ fuel, (MLIR.MemRef.CF.lower model.cells graph).run (MLIR.MemRef.CF.evalBody model.input)
        fuel .nil ⟨initial⟩ = (some (.cons word .nil), ⟨final⟩) :=
  (finishes_iff _ _ _ _).trans (memref_run_iff_theta_run graph model initial word final).symm

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

theorem theta_no_return_iff_memref (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    thetaObservation graph model initial = Part.none ↔ MLIR.MemRef.CF.Institution.observe graph model initial = Part.none := by
  rw [MLIR.MemRef.CF.Institution.observe_eq]
  exact theta_no_return_iff graph model initial

/-- The absence of a finite coloured completion at any output tuple
agrees with absence of a finite MemRef CFG return. -/
theorem petri_no_completion_iff_memref (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    (∀ output, ¬ Finishes (thetaRuntime model.cells) graph.lowerTheta
      (Memory.encodeInput initial model.input) output) ↔
      MLIR.MemRef.CF.Institution.observe graph model initial = Part.none :=
  (Proofs.petri_no_completion_iff_theta graph model initial).trans (theta_no_return_iff_memref graph model initial)

/-- Equality of complete finite coloured results agrees with equality of
partial MemRef observations on every initial heap at the typed model. -/
theorem petri_satisfaction_iff_memref (e : Equation P) (model : EntryModel P) :
    petriHolds e model ↔ MLIR.MemRef.CF.Institution.Holds e model := by
  simp only [petriHolds, petri_completion_iff_memref, Part.eq_some_iff, MLIR.MemRef.CF.Institution.Holds]
  exact forall_congr' fun _ => ⟨fun agrees => Part.ext fun (word, final) => agrees word final,
    fun same word final => by rw [same]⟩

theorem petri_satisfaction (e : Equation P) (model : EntryModel P) : petriHolds e model ↔ e.Holds model :=
  (petri_satisfaction_iff_memref e model).trans (MLIR.MemRef.CF.Institution.satisfaction e model)

theorem petri_satisfaction_reindex (h : P ⟶ Q) (e : Equation P) (model : EntryModel Q) :
    petriHolds (e.map h) model ↔ petriHolds e (reduct h model) :=
  (petri_satisfaction (e.map h) model).trans
    ((e.satisfaction h model).trans (petri_satisfaction e (reduct h model)).symm)

theorem theta_satisfaction_iff_memref (e : Equation P) (model : EntryModel P) :
    thetaHolds e model ↔ MLIR.MemRef.CF.Institution.Holds e model :=
  (theta_satisfaction e model).trans (MLIR.MemRef.CF.Institution.satisfaction e model).symm

theorem lambda_satisfaction_iff_mlir (e : Equation P) (model : EntryModel P) :
    lambdaHolds e model ↔ MLIR.Institution.Holds e model :=
  (lambda_satisfaction e model).trans (MLIR.Institution.satisfaction e model).symm

theorem theta_satisfaction_iff_mlir (e : Equation P) (model : EntryModel P) :
    thetaHolds e model ↔ MLIR.Institution.Holds e model :=
  (theta_satisfaction e model).trans (MLIR.Institution.satisfaction e model).symm

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends
