module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Institution.Thms
public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Theta.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Proofs

open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Memory.Diamond.MLIR.Finite (Profile evalOp)
open Memory.Diamond.MLIR.Finite renaming encodeResult → encodeCFResult
open RVSDG.NestedTheta.Petri (Finishes finishes_iff)
open RVSDG.NestedTheta.Partial (observe_ofRuntime_eq_some_iff_returns)
open Silmaril.MLIR.CF.SwitchAssert (Cfg Outcome)

variable {P : EntrySignature}

theorem mlir_observation_iff_run (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    MLIR.Institution.observe graph model initial =
      Part.some (.returned (encodeCFResult (Profile.ofCells model.cells) word final)) ↔
      ∃ fuel, (MLIR.lower (Profile.ofCells model.cells) graph).run evalOp fuel
        (MLIR.encodeEntry (Profile.ofCells model.cells) model.input initial) =
          some (encodeCFResult (Profile.ofCells model.cells) word final) := by
  unfold MLIR.Institution.observe
  dsimp only
  erw [Cfg.denotePart_eq_some_iff]
  simp only [Cfg.embed_run, Option.map_eq_some_iff, Outcome.returned.injEq]
  constructor
  · rintro ⟨fuel, output, run, rfl⟩
    exact ⟨fuel, run⟩
  · rintro ⟨fuel, run⟩
    exact ⟨fuel, _, run, rfl⟩

theorem mlir_no_return_iff (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    MLIR.Institution.observe graph model initial = Part.none ↔ graph.denote model.input initial = Part.none := by
  unfold MLIR.Institution.observe
  erw [Cfg.denotePart_eq_none_iff, Cfg.embed_diverges_iff,
    MLIR.lower_diverges_iff (Profile.ofCells model.cells) graph model.input initial]
  exact Part.eq_none_iff'.symm

theorem mlir_observation_eq_map_theta (graph : Graph P.args) (model : EntryModel P) (initial : Heap model.cells) :
    MLIR.Institution.observe graph model initial =
      (thetaObservation graph model initial).map (fun result =>
        Outcome.returned (encodeCFResult (Profile.ofCells model.cells)
          (result.get .head) (result.get (.tail .head)))) := by
  erw [MLIR.Institution.observe_eq graph model initial, theta_observation graph model initial, Part.map_map]
  rfl

theorem memref_run_iff_theta_run (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) (word : Word) (final : Heap model.cells) :
    (∃ fuel, (MLIR.MemRef.CF.lower model.cells graph).run (MLIR.MemRef.CF.evalBody model.input)
      fuel .nil ⟨initial⟩ = (some (.cons word .nil), ⟨final⟩)) ↔
    ∃ fuel, graph.lowerTheta.run (thetaRuntime model.cells) fuel (Memory.encodeInput initial model.input) =
      some (Memory.encodeResult word final) := by
  constructor
  · rintro ⟨fuel, emitted⟩
    obtain ⟨count, _, native⟩ :=
      (MLIR.MemRef.CF.cfg_run_eq_some_iff_returnsAfter graph model.input fuel initial word final).mp emitted
    exact ⟨count + 1, ((graph.lowerTheta_returnsAfter_iff model.input initial count word final).mp native).2⟩
  · intro emitted
    obtain ⟨count, native⟩ := (graph.lowerTheta_returns_iff model.input initial word final).mpr emitted
    exact ⟨count + 3, (MLIR.MemRef.CF.cfg_run_eq_some_iff_returnsAfter
      graph model.input (count + 3) initial word final).mpr ⟨count, Nat.le_refl _, native⟩⟩

theorem petri_no_completion_iff_theta (graph : Graph P.args) (model : EntryModel P)
    (initial : Heap model.cells) :
    (∀ output, ¬ Finishes (thetaRuntime model.cells) graph.lowerTheta
      (Memory.encodeInput initial model.input) output) ↔ thetaObservation graph model initial = Part.none := by
  rw [Part.eq_none_iff]
  exact forall_congr' fun output => not_congr
    ((finishes_iff _ _ _ output).trans ((observe_ofRuntime_eq_some_iff_returns _ _ _ output).symm.trans
      Part.eq_some_iff))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Proofs
