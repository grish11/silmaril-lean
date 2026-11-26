module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends

open CategoryTheory
open Fixture
open Loop.Institution (Equation mapGraph)
open Memory.Diamond.Institution (reduct)
open Memory.Diamond.Institution renaming Signature → EntrySignature, Model → EntryModel
open Memory.Diamond.LambdaSSA (packet)
open Memory.Diamond.MLIR.Finite (Profile)
open Memory.Diamond.MLIR.Finite renaming encodeResult → encodeCFResult

private def sig : EntrySignature := ⟨args⟩
private def model : EntryModel sig := ⟨3, input⟩
private abbrev profile : Profile := Profile.ofCells model.cells

-- Evaluate the emitted CFG with two completed backedges, then recover
-- the exact observations of the other two emitted programs.
private theorem shiftCF :
    MLIR.Institution.observe shift model (initial 1) = Part.some (.returned (encodeCFResult profile 0 atExit)) :=
  (mlir_observation_iff_run shift model (initial 1) 0 atExit).2 ⟨8, by cbv⟩

example : lambdaReturns (lowerLambda shift) model (initial 1) 0 (packet 0) atExit :=
  (lambda_observation_iff_mlir shift model (initial 1) atExit 0 (packet 0)).2 ⟨0, shiftCF, rfl, rfl⟩

example : thetaObservation shift model (initial 1) = Part.some (Memory.encodeResult 0 atExit) :=
  (theta_observation_iff_mlir shift model (initial 1) 0 atExit).2 shiftCF

private def clearTail : Graph args :=
  ⟨.load (.latest 0) headWire
    (.store (.latest 0) tailWire (.arg (.tail (.tail .head)))
      (.ret (.latest 1) (.output (0 : Fin 1) .head))),
    rfl, .tail (.tail .head)⟩

private def cycling : Heap 3 := (initial 1).write tailCell 0

private theorem fixed : clearTail.step model.input cycling = .inr cycling := by
  have same : cycling.write tailCell 0 = cycling :=
    Function.update_eq_self_iff.2 (by cbv)
  change (if (1 : Word) = 0 then Sum.inl (1, cycling.write tailCell 0)
    else Sum.inr (cycling.write tailCell 0)) = .inr cycling
  rw [ite_eq_right (by decide : (1 : Word) ≠ 0), same]

private theorem noCF : MLIR.Institution.observe clearTail model cycling = Part.none := by
  apply (mlir_no_return_iff clearTail model cycling).2
  apply Part.eq_none_iff.2
  rintro ⟨word, final⟩ observed
  obtain ⟨count, returned⟩ := (clearTail.returns_iff_mem_denote model.input cycling word final).2 observed
  have native := (clearTail.returnsAfter_iff_evalAfter model.input cycling count word final).1 returned
  have noResult (n : Nat) : clearTail.evalFrom model.input n cycling = none := by
    induction n with
    | zero => simp [Graph.evalFrom, fixed]
    | succ n ih => simpa [Graph.evalFrom, fixed] using ih
  change clearTail.evalFrom model.input count cycling = some (word, final) at native
  rw [noResult count] at native
  cases native

example : ∀ label payload final, ¬ lambdaReturns (lowerLambda clearTail) model cycling label payload final :=
  (lambda_no_return_iff_mlir clearTail model cycling).2 noCF

example : thetaObservation clearTail model cycling = Part.none :=
  (theta_no_return_iff_mlir clearTail model cycling).2 noCF

private def equation : Equation sig := ⟨shift, clearTail⟩
private def shiftHeap : Heap 3 := update (initial 0) 2
private def clearedHeap : Heap 3 := (initial 0).write tailCell 0

private theorem observeImmediate (graph : Graph args) (final : Heap 3)
    (evaluated : graph.evalAfter model.input (initial 0) 0 = some (0, final)) :
    MLIR.MemRef.CF.Institution.observe (P := sig) graph model (initial 0) = Part.some (0, final) := by
  refine (MLIR.MemRef.CF.Institution.observe_eq (P := sig) graph model (initial 0)).trans ?_
  exact Part.eq_some_iff.mpr ((graph.returns_iff_mem_denote model.input (initial 0) 0 final).mp
    ⟨0, (graph.returnsAfter_iff_evalAfter model.input (initial 0) 0 0 final).mpr evaluated⟩)

-- The emitted programs return the same word at the same initial heap.
-- The first program writes the old tail word to the head cell.
example : ¬ MLIR.MemRef.CF.Institution.Holds equation model := by
  intro holds
  have same := (observeImmediate shift shiftHeap (by cbv)).symm.trans
    ((holds (initial 0)).trans (observeImmediate clearTail clearedHeap (by cbv)))
  have cell := congrArg (fun result : Word × Heap 3 => result.2 headCell) (Part.some_inj.mp same)
  exact (by decide : shiftHeap headCell ≠ clearedHeap headCell) cell

private theorem noMemRef : MLIR.MemRef.CF.Institution.observe (P := sig) clearTail model cycling = Part.none :=
  (MLIR.MemRef.CF.Institution.observe_eq (P := sig) clearTail model cycling).trans
    ((mlir_no_return_iff clearTail model cycling).mp noCF)

example : MLIR.Institution.observe (P := sig) clearTail model cycling = Part.none :=
  (mlir_observation_eq_map_memref (P := sig) clearTail model cycling).trans (by rw [noMemRef, Part.map_none])

private def swap : sig ⟶ sig :=
  ⟨fun
    | .head => .tail .head
    | .tail .head => .head
    | .tail (.tail .head) => .tail (.tail .head)⟩

example : MLIR.MemRef.CF.Institution.observe (mapGraph swap shift) model (initial 0) =
    MLIR.MemRef.CF.Institution.observe shift (reduct swap model) (initial 0) :=
  MLIR.MemRef.CF.Institution.observe_mapGraph swap shift model (initial 0)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends
