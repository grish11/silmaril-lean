module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.Portable.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.Theta.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression
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
open RVSDG.NestedTheta.Petri (Finishes)
open Silmaril.MLIR.MemRef (Buffer)

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

private def summarize (word : Word) (heap : Heap 3) : Word × Word × Word × Word :=
  (word, heap 0, heap 1, heap 2)

private def memrefResult (fuel : Nat) : Option (Word × Word × Word × Word) :=
  let (output, buffer) := (MLIR.MemRef.CF.lower 3 shift).run (MLIR.MemRef.CF.evalBody input)
    fuel .nil ⟨initial 1⟩
  output.map fun values => summarize (values.get .here) buffer.cell

private def thetaResult (fuel : Nat) : Option (Word × Word × Word × Word) :=
  (shift.lowerTheta.run (thetaRuntime 3) fuel (Memory.encodeInput (initial 1) input)).map fun result =>
    summarize (result.get .head) (result.get (.tail .head))

-- Both emitters execute two backedges. The first two cells change and
-- the last remains at its original value.
#guard (memrefResult 4).isNone
#guard (thetaResult 2).isNone
#guard memrefResult 5 == some (0, 0, 0, 99)
#guard thetaResult 3 == some (0, 0, 0, 99)

private theorem shiftMemRefRun :
    (MLIR.MemRef.CF.lower 3 shift).run (MLIR.MemRef.CF.evalBody input) 5 .nil ⟨initial 1⟩ =
      (some (.cons 0 .nil), Buffer.mk atExit) :=
  (MLIR.MemRef.CF.cfg_run_eq_some_iff_returnsAfter shift input 5 (initial 1) 0 atExit).mpr
    ⟨2, by decide, (shift.returnsAfter_iff_evalAfter input (initial 1) 2 0 atExit).mpr (by cbv)⟩

example : MLIR.MemRef.CF.Institution.observe (P := sig) shift model (initial 1) = Part.some (0, atExit) :=
  (memref_observation_iff_theta_returns (P := sig) shift model (initial 1) 0 atExit).mpr
    ((memref_run_iff_theta_run (P := sig) shift model (initial 1) 0 atExit).mp ⟨5, shiftMemRefRun⟩)

private theorem shiftPortable : Portable.Observation shift input (initial 1) 2 0 atExit :=
  (shift.returnsAfter_iff_portable input (initial 1) 2 0 atExit).mp
    ((shift.returnsAfter_iff_evalAfter input (initial 1) 2 0 atExit).mpr (by cbv))

private theorem shiftMemRefFromPetri :
    MLIR.MemRef.CF.Institution.observe (P := sig) shift model (initial 1) = Part.some (0, atExit) :=
  (petri_completion_iff_memref (P := sig) shift model (initial 1) 0 atExit).mp shiftPortable.petriCompletion

example : Finishes (thetaRuntime 3) shift.lowerTheta (Memory.encodeInput (initial 1) input)
    (Memory.encodeResult 0 atExit) :=
  (petri_completion_iff_memref_run (P := sig) shift model (initial 1) 0 atExit).mpr ⟨5, shiftMemRefRun⟩

private def wrongSentinel : Heap 3 := atExit.write untouched 0

-- Keeping the returned word and the two updated cells cannot hide an
-- incorrect value for the untouched sentinel.
example : ¬ Finishes (thetaRuntime 3) shift.lowerTheta (Memory.encodeInput (initial 1) input)
    (Memory.encodeResult 0 wrongSentinel) := by
  intro completed
  have observed := (petri_completion_iff_memref (P := sig) shift model (initial 1) 0 wrongSentinel).mp completed
  have same := Part.some_inj.mp (shiftMemRefFromPetri.symm.trans observed)
  exact (by decide : atExit untouched ≠ wrongSentinel untouched)
    (congrArg (fun result : Word × Heap 3 => result.2 untouched) same)

private def clearAt (address : RVSDG.Origin args [[.word]] .address) : Graph args :=
  ⟨.load (.latest 0) headWire
    (.store (.latest 0) address (.arg (.tail (.tail .head)))
      (.ret (.latest 1) (.output (0 : Fin 1) .head))),
    rfl, .tail (.tail .head)⟩

private def clearTail : Graph args := clearAt tailWire

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
private theorem heapMismatch : ¬ MLIR.MemRef.CF.Institution.Holds equation model := by
  intro holds
  have same := (observeImmediate shift shiftHeap (by cbv)).symm.trans
    ((holds (initial 0)).trans (observeImmediate clearTail clearedHeap (by cbv)))
  have cell := congrArg (fun result : Word × Heap 3 => result.2 headCell) (Part.some_inj.mp same)
  exact (by decide : shiftHeap headCell ≠ clearedHeap headCell) cell

example : ¬ petriHolds equation model :=
  fun holds => heapMismatch ((petri_satisfaction_iff_memref equation model).mp holds)

private theorem noMemRef : MLIR.MemRef.CF.Institution.observe (P := sig) clearTail model cycling = Part.none :=
  (MLIR.MemRef.CF.Institution.observe_eq (P := sig) clearTail model cycling).trans
    ((mlir_no_return_iff clearTail model cycling).mp noCF)

example : thetaObservation clearTail model cycling = Part.none :=
  (theta_no_return_iff_memref (P := sig) clearTail model cycling).mpr noMemRef

example : ∀ output, ¬ Finishes (thetaRuntime 3) clearTail.lowerTheta
    (Memory.encodeInput cycling input) output :=
  (petri_no_completion_iff_memref (P := sig) clearTail model cycling).mpr noMemRef

example : MLIR.Institution.observe (P := sig) clearTail model cycling = Part.none :=
  (mlir_observation_eq_map_memref (P := sig) clearTail model cycling).trans (by rw [noMemRef, Part.map_none])

private def clearHead : Graph args := clearAt headWire
private def budgetEquation : Equation sig := ⟨clearHead, clearTail⟩
private def clearedHead : Heap 3 := (cycling.write headCell 0).write headCell 0

-- The first activation takes a backedge on both sides. Clearing the
-- loaded cell lets the left side exit on its next activation.
#guard (MLIR.MemRef.CF.run clearHead input 0 ⟨cycling⟩).isNone
#guard (MLIR.MemRef.CF.run clearTail input 0 ⟨cycling⟩).isNone
#guard (MLIR.MemRef.CF.run clearHead input 1 ⟨cycling⟩).map
  (fun (word, buffer) => summarize word buffer.cell) == some (0, 0, 0, 99)

example : ¬ petriHolds budgetEquation model := by
  intro holds
  have completed := (clearHead.lowerTheta_finishes_iff input cycling 0 clearedHead).mp
    ⟨1, (clearHead.returnsAfter_iff_evalAfter input cycling 1 0 clearedHead).mpr (by cbv)⟩
  exact ((petri_no_completion_iff_memref (P := sig) clearTail model cycling).mpr noMemRef) _
    ((holds cycling 0 clearedHead).mp completed)

private def swap : sig ⟶ sig :=
  ⟨fun
    | .head => .tail .head
    | .tail .head => .head
    | .tail (.tail .head) => .tail (.tail .head)⟩

example : MLIR.MemRef.CF.Institution.observe (mapGraph swap shift) model (initial 0) =
    MLIR.MemRef.CF.Institution.observe shift (reduct swap model) (initial 0) :=
  MLIR.MemRef.CF.Institution.observe_mapGraph swap shift model (initial 0)

example : thetaHolds (equation.map swap) model ↔ MLIR.MemRef.CF.Institution.Holds equation (reduct swap model) :=
  (theta_satisfaction_iff_memref (equation.map swap) model).trans
    (MLIR.MemRef.CF.Institution.satisfaction_reindex swap equation model)

example : petriHolds (equation.map swap) model ↔ MLIR.MemRef.CF.Institution.Holds equation (reduct swap model) :=
  (petri_satisfaction_reindex swap equation model).trans (petri_satisfaction_iff_memref equation (reduct swap model))

end Silmaril.SSA.SeaOfNodes.Memory.Loop.Institution.Lowering.Backends
