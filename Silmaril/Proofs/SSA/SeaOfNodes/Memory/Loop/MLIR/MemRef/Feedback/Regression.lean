module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Feedback.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Feedback.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef

open Fixture
open Silmaril.MLIR.MemRef (Buffer)

private def summarize (result : Option (Word × Buffer 3)) : Option (Word × Word × Word × Word) :=
  result.map fun (word, final) => (word, final.cell 0, final.cell 1, final.cell 2)

-- The mandatory entry activation updates the heap even on immediate exit.
#guard summarize (runAfter shift input 0 ⟨initial 0⟩) == some (0, 2, 0, 99)
#guard (runAfter shift input 1 ⟨initial 0⟩).isNone

private def oneBackedge : Buffer 3 :=
  ⟨fun cell => if cell = headCell then 1 else if cell = tailCell then 0 else 99⟩

-- The first activation reads 1 and overwrites that cell with 0. The
-- second activation exits because it reads the post-store buffer.
#guard (runAfter shift input 0 oneBackedge).isNone
#guard summarize (runAfter shift input 1 oneBackedge) == some (0, 0, 0, 99)
#guard (runAfter shift input 2 oneBackedge).isNone

#guard summarize (runAfter shift input 2 ⟨initial 1⟩) == some (0, 0, 0, 99)

example : (0, Buffer.mk atExit) ∈ observe shift input ⟨initial 1⟩ := by
  apply (mem_observe_iff_exists_runAfter shift input _ _).mpr
  have evaluated : shift.evalAfter input (initial 1) 2 = some (0, atExit) := by cbv
  exact ⟨2, by simp only [runAfter_eq_evalAfter, evaluated, Option.map_some]⟩

private def repeatWrite : Graph Fixture.args :=
  let loaded : RVSDG.Origin Fixture.args [[.word]] .word := .output 0 .head
  ⟨.load (.latest 0) headWire
    (.store (.latest 0) headWire loaded (.ret (.latest 1) loaded)), rfl, .tail (.tail .head)⟩

private theorem repeats :
    observeActivation repeatWrite input ⟨initial 1⟩ = .inr ⟨initial 1⟩ := by
  rw [observeActivation_eq_step]
  change Sum.inr (Buffer.mk ((initial 1).write headCell 1)) = .inr ⟨initial 1⟩
  rw [show (initial 1).write headCell 1 = initial 1 from Function.update_eq_self headCell (initial 1)]

-- Each activation stores the same word before taking another backedge.
#guard (runAfter repeatWrite input 8 ⟨initial 1⟩).isNone

example : observe repeatWrite input ⟨initial 1⟩ = Part.none := by
  apply (observe_eq_none_iff repeatWrite input ⟨initial 1⟩).mpr
  intro count
  induction count with
  | zero => simp only [runAfter, repeats, Sum.elim_inr]
  | succ count ih => simpa only [runAfter, repeats, Sum.elim_inr] using ih

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef
