module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Defs
import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef.Defs

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Fixture

open RVSDG (Tuple)

abbrev args : List ValueSort := [.address, .address, .word, .word]

def body : Memory.Graph (.address :: args) :=
  .load (.latest 0) (.arg .head)
    (.store (.latest 0) (.arg .head) (.arg (.tail (.tail (.tail .head))))
      (.ret (.latest 1) (.output 0 .head)))

def graph : Graph args :=
  ⟨⟨body, rfl, .tail (.tail (.tail (.tail .head)))⟩, .head, .tail .head⟩

def input (feedback : Address 3) : Tuple (Val 3) args :=
  .cons (0 : Address 3) (.cons feedback (.cons (9 : Word) (.cons (0 : Word) .nil)))

def initial (first : Word) : Heap 3 :=
  fun cell => if cell = 0 then first else if cell = 1 then 0 else 99

def afterEntry : Heap 3 := (initial 7).write 0 9
def afterFeedback : Heap 3 := afterEntry.write 1 9

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.Fixture

end

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef

open Fixture
open RVSDG.NestedTheta.Petri (Finishes)
open Silmaril.MLIR.CF.Ordered (Block)
open Silmaril.MLIR.MemRef (Buffer)

private theorem entryHeader : Block.eval (evalBody graph (input 1)) ((lower 3 graph).block .header)
    (arrivalEnv .entry) ⟨initial 7⟩ =
    (.inl ⟨Label.header, arrivalEnv .backedge⟩, ⟨afterEntry⟩) := by
  rw [header_transition]
  rfl

private theorem feedbackHeader : Block.eval (evalBody graph (input 1)) ((lower 3 graph).block .header)
    (arrivalEnv .backedge) ⟨afterEntry⟩ =
    (.inl ⟨Label.exit, .cons 0 .nil⟩, ⟨afterFeedback⟩) := by
  rw [header_transition]
  rfl

-- The existing coloured activation uses the selected operands at each
-- occurrence. These checks seed the two activations independently.
example : Finishes (thetaRuntime 3) graph.activation.activation
    (Memory.encodeInput (initial 7) (graph.operands (input 1) .entry))
    (.cons ⟨1⟩ (Memory.encodeInput afterEntry (graph.operands (input 1) .entry))) :=
  (petri_activation_iff_header graph (input 1) .entry (initial 7) afterEntry true).mpr entryHeader

example : Finishes (thetaRuntime 3) graph.activation.activation
    (Memory.encodeInput afterEntry (graph.operands (input 1) .backedge))
    (.cons ⟨0⟩ (Memory.encodeInput afterFeedback (graph.operands (input 1) .backedge))) :=
  (petri_activation_iff_header graph (input 1) .backedge afterEntry afterFeedback false).mpr feedbackHeader

example : run graph (input 1) 1 ⟨initial 7⟩ = some (0, ⟨afterFeedback⟩) := by
  rw [run_eq_evalWithin]
  rfl

private def summarize (result : Option (Word × Buffer 3)) : Option (Word × Word × Word × Word) :=
  result.map fun (word, final) => (word, final.cell 0, final.cell 1, final.cell 2)

-- The entry activation writes 9 to cell 0 and restarts. The next header
-- reads the old zero of cell 1, writes 9 there, and exits.
#guard (run graph (input 1) 0 ⟨initial 7⟩).isNone
#guard summarize (run graph (input 1) 1 ⟨initial 7⟩) == some (0, 9, 9, 99)

-- Zero backedges executes the entry body and leaves the other cells alone.
#guard summarize (run graph (input 1) 0 ⟨initial 0⟩) == some (0, 9, 0, 99)

-- Aliasing the two ports retains the address and keeps reading 9.
#guard (run graph (input 0) 4 ⟨initial 7⟩).isNone

end Silmaril.SSA.SeaOfNodes.Memory.Loop.CarriedAddress.MemRef
