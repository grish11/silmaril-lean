module

import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Fixture
meta import Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef.Defs
meta import Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.TwoAddress.Fixture

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef

open Fixture
open RVSDG.NestedTheta.Petri (Finishes)
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.CF.Ordered (Block)
open Silmaril.MLIR.MemRef (Buffer)

-- Each conditional edge evaluates the two operands in the old bank.
example : (Block.eval (evalBody (input 1)) ((lower 4 graph).block .header)
    (encodeAddresses 0 1)).run ⟨initial⟩ =
    some (.inl ⟨Label.header, encodeAddresses 1 0⟩, ⟨afterFirst⟩) := by
  rw [header_transition graph (input 1) ⟨0, 1, initial⟩]
  rfl

example : (Block.eval (evalBody (input 1)) ((lower 4 graph).block .header)
    (encodeAddresses 1 0)).run ⟨afterFirst⟩ =
    some (.inl ⟨Label.header, encodeAddresses 0 1⟩, ⟨afterSecond⟩) := by
  rw [header_transition graph (input 1) ⟨1, 0, afterFirst⟩]
  rfl

example : (Block.eval (evalBody (input 1)) ((lower 4 graph).block .header)
    (encodeAddresses 0 1)).run ⟨afterSecond⟩ =
    some (.inl ⟨Label.exit, .cons 0 .nil⟩, ⟨final⟩) := by
  rw [header_transition graph (input 1) ⟨0, 1, afterSecond⟩]
  rfl

-- The first operand is valid but the second bit pattern names no cell.
private def invalid : Env (headerTypes 4) := .cons 0 (.cons 4 .nil)

example : (Block.eval (evalBody (input 1)) ((lower 4 graph).block .header) invalid).run ⟨initial⟩ =
    none :=
  header_rejects graph (input 1) invalid ⟨initial⟩ rfl

private theorem swap_returns : runFuel graph (input 1) 5 ⟨initial⟩ = some (0, ⟨final⟩) :=
  (run_eq_evalWithin graph (input 1) 2 initial).trans rfl

example : Finishes (thetaRuntime 4) (Petri.lower graph) (encodeInput initial (input 1))
    (encodeResult 0 final) :=
  (petri_finishes_iff_runFuel graph (input 1) initial 0 final).mpr ⟨5, swap_returns⟩

example : runFuel graph (input 0) 4 ⟨initial⟩ = some (0, ⟨aliased⟩) :=
  (run_eq_evalWithin graph (input 0) 1 initial).trans rfl

private def summarize (result : Option (Word × Buffer 4)) :
    Option (Word × Word × Word × Word × Word) :=
  result.map fun (word, final) => (word, final.cell 0, final.cell 1, final.cell 2, final.cell 3)

#guard (runFuel graph (input 1) 4 ⟨initial⟩).isNone
#guard summarize (runFuel graph (input 1) 5 ⟨initial⟩) == some (0, 0, 0, 0, 42)
#guard (runFuel graph (input 0) 3 ⟨initial⟩).isNone
#guard summarize (runFuel graph (input 0) 4 ⟨initial⟩) == some (0, 0, 5, 0, 42)

end Silmaril.SSA.SeaOfNodes.Memory.Loop.TwoAddress.MemRef
