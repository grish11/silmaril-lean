module

import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.SingleUser.Thms
import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Defs

meta import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.SingleUser.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.DeadStore.SingleUser

open RVSDG (Origin Port Tuple)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

private abbrev Args : List ValueSort := [.address, .address, .word]
private def observed : Port Args .address := .head
private def side : Port Args .address := .tail .head
private def early : Port Args .word := .tail (.tail .head)

private def loaded : Origin Args [[.word]] .word := .output 0 .head
private def firstLoad : Origin Args [[.word], [.word]] .word := .output 1 .head
private def lastLoad : Origin Args [[.word], [.word]] .word := .output 0 .head

-- The retained Store gets its data from the prefix read. The final read
-- observes the overwrite, and Return exports the full buffer.
private def source (overwrite : Port Args .address := observed) : Graph Args :=
  .load (.latest 0) (.arg side)
    (.store (.latest 0) (.arg observed) (.arg early)
      (.store (.latest 1) (.arg overwrite) loaded
        (.load (.latest 2) (.arg observed) (.ret (.latest 2) lastLoad))))

private def target : Graph Args :=
  .load (.latest 0) (.arg side)
    (.store (.latest 0) (.arg observed) loaded
      (.load (.latest 1) (.arg observed) (.ret (.latest 1) lastLoad)))

private def input (sideCell : Address 3 := 1) : Tuple (Val 3) Args :=
  .cons (0 : Address 3) (.cons sideCell (.cons (99 : Word) .nil))

private def initial : Heap 3 := fun address => if address = 0 then 7 else if address = 1 then 11 else 55

example : usersOf 1 source = [.store 2] := rfl
private theorem checked : rewrite source 1 = some target := rfl

example (ordinal : Nat) :
    readAt target ordinal input PUnit.unit initial = readAt source ordinal input PUnit.unit initial :=
  rewrite_readAt checked ordinal input initial

private def run (graph : Graph Args) (valuation : Tuple (Val 3) Args) : List Word :=
  let result := observe graph valuation ⟨initial⟩
  result.1 :: List.ofFn result.2.cell

/-- info: some ([11#64, 11#64, 11#64, 55#64], [11#64, 11#64, 11#64, 55#64]) -/
#guard_msgs in
#eval (rewrite source 1).map fun optimized => (run source input, run optimized input)

#guard ((rewrite source 1).map fun optimized => run optimized (input 0)) == some [7, 7, 11, 55]

-- This real Load and the overwriting Store both use version one.
-- Even with a disjoint reader, the chapter 10 single-user gate refuses.
private def secondUse : Graph Args :=
  .load (.latest 0) (.arg side)
    (.store (.latest 0) (.arg observed) (.arg early)
      (.load (.latest 1) (.arg side)
        (.store (.latest 1) (.arg observed) firstLoad (.ret (.latest 2) firstLoad))))

example : usersOf 1 secondUse = [.load, .store 2] := rfl
example : rewrite secondUse 1 = none := rfl
example : (DeadStore.rewrite secondUse ⟨1, 2⟩ ⟨observed, [side]⟩ input).isSome = true := rfl

-- Return uses and exports version one directly when there is no overwrite.
private def escapes : Graph Args :=
  .store (.latest 0) (.arg observed) (.arg early) (.ret (.latest 1) (.arg early))

example : usersOf 1 escapes = [.ret] := rfl
example : rewrite escapes 1 = none := rfl
#guard run escapes input == [99, 99, 11, 55]

-- Two original pointer ports are different even when this invocation
-- resolves them to the same initialized cell.
example : usersOf 1 (source side) = [.store 2] := rfl
example : rewrite (source side) 1 = none := rfl
#guard run (source side) (input 0) == run source (input 0)

end Silmaril.SSA.SeaOfNodes.Memory.DeadStore.SingleUser
