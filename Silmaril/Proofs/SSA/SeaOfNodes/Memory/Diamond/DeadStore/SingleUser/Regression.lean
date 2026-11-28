module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.SingleUser.Thms

meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.SingleUser.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.SingleUser

open RVSDG (Origin Port Tuple)
open SeaOfNodes.Diamond (Projection)
open Silmaril.MLIR.MemRef (Buffer)
open Discovery.MemRef.CF (Program entryTransition evalBody lowerDiamond run)

private abbrev Args : List ValueSort := [.address, .address, .word]
private def headPort : Port Args .address := .head
private def sidePort : Port Args .address := .tail .head
private def early : Port Args .word := .tail (.tail .head)
private def loaded : Origin Args [[.word]] .word := .output 0 .head
private def newest : Origin Args [[.word], [.word]] .word := .output 0 .head

private def trueArm : Memory.Graph Args :=
  .load (.latest 0) (.arg sidePort)
    (.store (.latest 0) (.arg headPort) (.arg early)
      (.store (.latest 1) (.arg headPort) loaded
        (.load (.latest 2) (.arg headPort) (.ret (.latest 2) newest))))

private def trueEdited : Memory.Graph Args :=
  .load (.latest 0) (.arg sidePort)
    (.store (.latest 0) (.arg headPort) loaded
      (.load (.latest 1) (.arg headPort) (.ret (.latest 1) newest)))

private def graph (first : Projection) : Graph Args where
  merge := ⟨first⟩
  arm
    | .onTrue => trueArm
    | .onFalse => .store (.latest 0) (.arg sidePort) (.arg early) (.ret (.latest 1) (.arg early))
  suffix :=
    .store (.latest 0) (.arg (.tail sidePort)) (.arg .head)
      (.load (.latest 1) (.arg (.tail headPort)) (.ret (.latest 1) (.output 0 .head)))

example : usersOf (graph .onFalse) .second 1 = [.store 2] := rfl
example : rewrite (graph .onFalse) .second 1 =
    some (replaceArm (graph .onFalse) .second trueEdited) := rfl

-- The last Load and Phi both consume the retained version. The true
-- arm's Phi occurrence changes with the Region order.
example : usersOf (graph .onTrue) .first 2 = [.load, .incoming .first] := rfl
example : usersOf (graph .onFalse) .second 2 = [.load, .incoming .second] := rfl

-- This cut exposes the actually exported memory of the other arm.
example : usersOf (graph .onFalse) .first 1 = [.incoming .first] := rfl
example : lower 3 (graph .onFalse) .first 1 = none := rfl

private def observer : Memory.Graph Args :=
  .store (.latest 0) (.arg headPort) (.arg early)
    (.load (.latest 1) (.arg sidePort)
      (.store (.latest 1) (.arg headPort) loaded (.ret (.latest 2) loaded)))

private def graphWithObserver : Graph Args :=
  replaceArm (graph .onFalse) .second observer

-- The extra Load is a real use, even though it reads another cell.
example : usersOf graphWithObserver .second 1 = [.load, .store 2] := rfl
example : lower 3 graphWithObserver .second 1 = none := rfl

private def input : Tuple (Val 3) Args :=
  .cons (0 : Address 3) (.cons (1 : Address 3) (.cons (99 : Word) .nil))
private def initial : Buffer 3 :=
  ⟨fun address => if address = 0 then 7 else if address = 1 then 11 else 55⟩

private def readback (word : Word) (buffer : Buffer 3) : List Word :=
  word :: List.ofFn buffer.cell

private def joinReadback (program : Program 3 Args) (guard : Bool) : Option (List Word) :=
  let entered := entryTransition program input guard initial
  match entered.1 with
  | .inl ⟨.arm arrival, _⟩ =>
    let next := (program.block (.arm arrival)).eval (evalBody input)
      (.cons (BitVec.ofBool guard) .nil) entered.2
    match next.1 with
    | .inl ⟨.join, words⟩ => some (readback (words.get .here) next.2)
    | _ => none
  | _ => none

private def runEdit (first : Projection) (guard : Bool) (fuel : Nat) :
    Option (List Word × List Word × List Word × List Word) := do
  let source := graph first
  let original := lowerDiamond 3 source none
  let optimized ← lower 3 source (source.merge.slot .onTrue) 1
  let originalJoin ← joinReadback original guard
  let optimizedJoin ← joinReadback optimized guard
  let before ← run original input guard fuel initial
  let after ← run optimized input guard fuel initial
  some (originalJoin, optimizedJoin, readback before.1 before.2, readback after.1 after.2)

/--
info: some
  ([11#64, 11#64, 11#64, 55#64], [11#64, 11#64, 11#64, 55#64], [11#64, 11#64, 11#64, 55#64],
    [11#64, 11#64, 11#64, 55#64])
-/
#guard_msgs in
#eval runEdit .onFalse true 3

#guard runEdit .onTrue true 3 ==
  some ([11, 11, 11, 55], [11, 11, 11, 55], [11, 11, 11, 55], [11, 11, 11, 55])
#guard runEdit .onFalse false 3 ==
  some ([99, 7, 99, 55], [99, 7, 99, 55], [7, 7, 99, 55], [7, 7, 99, 55])
#guard runEdit .onTrue false 3 ==
  some ([99, 7, 99, 55], [99, 7, 99, 55], [7, 7, 99, 55], [7, 7, 99, 55])
#guard runEdit .onFalse true 2 == none

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.SingleUser
