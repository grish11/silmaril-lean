module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore

open RVSDG (Origin Port Tuple)
open SeaOfNodes.Diamond (Merge Projection)
open Silmaril.MLIR.MemRef (Buffer)

private abbrev args : List ValueSort := [.address, .address, .address, .word, .word, .word]

private def headPort : Port args .address := .head
private def leftPort : Port args .address := .tail .head
private def rightPort : Port args .address := .tail (.tail .head)
private def entryWord : Port args .word := .tail (.tail (.tail .head))
private def leftWord : Port args .word := .tail (.tail (.tail (.tail .head)))
private def rightWord : Port args .word := .tail (.tail (.tail (.tail (.tail .head))))

private def loaded : Origin args [[.word]] .word := .output (0 : Fin 1) .head

private def leftArm (readPort : Port args .address) : Memory.Graph args :=
  .load (.latest 0) (.arg readPort)
    (.store (.latest 0) (.arg headPort) (.arg leftWord)
      (.store (.latest 1) (.arg leftPort) (.arg leftWord) (.ret (.latest 2) loaded)))

private def rightArm (overwrite : Bool) : Memory.Graph args :=
  let finish : Memory.Body args [[.word]] 1 :=
    if overwrite then .store (.latest 1) (.arg headPort) (.arg rightWord) (.ret (.latest 2) loaded)
    else .ret (.latest 1) loaded
  .load (.latest 0) (.arg rightPort) (.store (.latest 0) (.arg rightPort) (.arg rightWord) finish)

private def source (first : Projection) (rightOverwrite : Bool := true)
    (leftRead : Port args .address := leftPort) : Prefixed args where
  store := ⟨headPort, entryWord⟩
  diamond := {
    merge := ⟨first⟩
    arm
      | .onTrue => leftArm leftRead
      | .onFalse => rightArm rightOverwrite
    suffix := .ret (.latest 0) (.arg .head) }

private def candidate (first : Projection) : Candidate args := fun arrival =>
  let merge : Merge := ⟨first⟩
  match merge.predecessor arrival with
  | .onTrue => ⟨1, [leftPort]⟩
  | .onFalse => ⟨2, [rightPort]⟩

private def headCell : Address 4 := 0
private def leftCell : Address 4 := 1
private def rightCell : Address 4 := 2

private def input (rightAddress : Address 4 := rightCell) : Tuple (Val 4) args :=
  .cons headCell (.cons leftCell (.cons rightAddress
    (.cons (99 : Word) (.cons (11 : Word) (.cons (33 : Word) .nil)))))

private def initial : Heap 4 := fun address =>
  if address = headCell then 7 else if address = leftCell then 2 else if address = rightCell then 3 else 55

private def afterTrue : Heap 4 := (initial.write headCell 11).write leftCell 11
private def afterFalse : Heap 4 := (initial.write rightCell 33).write headCell 33

private def target (first : Projection) : Graph args :=
  let diamond := (source first).diamond
  { diamond with arm := fun edge =>
    match diamond.merge.slot edge with
    | .first => diamond.arm (diamond.merge.predecessor .first)
    | .second => diamond.arm (diamond.merge.predecessor .second) }

example (first : Projection) :
    rewrite (source first) (candidate first) input = some (target first) := by
  cases first <;> rfl

private def inferred (first : Projection) : Candidate args
  | .first => candidate first .first
  | .second => candidate first .second

private theorem accepted (first : Projection) :
    Discovery.rewrite (source first) input = some ⟨inferred first, target first⟩ := by
  cases first <;> rfl

-- The occurrence order can be reversed. The two witnesses differ in
-- overwrite version and reader port, and only the taken arm writes.
example (first : Projection) : (source first).Returns true input initial 2 afterTrue :=
  (Discovery.rewrite_returns_iff input (accepted first) true initial 2 afterTrue).mp
    (((target first).returns_iff_denote true input initial 2 afterTrue).mpr (by cases first <;> cbv))

example (first : Projection) : (source first).Returns false input initial 3 afterFalse :=
  (Discovery.rewrite_returns_iff input (accepted first) false initial 3 afterFalse).mp
    (((target first).returns_iff_denote false input initial 3 afterFalse).mpr (by cases first <;> cbv))

example (first : Projection) : (Discovery.rewrite (source first) (input 3)).isSome = true := by
  cases first <;> rfl

-- The false predecessor is first and has no qualifying overwrite.
example : (rewriteSlot (source .onFalse false) (candidate .onFalse) input .second).isSome = true := rfl
example : rewriteSlot (source .onFalse false) (candidate .onFalse) input .first = none := rfl
example : rewrite (source .onFalse false) (candidate .onFalse) input = none := rfl
example : Discovery.rewrite (source .onFalse false) input = none := rfl

-- A same-cell read sees 99 from the entry Store. Bypassing that Store
-- would instead return 7. The other arm is still admitted.
example : (rewriteSlot (source .onFalse true headPort) (candidate .onFalse) input .first).isSome = true := rfl
example : rewrite (source .onFalse true headPort) (candidate .onFalse) input = none := rfl
example : ((source .onFalse true headPort).denote true input initial).1 = 99 := by cbv
example : ((source .onFalse true headPort).diamond.denote true input initial).1 = 7 := by cbv

-- The two ports in the false certificate may name one concrete cell.
example : rewrite (source .onFalse) (candidate .onFalse) (input headCell) = none := rfl
example : Discovery.discoverSlot (source .onFalse) .first = some ⟨2, [rightPort]⟩ := rfl
example : (rewriteSlot (source .onFalse) (inferred .onFalse) (input headCell) .second).isSome = true := rfl
example : rewriteSlot (source .onFalse) (inferred .onFalse) (input headCell) .first = none := rfl
example (first : Projection) : Discovery.rewrite (source first) (input headCell) = none := by
  cases first <;> rfl

/-- info: (some (2, 1), true) -/
#guard_msgs in
#eval
  let good := Discovery.rewrite (source .onFalse) input
  let bad := Discovery.rewrite (source .onFalse) (input headCell)
  (good.map fun result =>
    ((result.candidate .first).storeVersion, (result.candidate .second).storeVersion), bad.isNone)

private def readback (result : Word × Buffer 4) : List Word :=
  result.1 :: (List.finRange 4).map result.2.cell

private def runEmitted (first : Projection) (guard : Bool) (fuel : Nat) :
    Option (List Word × List Word) := do
  let programs ← Discovery.MemRef.CF.lower (source first) input
  let before ← Discovery.MemRef.CF.run programs.original programs.input guard fuel ⟨initial⟩
  let after ← Discovery.MemRef.CF.run programs.optimized programs.input guard fuel ⟨initial⟩
  some (readback before, readback after)

-- Each readback lists the returned word followed by all four buffer cells.
/-- info: some ([2#64, 11#64, 11#64, 3#64, 55#64], [2#64, 11#64, 11#64, 3#64, 55#64]) -/
#guard_msgs in
#eval runEmitted .onFalse true 3

/-- info: some ([3#64, 33#64, 2#64, 33#64, 55#64], [3#64, 33#64, 2#64, 33#64, 55#64]) -/
#guard_msgs in
#eval runEmitted .onFalse false 3

#guard (runEmitted .onFalse true 2).isNone
#guard runEmitted .onTrue false 5 == runEmitted .onFalse false 3

private def slotNumber (program : Discovery.MemRef.CF.Program 4 args) (guard : Bool) : Option Nat :=
  match Discovery.MemRef.CF.entryDestination program input guard ⟨initial⟩ with
  | .inl frame => match frame.argsTy, frame.label with
    | _, .arm .first => some 0
    | _, .arm .second => some 1
    | _, .join => none
  | .inr _ => none

#guard ((Discovery.MemRef.CF.lower (source .onFalse) input).map fun programs =>
  (slotNumber programs.original false, slotNumber programs.optimized false,
    slotNumber programs.original true, slotNumber programs.optimized true)) ==
      some (some 0, some 0, some 1, some 1)

-- The false route's alias rejects before either artifact is returned.
example : Discovery.MemRef.CF.lower (source .onFalse) (input headCell) = none := rfl

private def twoStoreEntry : Memory.Graph args :=
  (⟨rightPort, leftWord⟩ : PrefixStore args).prepend (source .onFalse).store.table

private def runSeeded (rightAddress : Address 4) (guard : Bool) :
    Option (List Nat × List Nat × List Nat) := do
  let valuation := input rightAddress
  let graph := (source .onFalse).diamond
  let original := Discovery.MemRef.CF.lowerDiamond 4 graph (some twoStoreEntry)
  let entered := (Discovery.MemRef.CF.entryTransition original valuation guard ⟨initial⟩).2
  let bare := Discovery.MemRef.CF.lowerDiamond 4 graph none
  let before ← Discovery.MemRef.CF.run original valuation guard 3 ⟨initial⟩
  let after ← Discovery.MemRef.CF.run bare valuation guard 3 entered
  some ((List.finRange 4).map (fun cell => (entered.cell cell).toNat),
    (readback before).map BitVec.toNat, (readback after).map BitVec.toNat)

-- Read back the entry buffer, then the word and final cells of each run.
/-- info: some ([99, 2, 11, 55], [11, 33, 2, 33, 55], [11, 33, 2, 33, 55]) -/
#guard_msgs in
#eval runSeeded rightCell false

#guard runSeeded rightCell true == some ([99, 2, 11, 55], [2, 11, 11, 11, 55], [2, 11, 11, 11, 55])

-- When both entry Stores target one cell, the false arm reads the second write.
/-- info: some ([99, 2, 3, 55], [99, 33, 2, 3, 55], [99, 33, 2, 3, 55]) -/
#guard_msgs in
#eval runSeeded headCell false

private def entryWithRead : Memory.Graph args :=
  .store (.latest 0) (.arg headPort) (.arg entryWord)
    (.load (.latest 1) (.arg rightPort)
      (.store (.latest 1) (.arg headPort) loaded (.ret (.latest 2) loaded)))

private def entryAfterEdit : Memory.Graph args :=
  .load (.latest 0) (.arg rightPort)
    (.store (.latest 0) (.arg headPort) loaded (.ret (.latest 1) loaded))

-- The Load, its use as the second Store's operand, and their order survive.
example : Entry.rewrite entryWithRead input = some entryAfterEdit := rfl

private def entryEditDiamond (first : Projection) : Graph args := (source first true headPort).diamond

private def runEntryEdit (first : Projection) (guard : Bool) (fuel : Nat) :
    Option (Word × Word × List Word × List Word) := do
  let programs ← Entry.lower (entryEditDiamond first) entryWithRead input
  let enteredBefore := Discovery.MemRef.CF.entryTransition programs.original programs.input guard ⟨initial⟩
  let enteredAfter := Discovery.MemRef.CF.entryTransition programs.optimized programs.input guard ⟨initial⟩
  let before ← Discovery.MemRef.CF.run programs.original programs.input guard fuel ⟨initial⟩
  let after ← Discovery.MemRef.CF.run programs.optimized programs.input guard fuel ⟨initial⟩
  some (enteredBefore.2.cell headCell, enteredAfter.2.cell headCell, readback before, readback after)

-- Both emitted entries write 3 through the second Store.
/-- info: some (3#64, 3#64, [3#64, 11#64, 11#64, 3#64, 55#64], [3#64, 11#64, 11#64, 3#64, 55#64]) -/
#guard_msgs in
#eval runEntryEdit .onFalse true 3

#guard runEntryEdit .onTrue false 3 == some (3, 3, [3, 33, 2, 33, 55], [3, 33, 2, 33, 55])
#guard (runEntryEdit .onFalse true 2).isNone

-- The distinct reader port aliases the first Store, so the second Store
-- must still receive 99 from the Load. The checker refuses before emission.
example : Entry.lower (entryEditDiamond .onFalse) entryWithRead (input headCell) = none := rfl

#guard ((Discovery.MemRef.CF.run
    (Discovery.MemRef.CF.lowerDiamond 4 (entryEditDiamond .onFalse) (some entryWithRead))
    (input headCell) false 3 ⟨initial⟩).map readback) == some [99, 33, 2, 3, 55]

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore
