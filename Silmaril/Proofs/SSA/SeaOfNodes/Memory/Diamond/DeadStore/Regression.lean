module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.StoreTail.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Staged.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Staged.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.LoadTail.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Reindex.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Inference.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Discovery.MemRef.CF.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.StoreTail.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Staged.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.Staged.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Static.Final.LoadTail.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Reindex.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Inference.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.Institution.Defs

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

private def rightArm (overwrite : Bool) (readPort : Port args .address := rightPort) : Memory.Graph args :=
  let finish : Memory.Body args [[.word]] 1 :=
    if overwrite then .store (.latest 1) (.arg headPort) (.arg rightWord) (.ret (.latest 2) loaded)
    else .ret (.latest 1) loaded
  .load (.latest 0) (.arg readPort) (.store (.latest 0) (.arg rightPort) (.arg rightWord) finish)

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

private def runEntryPrograms (programs : Discovery.MemRef.CF.Programs 4 args) (guard : Bool) (fuel : Nat) :
    Option (Word × Word × List Word × List Word) := do
  let enteredBefore := Discovery.MemRef.CF.entryTransition programs.original programs.input guard ⟨initial⟩
  let enteredAfter := Discovery.MemRef.CF.entryTransition programs.optimized programs.input guard ⟨initial⟩
  let before ← Discovery.MemRef.CF.run programs.original programs.input guard fuel ⟨initial⟩
  let after ← Discovery.MemRef.CF.run programs.optimized programs.input guard fuel ⟨initial⟩
  some (enteredBefore.2.cell headCell, enteredAfter.2.cell headCell, readback before, readback after)

private def runEntryEdit (first : Projection) (guard : Bool) (fuel : Nat) :
    Option (Word × Word × List Word × List Word) := do
  let programs ← Entry.lower (entryEditDiamond first) entryWithRead input
  runEntryPrograms programs guard fuel

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

private def sideStore : PrefixStore args := ⟨leftPort, leftWord⟩
private def entryWithSideStore : Memory.Graph args := sideStore.prepend entryWithRead
private def entryWithoutSelected : Memory.Graph args := sideStore.prepend entryAfterEdit

example : Entry.rewriteSelected entryWithSideStore 2 input =
    some ⟨⟨2, 3⟩, ⟨headPort, [rightPort]⟩, entryWithoutSelected⟩ := rfl

-- The side Store can also sit between the selected Store and its overwrite.
example : Entry.rewriteSelected ((source .onFalse).store.prepend entryWithoutSelected) 1 input =
    some ⟨⟨1, 3⟩, ⟨headPort, [rightPort]⟩, entryWithoutSelected⟩ := rfl

example : Entry.lowerSelected (entryEditDiamond .onFalse) entryWithRead 1 input =
    Entry.lower (entryEditDiamond .onFalse) entryWithRead input := rfl

private def runSelectedEntry (guard : Bool) : Option (Word × Word × List Word × List Word) := do
  let programs ← Entry.lowerSelected (entryEditDiamond .onFalse) entryWithSideStore 2 input
  runEntryPrograms programs guard 3

-- The false arm leaves cell one at the retained entry Store's value, 11.
/-- info: some (3#64, 3#64, [3#64, 33#64, 11#64, 33#64, 55#64], [3#64, 33#64, 11#64, 33#64, 55#64]) -/
#guard_msgs in
#eval runSelectedEntry false

#guard runSelectedEntry true == some (3, 3, [3, 11, 11, 3, 55], [3, 11, 11, 3, 55])

example : Entry.lowerSelected (entryEditDiamond .onFalse) entryWithSideStore 2 (input headCell) = none := rfl

#guard ((Discovery.MemRef.CF.run
    (Discovery.MemRef.CF.lowerDiamond 4 (entryEditDiamond .onFalse) (some entryWithSideStore))
    (input headCell) false 3 ⟨initial⟩).map readback) == some [99, 33, 11, 3, 55]

private def repeatedEntry : Memory.Graph args :=
  (⟨leftPort, entryWord⟩ : PrefixStore args).prepend entryWithSideStore

private def lowerRepeatedEntry (rightAddress : Address 4) : Entry.Repeated 4 args :=
  Entry.lowerRepeated (entryEditDiamond .onFalse) repeatedEntry (input rightAddress)

example : (lowerRepeatedEntry rightCell).entry = entryWithoutSelected := rfl
example : (lowerRepeatedEntry rightCell).deleted = 2 := rfl

-- The second deletion sees versions 2 and 3 after the first deletion's
-- renumbering. Those Stores had versions 3 and 4 in the original table.
example : Memory.DeadStore.Search.Selection.Readers.rewrite repeatedEntry input =
    some ⟨⟨1, 2⟩, ⟨leftPort, []⟩, entryWithSideStore⟩ := rfl
example : (Memory.DeadStore.Search.Selection.Readers.rewrite entryWithSideStore input).map
    (fun step => (step.candidate.removeVersion, step.candidate.overwriteVersion)) = some (2, 3) := rfl

private def runRepeatedEntry (rightAddress : Address 4) (guard : Bool) (fuel : Nat) :
    Nat × Option (Word × Word × List Word × List Word) :=
  let result := lowerRepeatedEntry rightAddress
  (result.deleted, runEntryPrograms result.programs guard fuel)

/-- info: (2, some (3#64, 3#64, [3#64, 33#64, 11#64, 33#64, 55#64], [3#64, 33#64, 11#64, 33#64, 55#64])) -/
#guard_msgs in
#eval runRepeatedEntry rightCell false 3

#guard runRepeatedEntry rightCell true 3 == (2, some (3, 3, [3, 11, 11, 3, 55], [3, 11, 11, 3, 55]))
#guard runRepeatedEntry rightCell false 2 == (2, none)

-- The side deletion is committed. The aliased Load protects the later
-- candidate and both emitted CFGs still return the observed 99.
example : (lowerRepeatedEntry headCell).entry = entryWithSideStore := rfl
example : (lowerRepeatedEntry headCell).deleted = 1 := rfl
example : Memory.DeadStore.Search.Selection.Readers.rewrite (lowerRepeatedEntry headCell).entry
    (input headCell) = none := rfl
#guard runRepeatedEntry headCell false 3 == (1, some (99, 99, [99, 33, 11, 3, 55], [99, 33, 11, 3, 55]))

-- Starting at the already exhausted entry emits a zero-deletion pair.
example : Entry.lowerRepeated (entryEditDiamond .onFalse) entryWithSideStore (input headCell) =
    ⟨entryWithSideStore, 0, Entry.lowerPair (entryEditDiamond .onFalse)
      entryWithSideStore entryWithSideStore (input headCell)⟩ := rfl

private def residualEntry : Memory.Graph args :=
  .store (.latest 0) (.arg headPort) (.arg entryWord) (.ret (.latest 1) (.arg leftWord))

private def composedEntry : Memory.Graph args :=
  (⟨headPort, leftWord⟩ : PrefixStore args).prepend residualEntry

private def lowerComposed (rightAddress : Address 4) : Entry.Composition.Result 4 args :=
  Entry.Composition.lower (source .onFalse).diamond composedEntry (input rightAddress)

-- The residual Return names a different word, and the entry boundary uses its heap.
example : (Entry.lowerRepeated (source .onFalse).diamond composedEntry input).entry = residualEntry := rfl
example : Entry.Composition.asPrefixStore residualEntry = some (source .onFalse).store := rfl
example : Entry.Composition.asPrefixStore entryAfterEdit = none := rfl

private def runComposed (rightAddress : Address 4) (guard : Bool) (fuel : Nat) :
    Nat × Bool × Option (Word × Word × List Word × List Word) :=
  let result := lowerComposed rightAddress
  (result.entryDeleted, result.allPathDeleted, runEntryPrograms result.programs guard fuel)

-- The final observations agree even when the successful all-path step changes the entry buffer.
/-- info: (1, true, some (99#64, 7#64, [3#64, 33#64, 2#64, 33#64, 55#64], [3#64, 33#64, 2#64, 33#64, 55#64])) -/
#guard_msgs in
#eval runComposed rightCell false 3

#guard runComposed rightCell true 3 == (1, true, some (99, 7, [2, 11, 11, 3, 55], [2, 11, 11, 3, 55]))
#guard runComposed rightCell false 2 == (1, true, none)

-- At this valuation only the false route's reader aliases. The accepted
-- entry-local edit still supplies the optimized artifact.
example : Entry.Composition.rewriteResidual (source .onFalse).diamond residualEntry (input headCell) = none := rfl
example : (lowerComposed headCell).programs =
    (Entry.lowerRepeated (source .onFalse).diamond composedEntry (input headCell)).programs := rfl
#guard runComposed headCell false 3 == (1, false, some (99, 99, [99, 33, 2, 3, 55], [99, 33, 2, 3, 55]))

private def liveStore : PrefixStore args := ⟨leftPort, rightWord⟩
private def residualWithSide : Memory.Graph args := (source .onFalse).store.prepend liveStore.table
private def entryWithLiveStore : Memory.Graph args :=
  (⟨headPort, leftWord⟩ : PrefixStore args).prepend residualWithSide

private def lowerWithLiveStore (rightAddress : Address 4) : Entry.Composition.Result 4 args :=
  Entry.Composition.Retained.lower (source .onFalse).diamond entryWithLiveStore 1 (input rightAddress)

example : (Entry.lowerRepeated (source .onFalse).diamond entryWithLiveStore input).entry = residualWithSide := rfl
example : Entry.Composition.Retained.rewrite (source .onFalse).diamond
    (liveStore.prepend (source .onFalse).store.table) 2 input =
      some ⟨Entry.Composition.Retained.storeTable entryWord 0 [liveStore],
        ⟨inferred .onFalse, target .onFalse⟩⟩ := rfl
example : Entry.Composition.Retained.rewrite (source .onFalse).diamond residualWithSide 3 input = none := rfl

private def runWithLiveStore (rightAddress : Address 4) (guard : Bool) :
    Nat × Bool × List Nat × Option (List Nat × List Nat) :=
  let result := lowerWithLiveStore rightAddress
  let programs := result.programs
  let entered := (Discovery.MemRef.CF.entryTransition programs.optimized programs.input guard ⟨initial⟩).2
  let returned := (runEntryPrograms programs guard 3).map fun (_, _, before, after) =>
    (before.map BitVec.toNat, after.map BitVec.toNat)
  (result.entryDeleted, result.allPathDeleted, (List.finRange 4).map (fun i => (entered.cell i).toNat), returned)

-- Version 1 moves past the disjoint side Store for checking. The emitted
-- entry keeps that Store and the false arm leaves its 33 in cell one.
/-- info: (1, true, [7, 33, 3, 55], some ([3, 33, 33, 33, 55], [3, 33, 33, 33, 55])) -/
#guard_msgs in
#eval runWithLiveStore rightCell false

#guard runWithLiveStore rightCell true ==
  (1, true, [7, 33, 3, 55], some ([33, 11, 11, 3, 55], [33, 11, 11, 3, 55]))

-- Only the false path reads the nominated cell at this valuation. The
-- earlier entry deletion stays committed and the false route returns 99.
example : Entry.Composition.Retained.rewrite (source .onFalse).diamond residualWithSide 1
    (input headCell) = none := rfl
example : (lowerWithLiveStore headCell).programs =
    (Entry.lowerRepeated (source .onFalse).diamond entryWithLiveStore (input headCell)).programs := rfl
#guard runWithLiveStore headCell false ==
  (1, false, [99, 33, 3, 55], some ([99, 33, 33, 3, 55], [99, 33, 33, 3, 55]))

private def chainInput (left right : Address 4) : Tuple (Val 4) args :=
  .cons headCell (.cons left (.cons right
    (.cons (99 : Word) (.cons (11 : Word) (.cons (33 : Word) .nil)))))

private def lastSideStore : PrefixStore args := ⟨rightPort, rightWord⟩
private def middleStore : PrefixStore args := (source .onFalse).store
private def threeStoreResidual : Memory.Graph args :=
  sideStore.prepend (middleStore.prepend lastSideStore.table)
private def entryWithChain : Memory.Graph args :=
  (⟨headPort, leftWord⟩ : PrefixStore args).prepend threeStoreResidual

private def chainDiamond : Graph args := (source .onFalse true rightPort).diamond
private def retainedAliases : Tuple (Val 4) args := input leftCell
private def nominatedAliases : Tuple (Val 4) args := chainInput headCell rightCell

example : (Entry.lowerRepeated chainDiamond entryWithChain retainedAliases).entry = threeStoreResidual := rfl
example : (Entry.Composition.Retained.rewrite chainDiamond threeStoreResidual 2 retainedAliases).map
    (fun edit => edit.retained) = some (sideStore.prepend lastSideStore.table) := rfl
example : Entry.Composition.Retained.rewrite chainDiamond threeStoreResidual 0 retainedAliases = none := rfl
example : Entry.Composition.Retained.rewrite chainDiamond entryWithRead 1 retainedAliases = none := rfl

private def runChain (entry : Memory.Graph args) (valuation : Tuple (Val 4) args) (guard : Bool) :
    Nat × Bool × List Nat × Option (List Nat × List Nat) :=
  let result := Entry.Composition.Retained.lower chainDiamond entry 2 valuation
  let programs := result.programs
  let entered := (Discovery.MemRef.CF.entryTransition programs.optimized programs.input guard ⟨initial⟩).2
  let returned := (runEntryPrograms programs guard 3).map fun (_, _, before, after) =>
    (before.map BitVec.toNat, after.map BitVec.toNat)
  (result.entryDeleted, result.allPathDeleted, (List.finRange 4).map (fun i => (entered.cell i).toNat), returned)

-- The retained Stores alias on cell one. Both routes read the last write, 33.
/-- info: (1, true, [7, 33, 3, 55], some ([33, 33, 33, 3, 55], [33, 33, 33, 3, 55])) -/
#guard_msgs in
#eval runChain entryWithChain retainedAliases false

#guard runChain entryWithChain retainedAliases true ==
  (1, true, [7, 33, 3, 55], some ([33, 11, 11, 3, 55], [33, 11, 11, 3, 55]))

-- The prefix alias survives entry-local deletion because the address ports
-- differ. Only the disjoint suffix is crossed. The retained entry exposes 11
-- in cell zero until the selected route overwrites it.
example : (Entry.lowerRepeated chainDiamond entryWithChain nominatedAliases).entry = threeStoreResidual := rfl
example : (Entry.Composition.Retained.rewrite chainDiamond threeStoreResidual 2 nominatedAliases).map
    (fun edit => edit.retained) = some (sideStore.prepend lastSideStore.table) := rfl

/-- info: (1, true, [11, 2, 33, 55], some ([33, 33, 2, 33, 55], [33, 33, 2, 33, 55])) -/
#guard_msgs in
#eval runChain entryWithChain nominatedAliases false

#guard runChain entryWithChain nominatedAliases true ==
  (1, true, [11, 2, 33, 55], some ([33, 11, 2, 33, 55], [33, 11, 2, 33, 55]))

private def suffixAliasResidual : Memory.Graph args := lastSideStore.prepend (middleStore.prepend sideStore.table)
private def suffixAliasEntry : Memory.Graph args :=
  (⟨headPort, leftWord⟩ : PrefixStore args).prepend suffixAliasResidual

-- The same concrete alias now lies after the nomination. Both route
-- certificates pass on their own. The suffix refusal keeps stage one.
example : (Entry.lowerRepeated chainDiamond suffixAliasEntry nominatedAliases).entry = suffixAliasResidual := rfl
example : (Discovery.rewrite ⟨middleStore, chainDiamond⟩ nominatedAliases).isSome = true := rfl
example : Entry.Composition.Retained.rewrite chainDiamond suffixAliasResidual 2 nominatedAliases = none := rfl
example : (Entry.Composition.Retained.lower chainDiamond suffixAliasEntry 2 nominatedAliases).programs =
    (Entry.lowerRepeated chainDiamond suffixAliasEntry nominatedAliases).programs := rfl
#guard runChain suffixAliasEntry nominatedAliases false ==
  (1, false, [11, 2, 33, 55], some ([33, 33, 2, 33, 55], [33, 33, 2, 33, 55]))

private def retainedLoadEntry : Memory.Graph args :=
  .load (.latest 0) (.arg rightPort)
    (.store (.latest 0) (.arg leftPort) loaded (.ret (.latest 1) loaded))

private def residualLoadEntry : Memory.Graph args := middleStore.prepend retainedLoadEntry
private def entryLoading : Memory.Graph args :=
  (⟨headPort, leftWord⟩ : PrefixStore args).prepend residualLoadEntry

private def loadDiamond : Graph args :=
  { (source .onFalse).diamond with
    arm := fun edge => match edge with
      | .onTrue => leftArm leftPort
      | .onFalse => rightArm true leftPort }

example : (Entry.lowerRepeated loadDiamond entryLoading input).entry = residualLoadEntry := rfl
example : Entry.Composition.Retained.Load.cut 1 input residualLoadEntry =
    some (middleStore, retainedLoadEntry) := rfl
example : Entry.Composition.Retained.Load.cut 2 input (sideStore.prepend residualLoadEntry) =
    some (middleStore, sideStore.prepend retainedLoadEntry) := rfl

private def runLoadEdit (valuation : Tuple (Val 4) args) (guard : Bool) :
    Nat × Bool × Option (List Nat × List Nat) :=
  let result := Entry.Composition.Retained.Load.lower loadDiamond entryLoading 1 valuation
  let returned := (runEntryPrograms result.programs guard 3).map fun (_, _, before, after) =>
    (before.map BitVec.toNat, after.map BitVec.toNat)
  (result.entryDeleted, result.allPathDeleted, returned)

-- The entry Load supplies the retained Store operand. The false arm reads
-- 3 from the copied cell and leaves that cell unchanged at exit.
/-- info: (1, true, some ([3, 33, 3, 33, 55], [3, 33, 3, 33, 55])) -/
#guard_msgs in
#eval runLoadEdit input false

#guard runLoadEdit input true == (1, true, some ([3, 11, 11, 3, 55], [3, 11, 11, 3, 55]))

-- Both routes still overwrite and satisfy their own reader checks. The
-- entry Load is the reason to refuse, and the previous deletion survives.
example : (Discovery.rewrite ⟨middleStore, loadDiamond⟩ (input headCell)).isSome = true := rfl
example : Entry.Composition.Retained.Load.cut 1 (input headCell) residualLoadEntry = none := rfl
example : (Entry.Composition.Retained.Load.lower loadDiamond entryLoading 1 (input headCell)).programs =
    (Entry.lowerRepeated loadDiamond entryLoading (input headCell)).programs := rfl
#guard runLoadEdit (input headCell) false == (1, false, some ([99, 33, 99, 3, 55], [99, 33, 99, 3, 55]))

private def twoReadTail : Memory.Graph args :=
  .load (.latest 0) (.arg rightPort)
    (.load (.latest 0) (.arg leftPort)
      (.store (.latest 0) (.arg rightPort) (.output (0 : Fin 2) .head)
        (.ret (.latest 1) (.output (1 : Fin 2) .head))))

private def twoReadResidual : Memory.Graph args := middleStore.prepend twoReadTail
private def entryWithTwoReads : Memory.Graph args :=
  (⟨headPort, leftWord⟩ : PrefixStore args).prepend twoReadResidual

example : (Entry.lowerRepeated chainDiamond entryWithTwoReads input).entry = twoReadResidual := rfl
example : Entry.Composition.Retained.Load.cut 1 input twoReadResidual = some (middleStore, twoReadTail) := rfl

-- The entry Return uses the older binding. The Store uses the newer one.
example : twoReadTail.denote input initial = (3, initial.write rightCell 2) := by cbv

private def runTwoReadEdit (valuation : Tuple (Val 4) args) (guard : Bool) :
    Nat × Bool × Option (List Nat × List Nat) :=
  let result := Entry.Composition.Retained.Load.lower chainDiamond entryWithTwoReads 1 valuation
  let returned := (runEntryPrograms result.programs guard 3).map fun (_, _, before, after) =>
    (before.map BitVec.toNat, after.map BitVec.toNat)
  (result.entryDeleted, result.allPathDeleted, returned)

/-- info: (1, true, some ([2, 33, 2, 33, 55], [2, 33, 2, 33, 55])) -/
#guard_msgs in
#eval runTwoReadEdit input false

#guard runTwoReadEdit input true == (1, true, some ([2, 11, 11, 2, 55], [2, 11, 11, 2, 55]))

-- At this input only the later Load aliases the nominated cell. The
-- first Load, retained Store, and the two route certificates still pass.
example : Entry.Composition.Retained.Load.checkTail middleStore nominatedAliases
    (.load (.latest 0) (.arg rightPort)
      (.store (.latest 0) (.arg rightPort) loaded (.ret (.latest 1) loaded))) = true := rfl
example : (Discovery.rewrite ⟨middleStore, chainDiamond⟩ nominatedAliases).isSome = true := rfl
example : Entry.Composition.Retained.Load.cut 1 nominatedAliases twoReadResidual = none := rfl
example : (Entry.Composition.Retained.Load.lower chainDiamond entryWithTwoReads 1 nominatedAliases).programs =
    (Entry.lowerRepeated chainDiamond entryWithTwoReads nominatedAliases).programs := rfl
#guard runTwoReadEdit nominatedAliases true ==
  (1, false, some ([99, 11, 2, 99, 55], [99, 11, 2, 99, 55]))

private def overwriteTail (firstRead : Port args .address) : Memory.Graph args :=
  .load (.latest 0) (.arg firstRead)
    (.store (.latest 0) (.arg rightPort) loaded
      (.load (.latest 1) (.arg headPort)
        (.store (.latest 1) (.arg leftPort) (.output (0 : Fin 2) .head)
          (.ret (.latest 2) (.output (0 : Fin 2) .head)))))

private def overwriteEntry (firstRead : Port args .address) : Memory.Graph args :=
  (⟨headPort, leftWord⟩ : PrefixStore args).prepend (middleStore.prepend (overwriteTail firstRead))

private def overwriteDiamond : Graph args :=
  { (source .onFalse).diamond with
    arm := fun edge => match edge with
      | .onTrue => leftArm leftPort
      | .onFalse => .load (.latest 0) (.arg headPort) (.ret (.latest 0) loaded) }

private def overwriteInput : Tuple (Val 4) args := input headCell

private def lowerWithOverwrite (firstRead : Port args .address) :
    Entry.Composition.Retained.Load.OverwriteResult 4 args :=
  Entry.Composition.Retained.Load.lowerOverwrite overwriteDiamond (overwriteEntry firstRead) 1 overwriteInput

-- The early same-wire duplicate is removed. The remaining overwrite uses
-- a different port to the same cell, and the false arm only reads it.
example : (Entry.lowerRepeated overwriteDiamond (overwriteEntry leftPort) overwriteInput).entry =
    middleStore.prepend (overwriteTail leftPort) := rfl
example : Discovery.rewrite ⟨middleStore, overwriteDiamond⟩ overwriteInput = none := rfl
example : Entry.Composition.Retained.Load.cutOverwrite 1 overwriteInput
    (middleStore.prepend (overwriteTail leftPort)) = some (middleStore, overwriteTail leftPort) := rfl
example : (lowerWithOverwrite leftPort).programs =
    Entry.lowerPair overwriteDiamond (overwriteEntry leftPort) (overwriteTail leftPort) overwriteInput := rfl

private def runOverwrite (firstRead : Port args .address) (guard : Bool) (fuel : Nat) :
    Nat × Bool × Option (Word × Word × List Word × List Word) :=
  let result := lowerWithOverwrite firstRead
  (result.entryDeleted, result.overwriteDeleted, runEntryPrograms result.programs guard fuel)

-- The first Load supplies 2 to the overwrite. A same-cell Load after it
-- feeds the retained side Store. The false route has no overwrite.
/-- info: (1, true, some (2#64, 2#64, [2#64, 2#64, 2#64, 3#64, 55#64], [2#64, 2#64, 2#64, 3#64, 55#64])) -/
#guard_msgs in
#eval runOverwrite leftPort false 3

#guard runOverwrite leftPort true 3 == (1, true, some (2, 2, [2, 11, 11, 3, 55], [2, 11, 11, 3, 55]))
#guard runOverwrite leftPort false 2 == (1, true, none)

-- Reading through the aliasing port before the overwrite sees 99, so
-- the second deletion refuses and the emitted stage-one edit survives.
example : Entry.Composition.Retained.Load.cutOverwrite 1 overwriteInput
    (middleStore.prepend (overwriteTail rightPort)) = none := rfl
example : (lowerWithOverwrite rightPort).programs =
    (Entry.lowerRepeated overwriteDiamond (overwriteEntry rightPort) overwriteInput).programs := rfl
#guard runOverwrite rightPort false 3 == (1, false, some (99, 99, [99, 99, 99, 3, 55], [99, 99, 99, 3, 55]))

open Entry.Composition.Retained.Load

private def addressFacts : Static.AddressContract args := ⟨⟨headPort, [leftPort]⟩, [rightPort]⟩

private def priorDeletion : Option (Memory.DeadStore.Candidate × Port args .address) :=
  some (⟨1, 2⟩, headPort)

-- This pair is emitted once. Runners take the varying valuation separately.
private def staticPrograms : Static.Programs 4 args :=
  Static.lower 4 overwriteDiamond (overwriteEntry leftPort) 1 addressFacts priorDeletion

private def anotherValuation : Tuple (Val 4) args :=
  .cons (3 : Address 4) (.cons rightCell (.cons (3 : Address 4)
    (.cons (91 : Word) (.cons (13 : Word) (.cons (31 : Word) .nil)))))

example : addressFacts.check overwriteInput = true := rfl
example : addressFacts.check anotherValuation = true := rfl
example : staticPrograms.overwriteDeleted = true := rfl
example : staticPrograms.optimized =
    Discovery.MemRef.CF.lowerDiamond 4 overwriteDiamond (some (overwriteTail leftPort)) := rfl

private def runStatic (programs : Static.Programs 4 args)
    (valuation : Tuple (Val 4) args) (guard : Bool) (fuel : Nat) : Option (List Word × List Word) := do
  let before ← Discovery.MemRef.CF.run programs.original valuation guard fuel ⟨initial⟩
  let after ← Discovery.MemRef.CF.run programs.optimized valuation guard fuel ⟨initial⟩
  some (readback before, readback after)

/-- info: (some ([2#64, 2#64, 2#64, 3#64, 55#64], [2#64, 2#64, 2#64, 3#64, 55#64]),
  some ([3#64, 7#64, 2#64, 3#64, 3#64], [3#64, 7#64, 2#64, 3#64, 3#64])) -/
#guard_msgs in
#eval (runStatic staticPrograms overwriteInput false 3, runStatic staticPrograms anotherValuation false 3)

#guard runStatic staticPrograms anotherValuation true 3 == some ([3, 7, 2, 13, 13], [3, 7, 2, 13, 13])
#guard runStatic staticPrograms anotherValuation true 2 == none

-- The first Load requires a disjointness fact. Contradictory facts are
-- refused before scanning, and a colliding valuation fails validation.
example : Static.cut ⟨⟨headPort, []⟩, [rightPort]⟩ 1 (middleStore.prepend (overwriteTail leftPort)) = none := rfl
example : Static.cut ⟨⟨headPort, [leftPort, rightPort]⟩, [rightPort]⟩ 1
    (middleStore.prepend (overwriteTail leftPort)) = none := rfl
example : addressFacts.check (chainInput headCell headCell) = false := rfl

-- A repeated port supplies equality by itself.
example : Static.cut ⟨⟨headPort, []⟩, []⟩ 1 (middleStore.prepend middleStore.table) =
    some (middleStore, middleStore.table) := rfl

private def staticRefused : Static.Programs 4 args :=
  Static.lower 4 overwriteDiamond (overwriteEntry rightPort) 1 addressFacts priorDeletion

-- The same valid facts identify the pre-overwrite Load as an observer.
-- The independent same-wire deletion is still present in the artifact.
example : staticRefused.overwriteDeleted = false := rfl
example : staticRefused.optimized = Discovery.MemRef.CF.lowerDiamond 4 overwriteDiamond
    (some (middleStore.prepend (overwriteTail rightPort))) := rfl
#guard runStatic staticRefused overwriteInput false 3 == some ([99, 99, 99, 3, 55], [99, 99, 99, 3, 55])

open CategoryTheory
open Diamond.Institution renaming Signature → EntrySignature
open Diamond.Institution (PortMap mapBody mapGraph pullInput)

private def swapAddressPorts : PortMap args args
  | _, .head => leftPort
  | _, .tail .head => headPort
  | _, .tail (.tail port) => .tail (.tail port)

private def identifyAliases : PortMap args args
  | _, .tail (.tail .head) => headPort
  | _, port => port

private def identifyDisjoint : PortMap args args
  | _, .tail .head => headPort
  | _, port => port

private def swapInput : Tuple (Val 4) args := pullInput swapAddressPorts overwriteInput

private def reindexTail : Memory.Graph args :=
  .load (.latest 0) (.arg leftPort)
    (.store (.latest 0) (.arg leftPort) (.arg rightWord)
      (.store (.latest 1) (.arg rightPort) loaded
        (.load (.latest 2) (.arg headPort) (.ret (.latest 2) (.output (0 : Fin 2) .head)))))

private def reindexEntry : Memory.Graph args := middleStore.prepend reindexTail

private def entrySignature : EntrySignature := ⟨args⟩

example : addressFacts.transport swapAddressPorts = some ⟨⟨leftPort, [headPort]⟩, [rightPort]⟩ := rfl
example : addressFacts.transport identifyAliases = some ⟨⟨headPort, [leftPort]⟩, [headPort]⟩ := rfl
example : addressFacts.transport identifyDisjoint = none := rfl
example : pullInput swapAddressPorts swapInput = overwriteInput := rfl
example : pullInput identifyAliases input = overwriteInput := rfl

example : Static.cut ⟨⟨leftPort, [headPort]⟩, [rightPort]⟩ 1 (mapBody swapAddressPorts reindexEntry) =
    some (Static.Reindex.mapStore swapAddressPorts middleStore, mapBody swapAddressPorts reindexTail) :=
  Static.Reindex.cut_transport swapAddressPorts
    (facts := addressFacts) (selected := middleStore) (retained := reindexTail) (entry := reindexEntry)
    rfl rfl

private def runReindexed (rename : PortMap args args) (valuation : Tuple (Val 4) args) (guard : Bool) (fuel : Nat) :
    Option (Bool × Option (List Word × List Word)) := do
  let facts ← addressFacts.transport rename
  if facts.check valuation then
    let h : entrySignature ⟶ entrySignature := ⟨rename⟩
    let target := Static.lower 4 (mapGraph h overwriteDiamond) (mapBody rename reindexEntry) 1 facts
    some (target.overwriteDeleted, runStatic target valuation guard fuel)
  else none

-- The disjoint Store before the overwrite stays in place. The false arm
-- reads the overwritten cell and the true arm reads the retained side Store.
/-- info: some (true, some ([2#64, 2#64, 33#64, 3#64, 55#64], [2#64, 2#64, 33#64, 3#64, 55#64])) -/
#guard_msgs in
#eval runReindexed swapAddressPorts swapInput false 3

#guard runReindexed swapAddressPorts swapInput true 3 == some (true, some ([33, 11, 11, 3, 55], [33, 11, 11, 3, 55]))
#guard (runReindexed swapAddressPorts swapInput false 3).bind Prod.snd ==
  runStatic (Static.lower 4 overwriteDiamond reindexEntry 1 addressFacts) overwriteInput false 3
#guard runReindexed swapAddressPorts swapInput false 2 == some (true, none)
#guard runReindexed identifyAliases input false 3 == runReindexed swapAddressPorts swapInput false 3
#guard runReindexed identifyAliases input true 3 == runReindexed swapAddressPorts swapInput true 3
#guard runReindexed identifyDisjoint input false 3 == none

private def sequenceTail : Memory.Graph args :=
  .store (.latest 0) (.arg rightPort) (.arg rightWord)
    (.load (.latest 1) (.arg headPort)
      (.store (.latest 1) (.arg leftPort) loaded (.ret (.latest 2) loaded)))

private def sequenceMiddle : Memory.Graph args := sideStore.prepend sequenceTail
private def sequenceEntry : Memory.Graph args := middleStore.prepend sequenceMiddle

private def firstStep : Static.Sequence.Step args := ⟨1, addressFacts⟩
private def secondStep : Static.Sequence.Step args := ⟨1, ⟨⟨leftPort, [headPort, rightPort]⟩, []⟩⟩
private def cutPlan : Static.Sequence.Plan args := [firstStep, secondStep]
private def staleStep : Static.Sequence.Step args := { secondStep with version := 2 }

-- First remove the head Store through a must-alias address, then remove
-- the left Store through its own port. The intervening Load of the head
-- cell supplies the retained left Store's value.
example : Static.cut firstStep.facts 1 sequenceEntry = some (middleStore, sequenceMiddle) := rfl
example : Static.cut secondStep.facts 1 sequenceMiddle = some (sideStore, sequenceTail) := rfl
example : cutPlan.rewrite sequenceEntry = some sequenceTail := rfl
example : cutPlan.check overwriteInput = true := rfl
example : Static.Sequence.lower overwriteDiamond sequenceEntry cutPlan overwriteInput =
    some (Entry.lowerPair overwriteDiamond sequenceEntry sequenceTail overwriteInput) := rfl

private def runCutPlan (plan : Static.Sequence.Plan args) (guard : Bool) (fuel : Nat) :
    Option (Word × Word × List Word × List Word) := do
  let programs ← Static.Sequence.lower overwriteDiamond sequenceEntry plan overwriteInput
  runEntryPrograms programs guard fuel

/-- info: some [33, 33, 33, 3, 55] -/
#guard_msgs in
#eval (runCutPlan cutPlan false 3).map (fun (_, _, original, _) => original.map BitVec.toNat)

#guard runCutPlan cutPlan false 3 == some (33, 33, [33, 33, 33, 3, 55], [33, 33, 33, 3, 55])
#guard runCutPlan cutPlan true 3 == some (33, 33, [33, 11, 11, 3, 55], [33, 11, 11, 3, 55])
#guard runCutPlan cutPlan true 2 == none

-- Version two is valid in the original table. After the first successful
-- cut it denotes the retained head-cell overwrite, so the whole plan refuses.
example : (Static.Sequence.Plan.rewrite [staleStep] sequenceEntry).isSome = true := rfl
example : Static.Sequence.Plan.check [firstStep, staleStep] overwriteInput = true := rfl
example : Static.Sequence.Plan.rewrite [firstStep, staleStep] sequenceEntry = none := rfl
example : Static.Sequence.lower overwriteDiamond sequenceEntry [firstStep, staleStep] overwriteInput = none := rfl
example : Static.Sequence.lower overwriteDiamond sequenceEntry cutPlan input = none := rfl

private def runMappedPlan (guard : Bool) : Option (Word × Word × List Word × List Word) := do
  let plan ← cutPlan.transport swapAddressPorts
  let h : entrySignature ⟶ entrySignature := ⟨swapAddressPorts⟩
  let programs ← Static.Sequence.lower (mapGraph h overwriteDiamond)
    (mapBody swapAddressPorts sequenceEntry) plan swapInput
  runEntryPrograms programs guard 3

#guard runMappedPlan false == runCutPlan cutPlan false 3
#guard runMappedPlan true == runCutPlan cutPlan true 3

private def suppliedContracts : List (Static.AddressContract args) := [firstStep.facts, secondStep.facts]

-- The second candidate starts at version 2. The first deletion shifts it
-- to version 1, which the next discovery step records on the current table.
example : Static.Sequence.Search.find sequenceEntry suppliedContracts = some (firstStep, sequenceMiddle) := rfl
example : Static.Sequence.Search.find sequenceMiddle suppliedContracts = some (secondStep, sequenceTail) := rfl
example : Static.Sequence.Search.discover sequenceEntry suppliedContracts = ⟨cutPlan, sequenceTail⟩ := rfl
example : Static.Sequence.Search.find sequenceTail suppliedContracts = none := rfl
example : Static.Sequence.Search.lower overwriteDiamond sequenceEntry suppliedContracts overwriteInput =
    .ok ⟨⟨cutPlan, sequenceTail⟩, Entry.lowerPair overwriteDiamond sequenceEntry sequenceTail overwriteInput⟩ := rfl

private def runDiscovered (entry : Memory.Graph args) (contracts : List (Static.AddressContract args))
    (valuation : Tuple (Val 4) args) (guard : Bool) :
    Option (List Nat × Option (Word × Word × List Word × List Word)) :=
  match Static.Sequence.Search.lower overwriteDiamond entry contracts valuation with
  | .error .invalidContracts => none
  | .ok emission => some (emission.plan.map (·.version), runEntryPrograms emission.programs guard 3)

/-- info: some ([1, 1], some (33#64, 33#64, [33#64, 33#64, 33#64, 3#64, 55#64], [33#64, 33#64, 33#64, 3#64, 55#64])) -/
#guard_msgs in
#eval runDiscovered sequenceEntry suppliedContracts overwriteInput false

#guard runDiscovered sequenceEntry suppliedContracts overwriteInput false == some ([1, 1], runCutPlan cutPlan false 3)
#guard runDiscovered sequenceEntry suppliedContracts overwriteInput true == some ([1, 1], runCutPlan cutPlan true 3)

-- The first same-wire deletion succeeds. A Load through rightPort then
-- observes the retained head Store, so the checker stops at that table.
private def blockedResidual : Memory.Graph args := middleStore.prepend (overwriteTail rightPort)

example : Static.Sequence.Search.discover (overwriteEntry rightPort) [addressFacts] =
    ⟨[firstStep], blockedResidual⟩ := rfl
example : Static.Sequence.Search.find blockedResidual [addressFacts] = none := rfl
#guard runDiscovered (overwriteEntry rightPort) [addressFacts] overwriteInput false ==
  some ([1], some (99, 99, [99, 99, 99, 3, 55], [99, 99, 99, 3, 55]))

-- An already blocked valid table yields an empty plan and runs normally.
-- A false contract, even on that table, is an explicit invocation error.
example : Static.Sequence.Search.lower overwriteDiamond blockedResidual [addressFacts] overwriteInput =
    .ok ⟨⟨[], blockedResidual⟩, Entry.lowerPair overwriteDiamond blockedResidual blockedResidual overwriteInput⟩ := rfl
example : Static.Sequence.Search.lower overwriteDiamond blockedResidual [addressFacts] input =
    .error .invalidContracts := rfl
#guard runDiscovered blockedResidual [addressFacts] overwriteInput false ==
  some ([], some (99, 99, [99, 99, 99, 3, 55], [99, 99, 99, 3, 55]))

open Entry.Composition.Retained.Load.Static.Sequence.Search.Inference (inferContracts)

private def unknownPrefix (tail : Memory.Graph args) : Memory.Graph args :=
  sideStore.prepend (lastSideStore.prepend ((⟨leftPort, entryWord⟩ : PrefixStore args).prepend tail))

private def observedHead : Memory.Graph args :=
  .load (.latest 0) (.arg headPort)
    (.store (.latest 0) (.arg headPort) loaded (.ret (.latest 1) loaded))

private def headWrite : Memory.Graph args := (⟨headPort, rightWord⟩ : PrefixStore args).prepend observedHead

private def inferredEntry : Memory.Graph args :=
  unknownPrefix ((⟨headPort, leftWord⟩ : PrefixStore args).prepend (middleStore.prepend headWrite))

private def inferredFinal : Memory.Graph args := unknownPrefix headWrite

private def inferredPlan : Static.Sequence.Plan args :=
  [⟨4, ⟨⟨headPort, []⟩, []⟩⟩, ⟨4, ⟨⟨headPort, []⟩, []⟩⟩]

example : inferContracts inferredEntry =
    [⟨⟨leftPort, []⟩, []⟩, ⟨⟨rightPort, []⟩, []⟩, ⟨⟨headPort, []⟩, []⟩] := rfl
example : Static.Sequence.Search.discover inferredEntry (inferContracts inferredEntry) =
    ⟨inferredPlan, inferredFinal⟩ := rfl

-- The next head-cell Load observes version four. The first left-cell
-- candidate needs disjointness from rightPort, which inference cannot supply.
example : Static.cut ⟨⟨headPort, []⟩, []⟩ 4 inferredFinal = none := rfl
example : Static.cut ⟨⟨leftPort, []⟩, []⟩ 1 inferredFinal = none := rfl
example : (Static.cut ⟨⟨leftPort, [rightPort]⟩, []⟩ 1 inferredFinal).isSome = true := rfl
example : Static.Sequence.Search.find inferredFinal (inferContracts inferredEntry) = none := rfl

private def runInferred (graph : Graph args) (entry : Memory.Graph args)
    (valuation : Tuple (Val 4) args) (guard : Bool) (fuel : Nat) :
    Option (List Nat × Option (Word × Word × List Word × List Word)) :=
  match Static.Sequence.Search.Inference.lower graph entry valuation with
  | .error .invalidContracts => none
  | .ok emission => some (emission.plan.map (·.version), runEntryPrograms emission.programs guard fuel)

/-- info: some ([4, 4], some (33#64, 33#64, [33#64, 33#64, 99#64, 33#64, 55#64], [33#64, 33#64, 99#64, 33#64, 55#64])) -/
#guard_msgs in
#eval runInferred overwriteDiamond inferredEntry input false 3

#guard runInferred overwriteDiamond inferredEntry input true 3 ==
  some ([4, 4], some (33, 33, [99, 11, 11, 33, 55], [99, 11, 11, 33, 55]))
#guard runInferred overwriteDiamond inferredEntry input true 2 == some ([4, 4], none)
#guard runInferred overwriteDiamond inferredEntry (input leftCell) false 3 ==
  some ([4, 4], some (33, 33, [33, 33, 99, 3, 55], [33, 33, 99, 3, 55]))

-- Routing both Store origins to the same typed argument exposes a cut.
-- Distinct original ports remain unknown even when an invocation aliases them.
private def originalRoutes : Memory.Graph args := middleStore.prepend lastSideStore.table
private def sharedRoute : Memory.Graph args := mapBody identifyAliases originalRoutes
private def routedDiamond : Graph args := mapGraph (⟨identifyAliases⟩ : entrySignature ⟶ entrySignature) overwriteDiamond

example : inferContracts sharedRoute = [⟨⟨headPort, []⟩, []⟩] := rfl
#guard runInferred overwriteDiamond originalRoutes overwriteInput false 3 ==
  some ([], some (33, 33, [33, 33, 2, 3, 55], [33, 33, 2, 3, 55]))
#guard runInferred routedDiamond sharedRoute input false 3 ==
  some ([1], some (33, 33, [33, 33, 2, 3, 55], [33, 33, 2, 3, 55]))

private def overwriteAndRead (word : Port args .word) : Memory.Graph args :=
  .store (.latest 0) (.arg headPort) (.arg word)
    (.load (.latest 1) (.arg headPort) (.ret (.latest 1) loaded))

private def samePortDiamond (first : Projection) (earlyReader : Option (Port args .address) := none) :
    Graph args where
  merge := ⟨first⟩
  arm
    | .onTrue => overwriteAndRead leftWord
    | .onFalse =>
      match earlyReader with
      | none => lastSideStore.prepend (overwriteAndRead rightWord)
      | some reader => .load (.latest 0) (.arg reader)
          (.store (.latest 0) (.arg headPort) (.arg rightWord) (.ret (.latest 1) loaded))
  suffix := .ret (.latest 0) (.arg .head)

private def beforeRouteCut : Memory.Graph args :=
  (⟨headPort, leftWord⟩ : PrefixStore args).prepend middleStore.table

-- Supply the table produced by the existing entry pass explicitly. The
-- surviving Store was version two and is now the singleton at version one.
private def preparedRouteEntry : Memory.Graph args :=
  (Static.Sequence.Search.discover beforeRouteCut (inferContracts beforeRouteCut)).entry

example : preparedRouteEntry = middleStore.table := rfl
example : Entry.Composition.Static.lower 4 (samePortDiamond .onFalse) beforeRouteCut = none := rfl

example : (Entry.Composition.Static.rewrite ⟨middleStore, samePortDiamond .onFalse⟩).map
    (fun edit => ((edit.candidate .first).storeVersion, (edit.candidate .second).storeVersion)) =
      some (2, 1) := rfl
example : (Entry.Composition.Static.rewrite ⟨middleStore, samePortDiamond .onTrue⟩).map
    (fun edit => ((edit.candidate .first).storeVersion, (edit.candidate .second).storeVersion)) =
      some (1, 2) := rfl

private def staticRoutePrograms := Entry.Composition.Static.lower 4 (samePortDiamond .onFalse) preparedRouteEntry

private def runStaticRoutes (valuation : Tuple (Val 4) args) (guard : Bool) (fuel : Nat) :
    Option (Word × Word × List Word × List Word) := do
  let artifacts ← staticRoutePrograms
  runEntryPrograms ⟨valuation, artifacts.original, artifacts.optimized⟩ guard fuel

-- The entry buffer exposes the removed write here. The selected arm
-- restores equality before producing the returned word and final buffer.
/-- info: some (99#64, 7#64, [33#64, 33#64, 2#64, 33#64, 55#64], [33#64, 33#64, 2#64, 33#64, 55#64]) -/
#guard_msgs in
#eval runStaticRoutes input false 3

#guard runStaticRoutes input true 3 == some (99, 7, [11, 11, 2, 3, 55], [11, 11, 2, 3, 55])
#guard runStaticRoutes overwriteInput false 3 == some (99, 7, [33, 33, 2, 3, 55], [33, 33, 2, 3, 55])
#guard runStaticRoutes input false 2 == none

-- The false occurrence observes the residual Store before overwriting it.
-- The true occurrence still has an empty reader certificate.
private def observingRoute : Graph args := samePortDiamond .onFalse (some headPort)

example : Discovery.discoverSlot ⟨middleStore, observingRoute⟩ .first = none := rfl
example : Discovery.discoverSlot ⟨middleStore, observingRoute⟩ .second = some ⟨1, []⟩ := rfl
example : Entry.Composition.Static.lower 4 observingRoute preparedRouteEntry = none := rfl
#guard runEntryPrograms (Entry.lowerPair observingRoute beforeRouteCut preparedRouteEntry input) false 3 ==
  some (99, 99, [99, 33, 2, 3, 55], [99, 33, 2, 3, 55])

-- A different symbolic port also incurs a reader obligation. The
-- concrete checker can accept it at this input, but the static cut refuses.
example : (Discovery.discoverSlot ⟨middleStore, samePortDiamond .onFalse (some rightPort)⟩ .first).map
    ArmOverwrite.readers = some [rightPort] := rfl
example : (Discovery.rewrite ⟨middleStore, samePortDiamond .onFalse (some rightPort)⟩ input).isSome = true := rfl
example : Entry.Composition.Static.lower 4 (samePortDiamond .onFalse (some rightPort)) preparedRouteEntry = none := rfl

open Entry.Composition.Static

-- Start from the two-Store input. The old version two is the singleton
-- seen by the route stage after the first Store is deleted.
example (first : Projection) :
    (Staged.lower (samePortDiamond first) beforeRouteCut input).map
      (fun result => (result.entryOnly.plan.map (·.version), result.entryOnly.entry)) =
      .ok ([1], preparedRouteEntry) := by
  cases first <;> rfl

example (first : Projection) :
    (Staged.lower (samePortDiamond first) beforeRouteCut input).map
      (fun result => match result.route with | .applied _ => true | _ => false) = .ok true := by
  cases first <;> rfl

private def runStaged (graph : Graph args) (entry : Memory.Graph args)
    (valuation : Tuple (Val 4) args) (guard : Bool) (fuel : Nat) :
    Option (Word × Word × List Word × List Word) := do
  let result ← (Staged.lower graph entry valuation).toOption
  runEntryPrograms result.programs guard fuel

/-- info: some (99#64, 7#64, [33#64, 33#64, 2#64, 33#64, 55#64], [33#64, 33#64, 2#64, 33#64, 55#64]) -/
#guard_msgs in
#eval runStaged (samePortDiamond .onFalse) beforeRouteCut input false 3

#guard runStaged (samePortDiamond .onFalse) beforeRouteCut input true 3 == runStaticRoutes input true 3
#guard runStaged (samePortDiamond .onTrue) beforeRouteCut input false 3 == runStaticRoutes input false 3
#guard runStaged (samePortDiamond .onTrue) beforeRouteCut input true 3 == runStaticRoutes input true 3
#guard runStaged (samePortDiamond .onTrue) beforeRouteCut overwriteInput false 3 ==
  runStaticRoutes overwriteInput false 3
#guard runStaged (samePortDiamond .onFalse) beforeRouteCut input true 2 == none

-- One branch observes the remaining Store. The first deletion stays
-- committed, with exactly the entry-only artifact supplying the pair.
example : (Staged.lower observingRoute beforeRouteCut input).map (·.route) = .ok .routesRefused := rfl
example : (Staged.lower observingRoute beforeRouteCut input).map (·.programs) =
    .ok (Entry.lowerPair observingRoute beforeRouteCut preparedRouteEntry input) := rfl
#guard runStaged observingRoute beforeRouteCut input false 3 ==
  some (99, 99, [99, 33, 2, 3, 55], [99, 33, 2, 3, 55])

-- A different symbolic reader also blocks the route stage.
example : (Staged.lower (samePortDiamond .onFalse (some rightPort)) beforeRouteCut input).map (·.route) =
    .ok .routesRefused := rfl

-- A successful entry plan may leave a larger table. This outcome is
-- distinct from a refusal on an eligible singleton shape.
example : (Staged.lower (samePortDiamond .onFalse) inferredEntry input).map (·.route) =
    .ok .entryNotSingleton := rfl
example : (Staged.lower (samePortDiamond .onFalse) inferredEntry input).map (·.programs) =
    .ok (Entry.lowerPair (samePortDiamond .onFalse) inferredEntry inferredFinal input) := rfl
#guard runStaged (samePortDiamond .onFalse) inferredEntry input true 3 ==
  some (33, 33, [11, 11, 99, 33, 55], [11, 11, 99, 33, 55])

private def entryWithLoadedPrefix (rest : Memory.Body args [[.word]] 1) : Memory.Graph args :=
  .load (.latest 0) (.arg rightPort) (.store (.latest 0) (.arg leftPort) loaded rest)

private def retainedFinalPrefix : Memory.Graph args :=
  entryWithLoadedPrefix (.ret (.latest 1) loaded)

private def finalStoreEntry : Memory.Graph args :=
  entryWithLoadedPrefix (.store (.latest 1) (.arg headPort) (.arg entryWord) (.ret (.latest 2) loaded))

private def overwriteThenReadPrefix (word : Port args .word) : Memory.Graph args :=
  .store (.latest 0) (.arg headPort) (.arg word)
    (.load (.latest 1) (.arg leftPort) (.ret (.latest 1) loaded))

private def finalStoreDiamond (first : Projection) : Graph args :=
  { samePortDiamond first with
    arm
      | .onTrue => overwriteThenReadPrefix leftWord
      | .onFalse => lastSideStore.prepend (overwriteThenReadPrefix rightWord) }

example : (Static.Sequence.Search.discover finalStoreEntry (inferContracts finalStoreEntry)).entry =
    finalStoreEntry := rfl
example : Final.cut 2 finalStoreEntry = some (middleStore, retainedFinalPrefix) := rfl
example : Final.cut 1 finalStoreEntry = none := rfl
example : Final.cut 3 finalStoreEntry = none := rfl
example : Final.cut 2
    (entryWithLoadedPrefix (.store (.latest 1) (.arg headPort) loaded (.ret (.latest 2) loaded))) = none := rfl

private def runFinalStore (first : Projection) (valuation : Tuple (Val 4) args)
    (guard : Bool) (fuel : Nat) : Option (Word × Word × List Word × List Word) := do
  let artifacts ← Final.lower 4 (finalStoreDiamond first) finalStoreEntry 2
  runEntryPrograms ⟨valuation, artifacts.original, artifacts.optimized⟩ guard fuel

-- The earlier Load supplies 3 to the retained Store. Each route reads
-- that cell after its overwrite, so the effect remains observable.
/-- info: some (99#64, 7#64, [3#64, 33#64, 3#64, 33#64, 55#64], [3#64, 33#64, 3#64, 33#64, 55#64]) -/
#guard_msgs in
#eval runFinalStore .onFalse input false 3

#guard runFinalStore .onFalse input true 3 == some (99, 7, [3, 11, 3, 3, 55], [3, 11, 3, 3, 55])
#guard runFinalStore .onTrue input false 3 == runFinalStore .onFalse input false 3
#guard runFinalStore .onTrue input true 3 == runFinalStore .onFalse input true 3
#guard runFinalStore .onFalse input false 2 == none

-- The earlier Store can target the nominated cell through another port.
-- Its 3 reaches the optimized entry boundary until the arm writes 33.
#guard runFinalStore .onFalse (chainInput headCell rightCell) false 3 ==
  some (99, 3, [33, 33, 2, 33, 55], [33, 33, 2, 33, 55])

example : Final.lower 4 observingRoute finalStoreEntry 2 = none := rfl
#guard runEntryPrograms (Entry.lowerPair observingRoute finalStoreEntry finalStoreEntry input) false 3 ==
  some (99, 99, [99, 33, 3, 3, 55], [99, 33, 3, 3, 55])

private def residualWithLiveStore : Memory.Graph args := sideStore.prepend middleStore.table

private def stagedFinalEntry : Memory.Graph args :=
  (⟨leftPort, entryWord⟩ : PrefixStore args).prepend residualWithLiveStore

-- The final Store moves from version three to two. The earlier live
-- Store stays, so the residual is still a two-Store table.
example : Final.Staged.find stagedFinalEntry = some 3 := rfl
example : (Final.Staged.lower (finalStoreDiamond .onFalse) stagedFinalEntry input).map
    (fun result => (result.entryOnly.plan.map (·.version), result.entryOnly.entry)) =
      .ok ([1], residualWithLiveStore) := rfl

example (first : Projection) :
    (Final.Staged.lower (finalStoreDiamond first) stagedFinalEntry input).map
      (fun result => match result.route with | .applied version _ => some version | _ => none) = .ok (some 2) := by
  cases first <;> rfl

private def runFinalStaged (graph : Graph args) (entry : Memory.Graph args) (guard : Bool) (fuel : Nat) :
    Option (Word × Word × List Word × List Word) := do
  let result ← (Final.Staged.lower graph entry input).toOption
  runEntryPrograms result.programs guard fuel

-- Both arms return the live prefix Store's 11 after overwriting headCell.
/-- info: some (99#64, 7#64, [11#64, 33#64, 11#64, 33#64, 55#64], [11#64, 33#64, 11#64, 33#64, 55#64]) -/
#guard_msgs in
#eval runFinalStaged (finalStoreDiamond .onFalse) stagedFinalEntry false 3

#guard runFinalStaged (finalStoreDiamond .onFalse) stagedFinalEntry true 3 ==
    some (99, 7, [11, 11, 11, 3, 55], [11, 11, 11, 3, 55])
#guard runFinalStaged (finalStoreDiamond .onTrue) stagedFinalEntry false 3 ==
    runFinalStaged (finalStoreDiamond .onFalse) stagedFinalEntry false 3
#guard runFinalStaged (finalStoreDiamond .onTrue) stagedFinalEntry true 3 ==
    runFinalStaged (finalStoreDiamond .onFalse) stagedFinalEntry true 3
#guard runFinalStaged (finalStoreDiamond .onFalse) stagedFinalEntry false 2 == none

-- One route reads the remaining Store. Keep the actual entry-only pair.
example : (Final.Staged.lower observingRoute stagedFinalEntry input).map (·.route) =
    .ok (.routesRefused 2) := rfl
example : (Final.Staged.lower observingRoute stagedFinalEntry input).map (·.programs) =
    .ok (Entry.lowerPair observingRoute stagedFinalEntry residualWithLiveStore input) := rfl
#guard runFinalStaged observingRoute stagedFinalEntry false 3 ==
    some (99, 99, [99, 33, 11, 3, 55], [99, 33, 11, 3, 55])

-- A trailing Load makes the final Store ineligible. The same first cut
-- succeeds, and its retained program supplies the optimized artifact.
private def residualWithTrailingRead : Memory.Graph args :=
  sideStore.prepend (.store (.latest 0) (.arg headPort) (.arg entryWord)
    (.load (.latest 1) (.arg leftPort) (.ret (.latest 1) loaded)))

private def stagedWithoutFinal : Memory.Graph args :=
  (⟨leftPort, entryWord⟩ : PrefixStore args).prepend residualWithTrailingRead

example : Final.Staged.find residualWithTrailingRead = none := rfl
example : (Final.Staged.lower (finalStoreDiamond .onFalse) stagedWithoutFinal input).map (·.route) =
    .ok .noFinalCandidate := rfl
example : (Final.Staged.lower (finalStoreDiamond .onFalse) stagedWithoutFinal input).map (·.programs) =
    .ok (Entry.lowerPair (finalStoreDiamond .onFalse) stagedWithoutFinal residualWithTrailingRead input) := rfl
#guard runFinalStaged (finalStoreDiamond .onFalse) stagedWithoutFinal false 3 ==
    some (99, 99, [11, 33, 11, 33, 55], [11, 33, 11, 33, 55])

private def tailFacts : Memory.Forwarding.Disjoint.Certificate args := ⟨headPort, [leftPort]⟩

private def retainedTailLoad : Memory.Graph args :=
  sideStore.prepend (.load (.latest 0) (.arg leftPort) (.ret (.latest 0) loaded))

example : Final.LoadTail.cut tailFacts 2 residualWithTrailingRead = some (middleStore, retainedTailLoad) := rfl
example : (Final.LoadTail.lower (finalStoreDiamond .onFalse) stagedWithoutFinal input tailFacts).map
    (fun result => (result.entryOnly.plan.map (·.version), result.routes.isSome)) = .ok ([1], true) := rfl

private def runLoadTail (graph : Graph args) (entry : Memory.Graph args) (valuation : Tuple (Val 4) args)
    (facts : Memory.Forwarding.Disjoint.Certificate args) (guard : Bool) (fuel : Nat) :
    Option (Option Word × Option Word × Option (Word × Word × List Word × List Word)) := do
  let result ← (Final.LoadTail.lower graph entry valuation facts).toOption
  let programs := result.programs
  some (Final.LoadTail.entryWord programs.original programs.input ⟨initial⟩,
    Final.LoadTail.entryWord programs.optimized programs.input ⟨initial⟩, runEntryPrograms programs guard fuel)

-- The emitted entry Return exports the retained Load's 11. Read that
-- actual entry code as well as running the full original and optimized CFGs.
#guard runLoadTail (finalStoreDiamond .onFalse) stagedWithoutFinal input tailFacts false 3 ==
    some (some 11, some 11, some (99, 7, [11, 33, 11, 33, 55], [11, 33, 11, 33, 55]))
#guard runLoadTail (finalStoreDiamond .onTrue) stagedWithoutFinal input tailFacts true 3 ==
    some (some 11, some 11, some (99, 7, [11, 11, 11, 3, 55], [11, 11, 11, 3, 55]))
#guard runLoadTail (finalStoreDiamond .onFalse) stagedWithoutFinal input tailFacts false 2 ==
    some (some 11, some 11, none)

-- Unknown separation and an invocation that aliases both ports leave the
-- exact entry-only program pair, including its earlier accepted deletion.
example : (Final.LoadTail.lower (finalStoreDiamond .onFalse) stagedWithoutFinal input ⟨headPort, []⟩).map (·.programs) =
    .ok (Entry.lowerPair (finalStoreDiamond .onFalse) stagedWithoutFinal residualWithTrailingRead input) := rfl
example : (Final.LoadTail.lower (finalStoreDiamond .onFalse) stagedWithoutFinal (chainInput headCell rightCell)
    tailFacts).map (·.programs) =
    .ok (Entry.lowerPair (finalStoreDiamond .onFalse) stagedWithoutFinal residualWithTrailingRead
      (chainInput headCell rightCell)) := rfl

private def residualWithSameCellLoad : Memory.Graph args :=
  sideStore.prepend (.store (.latest 0) (.arg headPort) (.arg entryWord)
    (.load (.latest 1) (.arg headPort) (.ret (.latest 1) loaded)))

private def beforeSameCellLoad : Memory.Graph args :=
  (⟨leftPort, entryWord⟩ : PrefixStore args).prepend residualWithSameCellLoad

example : Final.LoadTail.cut ⟨headPort, [headPort]⟩ 2 residualWithSameCellLoad = none := rfl
example : (Final.LoadTail.lower (finalStoreDiamond .onFalse) beforeSameCellLoad input tailFacts).map (·.programs) =
    .ok (Entry.lowerPair (finalStoreDiamond .onFalse) beforeSameCellLoad residualWithSameCellLoad input) := rfl
#guard runLoadTail (finalStoreDiamond .onFalse) beforeSameCellLoad input tailFacts false 3 ==
    some (some 99, some 99, some (99, 99, [11, 33, 11, 33, 55], [11, 33, 11, 33, 55]))

private def chainTailFacts : Memory.Forwarding.Disjoint.Certificate args := ⟨headPort, [leftPort, rightPort]⟩

private def twoReadsAfterLastStore (second : Port args .address) (returnFirst : Bool) : Memory.Graph args :=
  let returned : Origin args [[.word], [.word]] .word :=
    if returnFirst then .output (1 : Fin 2) .head else .output (0 : Fin 2) .head
  sideStore.prepend (.store (.latest 0) (.arg headPort) (.arg entryWord)
    (.load (.latest 1) (.arg leftPort)
      (.load (.latest 1) (.arg second) (.ret (.latest 1) returned))))

private def entryWithTrailingReads (second : Port args .address) (returnFirst : Bool) : Memory.Graph args :=
  (⟨leftPort, entryWord⟩ : PrefixStore args).prepend (twoReadsAfterLastStore second returnFirst)

example : (Final.LoadTail.lower (finalStoreDiamond .onFalse) (entryWithTrailingReads rightPort false)
    input chainTailFacts).map (fun result => (result.entryOnly.plan.map (·.version), result.routes.isSome)) =
    .ok ([1], true) := rfl

-- Return can observe either Load. Both original and optimized emitted
-- entry bodies preserve the first 11 and the second 3.
#guard runLoadTail (finalStoreDiamond .onFalse) (entryWithTrailingReads rightPort true)
    input chainTailFacts false 3 ==
    some (some 11, some 11, some (99, 7, [11, 33, 11, 33, 55], [11, 33, 11, 33, 55]))
#guard runLoadTail (finalStoreDiamond .onTrue) (entryWithTrailingReads rightPort false)
    input chainTailFacts true 3 ==
    some (some 3, some 3, some (99, 7, [11, 11, 11, 3, 55], [11, 11, 11, 3, 55]))
#guard runLoadTail (finalStoreDiamond .onFalse) (entryWithTrailingReads rightPort false)
    input chainTailFacts false 2 == some (some 3, some 3, none)

-- The first reader is covered. A later same-port read or missing fact
-- refuses the cut and keeps the precise entry-only emitted pair.
example : Final.LoadTail.cut chainTailFacts 2 (twoReadsAfterLastStore headPort false) = none := rfl
example : Final.LoadTail.cut tailFacts 2 (twoReadsAfterLastStore rightPort false) = none := rfl
example : (Final.LoadTail.lower (finalStoreDiamond .onFalse) (entryWithTrailingReads headPort false)
    input chainTailFacts).map (·.programs) =
    .ok (Entry.lowerPair (finalStoreDiamond .onFalse) (entryWithTrailingReads headPort false)
      (twoReadsAfterLastStore headPort false) input) := rfl
#guard runLoadTail (finalStoreDiamond .onFalse) (entryWithTrailingReads headPort false)
    input chainTailFacts false 3 ==
    some (some 99, some 99, some (99, 99, [11, 33, 11, 33, 55], [11, 33, 11, 33, 55]))

-- A later symbolic reader may alias at a concrete invocation as well.
example : (Final.LoadTail.lower (finalStoreDiamond .onFalse) (entryWithTrailingReads rightPort false)
    overwriteInput chainTailFacts).map (·.programs) =
    .ok (Entry.lowerPair (finalStoreDiamond .onFalse) (entryWithTrailingReads rightPort false)
      (twoReadsAfterLastStore rightPort false) overwriteInput) := rfl

private def disjointStoreTailFacts : Memory.Forwarding.Disjoint.Certificate args := ⟨headPort, [rightPort]⟩

private def residualWithDisjointStore : Memory.Graph args :=
  sideStore.prepend (.load (.latest 0) (.arg leftPort)
    (.store (.latest 0) (.arg headPort) (.arg entryWord)
      (.store (.latest 1) (.arg rightPort) loaded
        (.load (.latest 2) (.arg rightPort) (.ret (.latest 2) (.output (0 : Fin 2) .head))))))

private def keptDisjointStore : Memory.Graph args :=
  sideStore.prepend (.load (.latest 0) (.arg leftPort)
    (.store (.latest 0) (.arg rightPort) loaded
      (.load (.latest 1) (.arg rightPort) (.ret (.latest 1) (.output (0 : Fin 2) .head)))))

private def entryWithDisjointStore : Memory.Graph args :=
  (⟨leftPort, entryWord⟩ : PrefixStore args).prepend residualWithDisjointStore

private def suffixStoreDiamond (first : Projection) : Graph args :=
  let overwrite (word : Port args .word) : Memory.Graph args :=
    .store (.latest 0) (.arg headPort) (.arg word)
      (.load (.latest 1) (.arg rightPort) (.ret (.latest 1) loaded))
  { samePortDiamond first with
    arm
      | .onTrue => overwrite leftWord
      | .onFalse => overwrite rightWord }

-- The first pass removes version one. The candidate is now version
-- two, after a Load that feeds the exact retained Store data wire.
example : (StoreTail.lower (suffixStoreDiamond .onFalse) entryWithDisjointStore 2 input
    disjointStoreTailFacts).map (fun result => (result.entryOnly.plan.map (·.version), result.entryOnly.entry)) =
      .ok ([1], residualWithDisjointStore) := rfl
example : Entry.Composition.Retained.Load.cut 2 input residualWithDisjointStore = none := rfl
example : StoreTail.cut disjointStoreTailFacts 2 residualWithDisjointStore =
    some (middleStore, keptDisjointStore) := rfl
example : (StoreTail.lower (suffixStoreDiamond .onFalse) entryWithDisjointStore 2 input
    disjointStoreTailFacts).map (·.routes.isSome) = .ok true := rfl

private def runStoreTail (graph : Graph args) (valuation : Tuple (Val 4) args)
    (facts : Memory.Forwarding.Disjoint.Certificate args) (guard : Bool) (fuel : Nat) :
    Option (Word × Word × List Word × List Word) := do
  let result ← (StoreTail.lower graph entryWithDisjointStore 2 valuation facts).toOption
  runEntryPrograms result.programs guard fuel

-- Both arms observe the retained Store's 11 after their overwrite.
/-- info: some (99#64, 7#64, [11#64, 33#64, 11#64, 11#64, 55#64], [11#64, 33#64, 11#64, 11#64, 55#64]) -/
#guard_msgs in
#eval runStoreTail (suffixStoreDiamond .onFalse) input disjointStoreTailFacts false 3

#guard runStoreTail (suffixStoreDiamond .onTrue) input disjointStoreTailFacts true 3 ==
    some (99, 7, [11, 11, 11, 11, 55], [11, 11, 11, 11, 55])
#guard runStoreTail (suffixStoreDiamond .onFalse) input disjointStoreTailFacts false 2 == none

-- Missing coverage and aliasing at the invocation keep the exact first
-- optimized artifact. An observing branch refuses the route cut as well.
example : StoreTail.cut ⟨headPort, []⟩ 2 residualWithDisjointStore = none := rfl
example : (StoreTail.lower (suffixStoreDiamond .onFalse) entryWithDisjointStore 2 input
    ⟨headPort, []⟩).map (·.programs) =
    .ok (Entry.lowerPair (suffixStoreDiamond .onFalse) entryWithDisjointStore residualWithDisjointStore input) := rfl
example : (StoreTail.lower (suffixStoreDiamond .onFalse) entryWithDisjointStore 2 overwriteInput
    disjointStoreTailFacts).map (·.programs) =
    .ok (Entry.lowerPair (suffixStoreDiamond .onFalse) entryWithDisjointStore
      residualWithDisjointStore overwriteInput) := rfl
#guard runStoreTail (suffixStoreDiamond .onFalse) overwriteInput disjointStoreTailFacts false 3 ==
    some (11, 11, [33, 33, 11, 3, 55], [33, 33, 11, 3, 55])
example : (StoreTail.lower observingRoute entryWithDisjointStore 2 input disjointStoreTailFacts).map
    (·.programs) = .ok (Entry.lowerPair observingRoute entryWithDisjointStore residualWithDisjointStore input) := rfl

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore
