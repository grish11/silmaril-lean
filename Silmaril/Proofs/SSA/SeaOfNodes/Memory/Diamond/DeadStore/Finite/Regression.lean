module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.FinalEntry.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.Thms

meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.FinalEntry.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite

open RVSDG (Origin Port Tuple)
open Quads.CFG (Predecessors)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

private abbrev Args : List ValueSort := [.address, .address, .word, .word, .word]

private def headPort : Port Args .address := .head
private def sidePort : Port Args .address := .tail .head
private def entryWord : Port Args .word := .tail (.tail .head)
private def firstWord : Port Args .word := .tail (.tail (.tail .head))
private def middleWord : Port Args .word := .tail (.tail (.tail (.tail .head)))
private def loaded : Origin Args [[.word]] .word := .output 0 .head

-- The first two paths finish at the same named predecessor. Their
-- complete reaching paths and their overwrite versions differ.
private def preds : Predecessors 2 := ⟨0, [0, 1]⟩
private def reversed : Predecessors 2 := ⟨1, [0, 0]⟩

private def reverseOrder : Occurrence reversed ≃ Occurrence preds :=
  ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩

example : List.ofFn preds.get = [0, 0, 1] := rfl
example : List.ofFn reversed.get = List.ofFn (fun i => preds.get (reverseOrder i)) := rfl

private def shared : PrefixStore Args := ⟨headPort, entryWord⟩

private def first : Memory.Graph Args :=
  .load (.latest 0) (.arg sidePort)
    (.store (.latest 0) (.arg headPort) (.arg firstWord) (.ret (.latest 1) loaded))

private def middle (reader : Port Args .address) : Memory.Graph Args :=
  .load (.latest 0) (.arg reader)
    (.store (.latest 0) (.arg sidePort) (.arg middleWord)
      (.store (.latest 1) (.arg headPort) (.arg middleWord) (.ret (.latest 2) loaded)))

private def last : Memory.Graph Args :=
  .store (.latest 0) (.arg headPort) (.arg entryWord)
    (.load (.latest 1) (.arg headPort) (.ret (.latest 1) loaded))

private def arms (middleReader : Port Args .address) (arrival : Occurrence preds) : Memory.Graph Args :=
  match arrival.val with
  | 0 => first
  | 1 => middle middleReader
  | _ => last

private def witnesses (arrival : Occurrence preds) : ArmOverwrite Args :=
  match arrival.val with
  | 0 => ⟨1, [sidePort]⟩
  | 1 => ⟨2, [sidePort]⟩
  | _ => ⟨1, []⟩

private def input : Tuple (Val 3) Args :=
  .cons (0 : Address 3) (.cons (1 : Address 3)
    (.cons (99 : Word) (.cons (11 : Word) (.cons (22 : Word) .nil))))

private def initial : Buffer 3 :=
  ⟨fun i => if i = 0 then 7 else if i = 1 then 3 else 55⟩

private def edited : Bank Args preds := #v[first, middle sidePort, last]

private theorem accepted : check preds shared (arms sidePort) witnesses input = some edited := by
  apply check_eq_some_iff.mpr
  intro arrival
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun j => ?_) i) arrival
  · rfl
  · rfl
  · rw [Fin.eq_zero j]
    rfl

example : check reversed shared (fun i => arms sidePort (reverseOrder i)) (fun i => witnesses (reverseOrder i))
    input = some (Vector.ofFn fun i => edited[(reverseOrder i).val]) :=
  check_reindex reverseOrder accepted

-- Only occurrence one observes the old cell. Occurrence zero has the
-- same predecessor identifier and still checks successfully.
example : rewriteArm shared (arms headPort 0) (witnesses 0) input = some first := rfl
example : rewriteArm shared (arms headPort 1) (witnesses 1) input = none := rfl
example : rewriteArm shared (arms headPort 2) (witnesses 2) input = some last := rfl
example : check preds shared (arms headPort) witnesses input = none :=
  check_eq_none_iff.mpr ⟨1, rfl⟩
#guard (check preds shared (arms headPort) witnesses input).isNone

#guard Memory.DeadStore.readAt (shared.prepend (arms headPort 1)) 0 input PUnit.unit initial.cell == some 99
#guard Memory.DeadStore.readAt (arms headPort 1) 0 input PUnit.unit initial.cell == some 7

private def readback (result : Word × Buffer 3) : List Nat :=
  result.1.toNat :: List.ofFn (fun i => (result.2.cell i).toNat)

private def runBank (order : Predecessors 2) (arm : Occurrence order → Memory.Graph Args)
    (candidate : Candidate Args order) : Option (List (List Nat × List Nat)) := do
  let result ← check order shared arm candidate input
  pure (List.ofFn fun i =>
    (readback (observe (shared.prepend (arm i)) input initial), readback (observe result[i.val] input initial)))

/-- info: some [[3, 11, 3, 55], [3, 22, 22, 55], [99, 99, 3, 55]] -/
#guard_msgs in
#eval (runBank preds (arms sidePort) witnesses).map (List.map Prod.snd)

#guard runBank preds (arms sidePort) witnesses ==
  some [([3, 11, 3, 55], [3, 11, 3, 55]), ([3, 22, 22, 55], [3, 22, 22, 55]), ([99, 99, 3, 55], [99, 99, 3, 55])]

#guard runBank reversed (fun i => arms sidePort (reverseOrder i)) (fun i => witnesses (reverseOrder i)) ==
  (runBank preds (arms sidePort) witnesses).map List.reverse

-- The shared suffix writes the selected word to the side cell and then
-- returns the selected path's new head cell.
private def suffix : Memory.Graph (.word :: Args) :=
  .store (.latest 0) (.arg (.tail sidePort)) (.arg .head)
    (.load (.latest 1) (.arg (.tail headPort)) (.ret (.latest 1) (.output 0 .head)))

private def inspectSwitch {order : Predecessors 2} (program : MemRef.CF.Program 3 Args order)
    (arrival : Occurrence order) (fuel : Nat) : Option (Nat × List Nat × List Nat) := do
  let entered := MemRef.CF.entryTransition program input arrival initial
  let .inl ⟨.arm slot, _⟩ := entered.1 | none
  let joined := MemRef.CF.armTransition program input slot entered.2
  let .inl ⟨.join, words⟩ := joined.1 | none
  let final ← MemRef.CF.run program input arrival fuel initial
  some (slot.val, readback (words.get .here, joined.2), readback final)

private def compareSwitch {order : Predecessors 2} (emitted : Option (MemRef.CF.Programs 3 Args order))
    (arrival : Occurrence order) (fuel : Nat) : Option (Nat × List Nat × List Nat) := do
  let programs ← emitted
  let before ← inspectSwitch programs.original arrival fuel
  let after ← inspectSwitch programs.optimized arrival fuel
  if before == after then some after else none

private def runSwitch (order : Predecessors 2) (fits : MemRef.CF.Fits order)
    (arm : Occurrence order → Memory.Graph Args) (candidate : Candidate Args order)
    (arrival : Occurrence order) (fuel : Nat) : Option (Nat × List Nat × List Nat) :=
  compareSwitch (MemRef.CF.lower order fits shared arm candidate suffix input) arrival fuel

private theorem fits : MemRef.CF.Fits preds := by decide
private theorem reversedFits : MemRef.CF.Fits reversed := by decide

private def originalSelections : List (Option (Nat × List Nat × List Nat)) :=
  List.ofFn fun i => runSwitch preds fits (arms sidePort) witnesses i 3

-- Each row records the actual switch slot, the join packet and the
-- final return. Both lists start with a word followed by all cells.
#guard originalSelections ==
  [some (0, [3, 11, 3, 55], [11, 11, 3, 55]),
   some (1, [3, 22, 22, 55], [22, 22, 3, 55]),
   some (2, [99, 99, 3, 55], [99, 99, 99, 55])]

private def transportedSelections : List (Option (Nat × List Nat × List Nat)) :=
  List.ofFn fun (original : Occurrence preds) => do
    let arrival := reverseOrder.symm original
    let (slot, packet, final) ← runSwitch reversed reversedFits
      (fun i => arms sidePort (reverseOrder i)) (fun i => witnesses (reverseOrder i)) arrival 3
    if slot == arrival.val then some (original.val, packet, final) else none

#guard transportedSelections == originalSelections
#guard (runSwitch preds fits (arms sidePort) witnesses 0 2).isNone
#guard (MemRef.CF.lower preds fits shared (arms headPort) witnesses suffix input).isNone
example : MemRef.CF.lower preds fits shared (arms headPort) witnesses suffix input = none :=
  MemRef.CF.lower_eq_none_iff.mpr ⟨1, rfl⟩

private def entryPrefix (lastWriter : Port Args .address) (tail : Memory.Body Args [[.word]] 2) :
    Memory.Graph Args :=
  .load (.latest 0) (.arg headPort)
    (.store (.latest 0) (.arg sidePort) loaded
      (.store (.latest 1) (.arg lastWriter) (.arg firstWord) tail))

private def sourceEntry (lastWriter : Port Args .address := headPort) : Memory.Graph Args :=
  entryPrefix lastWriter (.store (.latest 2) (.arg headPort) (.arg entryWord) (.ret (.latest 3) loaded))

private def retainedEntry : Memory.Graph Args := entryPrefix headPort (.ret (.latest 2) loaded)

private theorem cutAccepted :
    Entry.Composition.Static.Final.cut 3 sourceEntry = some (shared, retainedEntry) := rfl

private def entryPrograms :=
  MemRef.CF.FinalEntry.lower preds fits sourceEntry 3 (arms sidePort) witnesses suffix input

private def entryBuffers (programs : MemRef.CF.Programs 3 Args preds) : List Nat × List Nat :=
  let before := MemRef.CF.entryTransition programs.original programs.input 1 initial
  let after := MemRef.CF.entryTransition programs.optimized programs.input 1 initial
  (List.ofFn (fun i => (before.2.cell i).toNat), List.ofFn (fun i => (after.2.cell i).toNat))

-- The side Store still uses the original Load. The retained write to
-- the head is observable on the edge to the switch arm.
#guard entryPrograms.map entryBuffers == some ([99, 7, 55], [11, 7, 55])
#guard readback (observe sourceEntry input initial) == [7, 99, 7, 55]
#guard readback (observe retainedEntry input initial) == [7, 11, 7, 55]

private def runEntrySwitch (arrival : Occurrence preds) (fuel : Nat) :
    Option (Nat × List Nat × List Nat) :=
  compareSwitch entryPrograms arrival fuel

#guard (List.ofFn fun i => runEntrySwitch i 3) ==
  [some (0, [7, 11, 7, 55], [11, 11, 7, 55]),
   some (1, [7, 22, 22, 55], [22, 22, 7, 55]),
   some (2, [99, 99, 7, 55], [99, 99, 99, 55])]
#guard (runEntrySwitch 1 2).isNone

#guard Memory.DeadStore.readAt (arms headPort 1) 0 input PUnit.unit
    (sourceEntry.denote input initial.cell).2 == some 99
#guard Memory.DeadStore.readAt (arms headPort 1) 0 input PUnit.unit
    (retainedEntry.denote input initial.cell).2 == some 11
#guard (MemRef.CF.FinalEntry.lower preds fits sourceEntry 3 (arms headPort) witnesses suffix input).isNone
example : MemRef.CF.FinalEntry.lower preds fits sourceEntry 3 (arms headPort) witnesses suffix input = none :=
  (MemRef.CF.FinalEntry.lower_eq_none_iff cutAccepted).mpr ⟨1, rfl⟩
#guard (MemRef.CF.FinalEntry.lower preds fits sourceEntry 2 (arms sidePort) witnesses suffix input).isNone

-- The last retained Store can also reach the head through a distinct
-- address port. These arms overwrite before doing any read.
private def aliasInput : Tuple (Val 3) Args :=
  .cons (0 : Address 3) (.cons (0 : Address 3)
    (.cons (99 : Word) (.cons (11 : Word) (.cons (22 : Word) .nil))))

#guard (MemRef.CF.FinalEntry.lower preds fits (sourceEntry sidePort) 3 (fun _ => last)
    (fun _ => ⟨1, []⟩) suffix aliasInput).map entryBuffers == some ([99, 3, 55], [11, 3, 55])

private def tailPrefix (tail : Memory.Body Args [[.word]] 2) : Memory.Graph Args :=
  .load (.latest 0) (.arg sidePort)
    (.store (.latest 0) (.arg headPort) loaded
      (.store (.latest 1) (.arg sidePort) (.arg firstWord) tail))

-- Return keeps the first trailing Load, whose value differs from the
-- pre-Store Load's value.
private def trailingReads (version : Nat) : Memory.Body Args [[.word]] version :=
  .load (.latest version) (.arg sidePort)
    (.load (.latest version) (.arg sidePort) (.ret (.latest version) (.output (1 : Fin 3) .head)))

private def tailEntry : Memory.Graph Args :=
  tailPrefix (.store (.latest 2) (.arg headPort) (.arg entryWord) (trailingReads 3))

private def keptTailEntry : Memory.Graph Args := tailPrefix (trailingReads 2)

private def tailFacts : Memory.Forwarding.Disjoint.Certificate Args := ⟨headPort, [sidePort]⟩

private theorem tailCutAccepted :
    MemRef.CF.LoadTail.cut tailFacts 3 tailEntry input = some (shared, keptTailEntry) := rfl

private def tailPrograms :=
  MemRef.CF.LoadTail.lower preds fits tailEntry 3 (arms sidePort) witnesses suffix input tailFacts

private def emittedEntryWord (program : MemRef.CF.Program 3 Args preds) : Option Nat :=
  program.entry.memory.map fun code => (Discovery.MemRef.CF.runWord code input initial).1.toNat

#guard tailPrograms.map entryBuffers == some ([99, 11, 55], [3, 11, 55])
#guard (tailPrograms.map fun p => (emittedEntryWord p.original, emittedEntryWord p.optimized)) ==
  some (some 11, some 11)

private def runTailSwitch (arrival : Occurrence preds) (fuel : Nat) :
    Option (Nat × List Nat × List Nat) :=
  compareSwitch tailPrograms arrival fuel

#guard (List.ofFn fun i => runTailSwitch i 3) ==
  [some (0, [11, 11, 11, 55], [11, 11, 11, 55]),
   some (1, [11, 22, 22, 55], [22, 22, 11, 55]),
   some (2, [99, 99, 11, 55], [99, 99, 99, 55])]
#guard (runTailSwitch 1 2).isNone

-- A concrete alias rejects even when every route overwrites first.
#guard (check preds shared (fun _ => last) (fun _ => ⟨1, []⟩) aliasInput).isSome
#guard (MemRef.CF.LoadTail.lower preds fits tailEntry 3 (fun _ => last)
    (fun _ => ⟨1, []⟩) suffix aliasInput tailFacts).isNone
#guard (MemRef.CF.LoadTail.lower preds fits tailEntry 3 (arms sidePort) witnesses suffix input
    ⟨headPort, []⟩).isNone
#guard (MemRef.CF.LoadTail.lower preds fits sourceEntry 3 (arms sidePort) witnesses suffix input tailFacts).isNone

example : MemRef.CF.LoadTail.lower preds fits tailEntry 3 (arms headPort) witnesses suffix input tailFacts = none :=
  (MemRef.CF.LoadTail.lower_eq_none_iff tailCutAccepted).mpr ⟨1, rfl⟩
#guard (MemRef.CF.LoadTail.lower preds fits tailEntry 3 (arms headPort) witnesses suffix input tailFacts).isNone

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite
