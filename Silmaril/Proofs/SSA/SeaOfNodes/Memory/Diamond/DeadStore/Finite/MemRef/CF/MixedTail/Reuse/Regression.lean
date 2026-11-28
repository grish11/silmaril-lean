module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Diagnostic.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Diagnostic.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Replay.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse

open RVSDG (Port Tuple)
open Quads.CFG (Predecessors)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

private abbrev Args : List ValueSort := [.address, .address, .address, .address, .word, .word, .word]

private def target : Port Args .address := .head
private def reader : Port Args .address := .tail .head
private def sink : Port Args .address := .tail (.tail .head)
private def observer : Port Args .address := .tail (.tail (.tail .head))
private def firstWord : Port Args .word := .tail (.tail (.tail (.tail .head)))
private def secondWord : Port Args .word := .tail (.tail (.tail (.tail (.tail .head))))
private def thirdWord : Port Args .word := .tail (.tail (.tail (.tail (.tail (.tail .head)))))

private def oldInput : Tuple (Val 5) Args :=
  .cons (0 : Address 5) (.cons (1 : Address 5) (.cons (2 : Address 5) (.cons (3 : Address 5)
    (.cons (11 : Word) (.cons (22 : Word) (.cons (99 : Word) .nil))))))

private def newInputAt (observed : Address 5) : Tuple (Val 5) Args :=
  .cons (1 : Address 5) (.cons (3 : Address 5) (.cons (0 : Address 5) (.cons observed
    (.cons (101 : Word) (.cons (202 : Word) (.cons (303 : Word) .nil))))))

private def newInput := newInputAt 2
private def aliasInput := newInputAt 1

private def initial : Buffer 5 :=
  ⟨fun cell => if cell = 0 then 70 else if cell = 1 then 80 else if cell = 2 then 90
    else if cell = 3 then 100 else 110⟩

private def entry : Memory.Graph Args :=
  .load (.latest 0) (.arg sink)
    (.store (.latest 0) (.arg target) (.output 0 .head)
      (.load (.latest 1) (.arg reader)
        (.store (.latest 1) (.arg sink) (.output 0 .head)
          (.load (.latest 2) (.arg sink) (.ret (.latest 2) (.output 0 .head))))))

private def preds : Predecessors 2 := ⟨0, [0, 1]⟩
private theorem fits : Fits preds := by decide

example : List.ofFn preds.get = [0, 0, 1] := rfl

private def arms (i : Occurrence preds) : Memory.Graph Args :=
  match i.val with
  | 0 => .load (.latest 0) (.arg observer)
      (.store (.latest 0) (.arg target) (.arg firstWord) (.ret (.latest 1) (.output 0 .head)))
  | 1 => .store (.latest 0) (.arg reader) (.arg secondWord)
      (.load (.latest 1) (.arg sink)
        (.store (.latest 1) (.arg target) (.arg secondWord) (.ret (.latest 2) (.output 0 .head))))
  | _ => .store (.latest 0) (.arg target) (.arg thirdWord)
      (.load (.latest 1) (.arg sink) (.ret (.latest 1) (.output 0 .head)))

private def suffix : Memory.Graph (.word :: Args) :=
  .store (.latest 0) (.arg (.tail reader)) (.arg .head)
    (.load (.latest 1) (.arg (.tail target)) (.ret (.latest 1) (.output 0 .head)))

private def admitted := MixedTail.lower fits arms suffix oldInput entry
private def reused := admitted.bind (fun stage => reuse stage newInput)

#guard admitted.map MixedTail.Result.version == some 1
#guard (admitted.map fun stage => (contractOf stage).entry.disjoint.writers.map Port.index) == some [1, 2, 2]
#guard (admitted.map fun stage =>
  (contractOf stage).arms.toList.map (fun facts => facts.disjoint.writers.map Port.index)) == some [[3], [2], []]
#guard (admitted.map fun stage => (contractOf stage).check oldInput && (contractOf stage).check newInput) == some true

example {stage next : MixedTail.Result 5 Args preds}
    (accepted : admitted = some stage) (rebound : reuse stage newInput = some next) :
    next.emission.programs.input = newInput ∧
      next.emission.programs.original = stage.emission.programs.original ∧
      next.emission.programs.optimized = stage.emission.programs.optimized :=
  (reuse_checked (fits := fits) (arm := arms) (suffix := suffix) (entry := entry) (oldInput := oldInput)
    accepted rebound).2

private def contents (buffer : Buffer 5) : List Nat := List.ofFn fun i => (buffer.cell i).toNat

#guard (reused.map fun stage =>
  let programs := stage.emission.programs
  [programs.original, programs.optimized].map fun program =>
    contents (entryTransition program programs.input 1 initial).2) ==
  some [[100, 70, 90, 100, 110], [100, 80, 90, 100, 110]]

private def snapshot (program : Program 5 Args preds) (input : Tuple (Val 5) Args) (arrival : Occurrence preds) :
    Option (Nat × List Nat × List Nat) := do
  let entered := entryTransition program input arrival initial
  let .inl ⟨.arm slot, _⟩ := entered.1 | none
  let joined := armTransition program input slot entered.2
  let .inl ⟨.join, words⟩ := joined.1 | none
  let final ← run program input arrival 3 initial
  some (slot.val, (words.get .here).toNat :: contents joined.2, final.1.toNat :: contents final.2)

private def expected : List (Option (Nat × List Nat × List Nat)) :=
  [some (0, [90, 100, 101, 90, 100, 110], [101, 100, 101, 90, 90, 110]),
   some (1, [100, 100, 202, 90, 202, 110], [202, 100, 202, 90, 100, 110]),
   some (2, [100, 100, 303, 90, 100, 110], [303, 100, 303, 90, 100, 110])]

#guard (reused.map fun stage =>
  let programs := stage.emission.programs
  [programs.original, programs.optimized].map fun program =>
    List.ofFn fun i => snapshot program programs.input i) == some [expected, expected]

#guard (reused.map fun stage =>
  let programs := stage.emission.programs
  [programs.original, programs.optimized].all fun program => (run program programs.input 1 2 initial).isNone) ==
  some true

private def probes (graph : Memory.Graph Args) (input : Tuple (Val 5) Args) : List (Option Nat) :=
  List.ofFn fun (i : Fin 4) => (Memory.DeadStore.throughLoad graph i.val).map fun block =>
    (observe block input initial).1.toNat

#guard probes entry newInput == [some 70, some 100, some 100, none]
#guard (reused.map fun stage => probes stage.emission.edit.retained stage.emission.programs.input) ==
  some (probes entry newInput)

-- Only the first occurrence's reader aliases the cut cell here. The
-- mixed entry and both other occurrence records still validate.
#guard (admitted.map fun stage =>
  let facts := contractOf stage
  (facts.entry.check aliasInput, facts.arms.toList.map (fun arm => arm.check aliasInput))) ==
  some (true, [false, true, true])
#guard (admitted.bind fun stage => reuse stage aliasInput).isNone

-- Only occurrence zero has the failing read. Occurrence one shares its predecessor ID.
private def recorded := Replay.lower preds fits entry arms suffix oldInput [.expect 1]
private def diagnosed := Chain.Diagnostic.lower recorded entry aliasInput

#guard diagnosed.checkedPrefix.replay.deleted == 0 && diagnosed.checkedPrefix.pending.length == 1
#guard (diagnosed.refusal.map fun report =>
  let site := match report.conflict.site with
    | .entry _ => none
    | .arm occurrence index => some (occurrence.val, index)
  (report.stageIndex, report.version, report.store.index, site, report.conflict.port.index,
    report.conflict.address.val)) == some (0, 1, 0, some (0, 0), 3, 1)

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse
