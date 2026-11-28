module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Diagnostic.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Replay.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Thms
import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Recovery.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Recovery.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Diagnostic.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Replay.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Reuse.Chain.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Replay

open RVSDG (Port Tuple)
open Quads.CFG (Predecessors)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)
open Memory.DeadStore.Search.Selection (storeVersions)

private abbrev Args : List ValueSort := [.address, .address, .address, .address, .address, .word, .word, .word]

private def left : Port Args .address := .head
private def right : Port Args .address := .tail .head
private def side : Port Args .address := .tail (.tail .head)
private def reader : Port Args .address := .tail (.tail (.tail .head))
private def sink : Port Args .address := .tail (.tail (.tail (.tail .head)))
private def firstWord : Port Args .word := .tail (.tail (.tail (.tail (.tail .head))))
private def secondWord : Port Args .word := .tail (.tail (.tail (.tail (.tail (.tail .head)))))
private def thirdWord : Port Args .word := .tail (.tail (.tail (.tail (.tail (.tail (.tail .head))))))

private def inputs (readCell : Address 5) : Tuple (Val 5) Args :=
  .cons (0 : Address 5) (.cons (1 : Address 5) (.cons (2 : Address 5) (.cons readCell (.cons (3 : Address 5)
    (.cons (11 : Word) (.cons (22 : Word) (.cons (99 : Word) .nil)))))))

private def input := inputs 2
private def aliasInput := inputs 1

private def initial : Buffer 5 :=
  ⟨fun cell => if cell = 0 then 7 else if cell = 1 then 8 else if cell = 2 then 5 else if cell = 3 then 3 else 55⟩

-- This Load supplies the retained Store. The next Load reads its published cell.
private def logging (version : Nat) : Memory.Body Args [[.word], [.word]] version :=
  .load (.latest version) (.arg reader)
    (.store (.latest version) (.arg sink) (.output 0 .head)
      (.load (.latest (version + 1)) (.arg sink) (.ret (.latest (version + 1)) (.output 0 .head))))

private def entry : Memory.Graph Args :=
  .load (.latest 0) (.arg sink)
    (.store (.latest 0) (.arg left) (.output 0 .head)
      (.load (.latest 1) (.arg side)
        (.store (.latest 1) (.arg right) (.output 0 .head) (logging 2))))

private def withoutBoth : Memory.Graph Args :=
  .load (.latest 0) (.arg sink) (.load (.latest 0) (.arg side) (logging 0))

private def preds : Predecessors 2 := ⟨0, [0, 1]⟩
private theorem fits : Fits preds := by decide

example : List.ofFn preds.get = [0, 0, 1] := rfl

private def arms (i : Occurrence preds) : Memory.Graph Args :=
  match i.val with
  | 0 => .store (.latest 0) (.arg left) (.arg firstWord)
      (.load (.latest 1) (.arg sink)
        (.store (.latest 1) (.arg right) (.arg firstWord) (.ret (.latest 2) (.output 0 .head))))
  | 1 => .store (.latest 0) (.arg right) (.arg secondWord)
      (.load (.latest 1) (.arg sink)
        (.store (.latest 1) (.arg left) (.arg secondWord) (.ret (.latest 2) (.output 0 .head))))
  | _ => .store (.latest 0) (.arg left) (.arg thirdWord)
      (.store (.latest 1) (.arg right) (.arg thirdWord)
        (.load (.latest 2) (.arg sink) (.ret (.latest 2) (.output 0 .head))))

private def suffix : Memory.Graph (.word :: Args) :=
  .store (.latest 0) (.arg (.tail side)) (.arg .head)
    (.load (.latest 1) (.arg (.tail right)) (.ret (.latest 1) (.output 0 .head)))

private def success := discover preds fits entry arms suffix input
private def plan : List Request := [.expect 1, .expect 1]
private def blocked := lower preds fits entry arms suffix aliasInput plan

#guard success.admitted.map MixedTail.Result.version == [1, 1]
#guard success.admitted.map (fun stage => (occurrenceRecords stage).toList.map ArmOverwrite.storeVersion) ==
  [[1, 2, 1], [2, 1, 2]]
#guard storeVersions success.retained == [1]
#guard (MixedTail.lower fits arms suffix input success.retained).isNone

example : lower preds fits entry arms suffix input (success.admitted.map fun stage => .expect stage.version) =
    { success with remaining := [] } :=
  lower_replayed (requests := List.replicate 3 .discover)

private def contents (buffer : Buffer 5) : List Nat := List.ofFn fun i => (buffer.cell i).toNat

private def artifacts (result : Result 5 Args preds) : List (Program 5 Args preds) :=
  result.programs.original :: result.admitted.map (fun stage => stage.emission.programs.optimized)

private def entryBuffers (result : Result 5 Args preds) : List (List Nat) :=
  (artifacts result).map fun program => contents (entryTransition program result.programs.input 1 initial).2

#guard entryBuffers success == [[3, 5, 5, 5, 55], [7, 5, 5, 5, 55], [7, 8, 5, 5, 55]]
#guard entryBuffers (lower preds fits entry arms suffix input plan) == entryBuffers success
#guard contents (success.restoreEntry initial) == [3, 5, 5, 5, 55]

private def snapshot (program : Program 5 Args preds) (values : Tuple (Val 5) Args)
    (arrival : Occurrence preds) : Option (Nat × List Nat × List Nat) := do
  let entered := entryTransition program values arrival initial
  let .inl ⟨.arm slot, _⟩ := entered.1 | none
  let joined := armTransition program values slot entered.2
  let .inl ⟨.join, words⟩ := joined.1 | none
  let final ← run program values arrival 3 initial
  some (slot.val, (words.get .here).toNat :: contents joined.2, final.1.toNat :: contents final.2)

private def snapshots (result : Result 5 Args preds) : List (List (Option (Nat × List Nat × List Nat))) :=
  List.ofFn fun i => (artifacts result).map fun artifact => snapshot artifact result.programs.input i

private def expected : List (Option (Nat × List Nat × List Nat)) :=
  [some (0, [5, 11, 11, 5, 5, 55], [11, 11, 11, 5, 5, 55]),
   some (1, [5, 22, 22, 5, 5, 55], [22, 22, 22, 5, 5, 55]),
   some (2, [5, 99, 99, 5, 5, 55], [99, 99, 99, 5, 5, 55])]

#guard snapshots success == expected.map (List.replicate 3)
#guard (artifacts success).all (fun program => (run program input 1 2 initial).isNone)

private def probes (graph : Memory.Graph Args) (values : Tuple (Val 5) Args) : List (Option Nat) :=
  List.ofFn fun (index : Fin 5) => (Memory.DeadStore.throughLoad graph index.val).map fun block =>
    (observe block values initial).1.toNat

#guard probes entry input == [some 3, some 5, some 5, some 5, none]
#guard success.admitted.all (fun stage => probes stage.emission.edit.retained input == probes entry input)

-- The retained reader aliases the right cell at this input. Cutting the
-- left Store is safe, and replay refuses the re-numbered right Store.
#guard blocked.deleted == 1 && blocked.remaining.length == 1
#guard storeVersions blocked.retained == [1, 2]
#guard (MixedTail.tryVersion fits arms suffix aliasInput blocked.retained 1).isNone
#guard entryBuffers blocked == [[3, 5, 5, 5, 55], [7, 5, 5, 5, 55]]
#guard contents (entryTransition blocked.programs.optimized blocked.programs.input 1 initial).2 ==
  [7, 5, 5, 5, 55]
#guard snapshots blocked == expected.map (List.replicate 2)
#guard contents (blocked.restoreEntry initial) == [3, 5, 5, 5, 55]
#guard probes blocked.retained aliasInput == [some 3, some 5, some 5, some 5, none]
#guard probes withoutBoth aliasInput == [some 3, some 5, some 8, some 8, none]

private def aliasDiscovery := discover preds fits entry arms suffix aliasInput
#guard aliasDiscovery.deleted == 1
#guard entryBuffers aliasDiscovery == entryBuffers blocked

private def stale := lower preds fits entry arms suffix input [.expect 1, .expect 2]
#guard stale.deleted == 1 && stale.remaining.length == 1
#guard entryBuffers stale == entryBuffers blocked

-- Rebind the already admitted two-cut chain without rediscovering it.
private def newInputs (readCell : Address 5) : Tuple (Val 5) Args :=
  .cons (1 : Address 5) (.cons (3 : Address 5) (.cons (0 : Address 5) (.cons readCell (.cons (2 : Address 5)
    (.cons (101 : Word) (.cons (202 : Word) (.cons (303 : Word) .nil)))))))

private def newInput := newInputs 0
private def secondAlias := newInputs 3

private def newBuffer : Buffer 5 :=
  ⟨fun cell => if cell = 0 then 60 else if cell = 1 then 70 else if cell = 2 then 80
    else if cell = 3 then 90 else 100⟩

private theorem recorded : Trace fits arms suffix input entry (lowerBank preds fits 5 (some entry) arms suffix)
    (List.replicate 3 .discover) success :=
  lower_trace

private def rebound := Reuse.Chain.lower success entry newInput
private def prefixOnly := Reuse.Chain.lower success entry secondAlias

#guard Reuse.Chain.check success newInput
#guard rebound.pending.isEmpty && rebound.replay.deleted == 2
#guard rebound.replay.admitted.map MixedTail.Result.version == [1, 1]
#guard rebound.replay.admitted.map (fun stage => (occurrenceRecords stage).toList.map ArmOverwrite.storeVersion) ==
  [[1, 2, 1], [2, 1, 2]]

example (complete : rebound.pending = []) : rebound.replay.programs.optimized = success.programs.optimized :=
  (Reuse.Chain.lower_complete_artifacts recorded complete).1

private def reboundBuffers (result : Result 5 Args preds) : List (List Nat) :=
  (artifacts result).map fun program => contents (entryTransition program result.programs.input 1 newBuffer).2

#guard reboundBuffers rebound.replay == [[60, 80, 60, 60, 100], [60, 70, 60, 60, 100], [60, 70, 60, 90, 100]]
#guard contents (rebound.replay.restoreEntry newBuffer) == [60, 80, 60, 60, 100]

private def newSnapshot (program : Program 5 Args preds) (values : Tuple (Val 5) Args)
    (arrival : Occurrence preds) : Option (Nat × List Nat × List Nat) := do
  let entered := entryTransition program values arrival newBuffer
  let .inl ⟨.arm slot, _⟩ := entered.1 | none
  let joined := armTransition program values slot entered.2
  let .inl ⟨.join, words⟩ := joined.1 | none
  let final ← run program values arrival 3 newBuffer
  some (slot.val, (words.get .here).toNat :: contents joined.2, final.1.toNat :: contents final.2)

private def reboundSnapshots (result : Result 5 Args preds) :
    List (List (Option (Nat × List Nat × List Nat))) :=
  List.ofFn fun i => (artifacts result).map fun artifact => newSnapshot artifact result.programs.input i

private def newExpected : List (Option (Nat × List Nat × List Nat)) :=
  [some (0, [60, 60, 101, 60, 101, 100], [101, 60, 101, 60, 101, 100]),
   some (1, [60, 60, 202, 60, 202, 100], [202, 60, 202, 60, 202, 100]),
   some (2, [60, 60, 303, 60, 303, 100], [303, 60, 303, 60, 303, 100])]

#guard reboundSnapshots rebound.replay == newExpected.map (List.replicate 3)

private def newProbes (graph : Memory.Graph Args) (values : Tuple (Val 5) Args) : List (Option Nat) :=
  List.ofFn fun (index : Fin 5) => (Memory.DeadStore.throughLoad graph index.val).map fun block =>
    (observe block values newBuffer).1.toNat

#guard newProbes entry newInput == [some 80, some 60, some 60, some 60, none]
#guard rebound.replay.admitted.all (fun stage =>
  newProbes stage.emission.edit.retained stage.emission.programs.input == newProbes entry newInput)

-- Only the second recorded cut loses separation, on the new right cell.
#guard (Reuse.Chain.contracts success).map (fun facts => facts.check secondAlias) == [true, false]
#guard prefixOnly.replay.deleted == 1 && prefixOnly.pending.length == 1
#guard reboundBuffers prefixOnly.replay == [[60, 80, 60, 60, 100], [60, 70, 60, 60, 100]]
#guard contents (entryTransition prefixOnly.replay.programs.optimized prefixOnly.replay.programs.input 1 newBuffer).2 ==
  [60, 70, 60, 60, 100]
#guard reboundSnapshots prefixOnly.replay == newExpected.map (List.replicate 2)
#guard newProbes prefixOnly.replay.retained secondAlias == newProbes entry secondAlias
#guard newProbes withoutBoth secondAlias == [some 80, some 60, some 90, some 90, none]

private def passed := Reuse.Chain.Diagnostic.lower success entry newInput
private def explained := Reuse.Chain.Diagnostic.lower success entry secondAlias

#guard passed.refusal.isNone && passed.checkedPrefix.replay.deleted == 2
#guard reboundSnapshots passed.checkedPrefix.replay == newExpected.map (List.replicate 3)
#guard explained.checkedPrefix.replay.deleted == 1 && explained.checkedPrefix.pending.length == 1
#guard reboundBuffers explained.checkedPrefix.replay == reboundBuffers prefixOnly.replay
#guard reboundSnapshots explained.checkedPrefix.replay == newExpected.map (List.replicate 2)

#guard (explained.refusal.map fun report =>
  let access := match report.conflict.site with
    | .entry index => some index
    | .arm _ _ => none
  (report.stageIndex, report.version, report.store.index, access, report.conflict.port.index,
    report.conflict.address.val)) == some (1, 1, 1, some 0, 3, 3)

example : explained.checkedPrefix = prefixOnly := Reuse.Chain.Diagnostic.lower_prefix

-- A stale original request is stopped by admission and never enters the recorded chain.
#guard (Reuse.Chain.Diagnostic.lower stale entry input).refusal.isNone

-- A different Store can still be cut after the recorded right Store refuses.
-- The final side write uses the first entry Load and is killed in every arm.
private def entryWithSide : Memory.Graph Args :=
  .load (.latest 0) (.arg sink)
    (.store (.latest 0) (.arg left) (.output 0 .head)
      (.load (.latest 1) (.arg side)
        (.store (.latest 1) (.arg right) (.output 0 .head)
          (.load (.latest 2) (.arg reader)
            (.store (.latest 2) (.arg sink) (.output 0 .head)
              (.load (.latest 3) (.arg sink)
                (.store (.latest 3) (.arg side) (.output 3 .head)
                  (.ret (.latest 4) (.output 0 .head)))))))))

private def writeSideBeforeReturn :
    {past : List (List ValueSort)} → {live : Nat} → Memory.Body Args past live → Memory.Body Args past live
  | _, live, .ret memory word =>
    .store memory (.arg side) word (.ret (.latest (live + 1)) word)
  | _, _, .load memory address rest => .load memory address (writeSideBeforeReturn rest)
  | _, _, .store memory address word rest => .store memory address word (writeSideBeforeReturn rest)

private def recoveryArms (arrival : Occurrence preds) := writeSideBeforeReturn (arms arrival)

private def twoRecorded := lower preds fits entryWithSide recoveryArms suffix input plan
private theorem twoRecorded_trace :
    Trace fits recoveryArms suffix input entryWithSide (lowerBank preds fits 5 (some entryWithSide) recoveryArms suffix)
      plan twoRecorded :=
  lower_trace

private def recovered := Reuse.Chain.Recovery.lower twoRecorded entryWithSide fits recoveryArms suffix secondAlias

#guard twoRecorded.admitted.map (fun stage => stage.emission.edit.address.index) == [0, 1]
#guard recovered.diagnostic.checkedPrefix.replay.deleted == 1 && recovered.deleted == 2
#guard (recovered.diagnostic.refusal.map fun report => (report.stageIndex, report.version, report.conflict.address.val)) ==
  some (1, 1, 3)
#guard recovered.diagnostic.checkedPrefix.pending.map (fun stage => stage.emission.edit.address.index) == [1]
#guard (recovered.fresh.map fun fresh =>
  fresh.admitted.map (fun stage => (stage.version, stage.emission.edit.address.index))) == some [(3, 2)]
#guard storeVersions recovered.retained == [1, 2]

example {fresh : Result 5 Args preds} (resumed : recovered.fresh = some fresh) :
    fresh.programs.original = recovered.diagnostic.checkedPrefix.replay.programs.optimized :=
  (Reuse.Chain.Recovery.lower_fresh_trace twoRecorded_trace resumed).1

private def recoveryArtifacts : List (Program 5 Args preds) :=
  artifacts recovered.diagnostic.checkedPrefix.replay ++
    (recovered.fresh.map fun fresh => fresh.admitted.map (fun stage => stage.emission.programs.optimized)).getD []

#guard recoveryArtifacts.map (fun program => contents (entryTransition program secondAlias 1 newBuffer).2) ==
  [[80, 80, 60, 60, 100], [80, 70, 60, 60, 100], [60, 70, 60, 60, 100]]
#guard (List.ofFn fun i => recoveryArtifacts.map fun program => newSnapshot program secondAlias i) ==
  newExpected.map (List.replicate 3)
#guard newProbes recovered.retained secondAlias == newProbes entryWithSide secondAlias

private def fullReuse := Reuse.Chain.Recovery.lower twoRecorded entryWithSide fits recoveryArms suffix newInput
#guard fullReuse.diagnostic.refusal.isNone && fullReuse.fresh.isNone && fullReuse.deleted == 2

-- The original fixture has no alternative cut. A refused recovery attempt
-- returns the same endpoint and retains the same diagnostic.
private def noAlternative := Reuse.Chain.Recovery.lower success entry fits arms suffix secondAlias
#guard noAlternative.diagnostic.refusal.isSome && noAlternative.fresh.map Result.deleted == some 0
#guard contents (entryTransition noAlternative.optimized secondAlias 1 newBuffer).2 == [60, 70, 60, 60, 100]

example (zero : (noAlternative.fresh.map Result.deleted).getD 0 = 0) :
    noAlternative.optimized = noAlternative.diagnostic.checkedPrefix.replay.programs.optimized :=
  (Reuse.Chain.Recovery.lower_no_fresh_cuts recorded zero).1

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Replay
