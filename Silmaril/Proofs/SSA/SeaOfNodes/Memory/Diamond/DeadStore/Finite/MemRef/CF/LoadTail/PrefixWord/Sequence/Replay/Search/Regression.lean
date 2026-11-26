module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Search.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Search.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Search

open RVSDG (Port Tuple)
open Quads.CFG (Predecessors)
open Memory.DeadStore.Search.Selection (storeVersions)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

private abbrev Args : List ValueSort := [.address, .address, .address, .address, .word, .word, .word]

private def left : Port Args .address := .head
private def right : Port Args .address := .tail .head
private def side : Port Args .address := .tail (.tail .head)
private def logger : Port Args .address := .tail (.tail (.tail .head))
private def firstWord : Port Args .word := .tail (.tail (.tail (.tail .head)))
private def secondWord : Port Args .word := .tail (.tail (.tail (.tail (.tail .head))))
private def thirdWord : Port Args .word := .tail (.tail (.tail (.tail (.tail (.tail .head)))))

private def inputs (logCell : Address 4) : Tuple (Val 4) Args :=
  .cons (0 : Address 4) (.cons (1 : Address 4) (.cons (2 : Address 4) (.cons logCell
    (.cons (11 : Word) (.cons (22 : Word) (.cons (99 : Word) .nil))))))

private def input := inputs 2
private def aliasInput := inputs 1

private def initial : Buffer 4 :=
  ⟨fun cell => if cell = 0 then 7 else if cell = 1 then 8 else if cell = 2 then 40 else 55⟩

private abbrev TwoWords := [[ValueSort.word], [ValueSort.word]]

private def entryPrefix (rest : Memory.Body Args TwoWords 0) : Memory.Graph Args :=
  .load (.latest 0) (.arg left) (.load (.latest 0) (.arg right) rest)

private def original (reader : Port Args .address) : Memory.Graph Args :=
  entryPrefix (.store (.latest 0) (.arg left) (.output 0 .head)
    (.load (.latest 1) (.arg reader)
      (.store (.latest 1) (.arg right) (.output 2 .head)
        (.load (.latest 2) (.arg side) (.ret (.latest 2) (.output 1 .head))))))

private def afterTwo (reader : Port Args .address) : Memory.Graph Args :=
  entryPrefix (.load (.latest 0) (.arg reader) (.load (.latest 0) (.arg side) (.ret (.latest 0) (.output 1 .head))))

private def preds : Predecessors 2 := ⟨0, [0, 1]⟩
private theorem fits : Fits preds := by decide

example : List.ofFn preds.get = [0, 0, 1] := rfl

private def arms (i : Occurrence preds) : Memory.Graph Args :=
  match i.val with
  | 0 => .store (.latest 0) (.arg right) (.arg firstWord)
      (.load (.latest 1) (.arg side)
        (.store (.latest 1) (.arg left) (.arg firstWord) (.ret (.latest 2) (.output 0 .head))))
  | 1 => .load (.latest 0) (.arg logger)
      (.store (.latest 0) (.arg left) (.arg secondWord)
        (.store (.latest 1) (.arg right) (.arg secondWord) (.ret (.latest 2) (.output 0 .head))))
  | _ => .store (.latest 0) (.arg right) (.arg thirdWord)
      (.store (.latest 1) (.arg left) (.arg thirdWord)
        (.load (.latest 2) (.arg side) (.ret (.latest 2) (.output 0 .head))))

private def suffix : Memory.Graph (.word :: Args) :=
  .store (.latest 0) (.arg (.tail side)) (.arg .head)
    (.load (.latest 1) (.arg (.tail right)) (.ret (.latest 1) (.output 0 .head)))

example : storeVersions (original side) = [1, 2] := rfl
example : tryVersion fits arms suffix input (original side) 1 = none := rfl

private def firstFound := find fits arms suffix input (original side)
#guard firstFound.map (fun found => found.1.version) == some 2
#guard (firstFound.map fun found => List.ofFn fun i => (found.1.candidate i).storeVersion) == some [1, 2, 1]

private def success := lower preds fits (original side) arms suffix input

#guard success.requests.map Request.version == [2, 1]
#guard success.replay.deleted == 2 && success.replay.remaining.isEmpty
#guard (storeVersions success.replay.retained).isEmpty
example : Replay.lower preds fits (original side) arms suffix input success.requests = success.replay :=
  (lower_replayed (fits := fits) (entry := original side) (arm := arms) (suffix := suffix) (input := input)).1

private def contents (buffer : Buffer 4) : List Nat := List.ofFn fun i => (buffer.cell i).toNat

private def artifacts (result : Result 4 Args preds) : List (Program 4 Args preds) :=
  result.replay.programs.original :: result.replay.admitted.map (fun stage => stage.programs.optimized)

#guard (artifacts success).map (fun program => contents (entryTransition program input 1 initial).2) ==
  [[8, 7, 40, 55], [8, 8, 40, 55], [7, 8, 40, 55]]

private def snapshot (program : Program 4 Args preds) (arrival : Occurrence preds) :
    Option (Nat × List Nat × List Nat) := do
  let entered := entryTransition program input arrival initial
  let .inl ⟨.arm slot, _⟩ := entered.1 | none
  let joined := armTransition program input slot entered.2
  let .inl ⟨.join, words⟩ := joined.1 | none
  let final ← CF.run program input arrival 3 initial
  some (slot.val, (words.get .here).toNat :: contents joined.2, final.1.toNat :: contents final.2)

private def expected : List (Option (Nat × List Nat × List Nat)) :=
  [some (0, [40, 11, 11, 40, 55], [11, 11, 11, 40, 55]),
   some (1, [40, 22, 22, 40, 55], [22, 22, 22, 40, 55]),
   some (2, [40, 99, 99, 40, 55], [99, 99, 99, 40, 55])]

#guard (List.ofFn fun i => (artifacts success).map fun artifact => snapshot artifact i) ==
  expected.map (List.replicate 3)
#guard (artifacts success).all (fun program => (CF.run program input 1 2 initial).isNone)

private def probes (graph : Memory.Graph Args) : List (Option Nat) :=
  List.ofFn fun (index : Fin 5) => (Memory.DeadStore.throughLoad graph index.val).map fun block =>
    (observe block input initial).1.toNat

#guard probes (original side) == [some 7, some 8, some 40, some 40, none]
#guard success.replay.admitted.all (fun stage => probes stage.edit.retained == probes (original side))

-- The older Store survives when its entry reader observes it after re-admission.
private def blocked := lower preds fits (original left) arms suffix input
#guard blocked.requests.map Request.version == [2]
#guard storeVersions blocked.replay.retained == [1]
#guard contents (entryTransition blocked.replay.programs.optimized input 1 initial).2 == [8, 8, 40, 55]
example : find fits arms suffix input blocked.replay.retained = none :=
  find_eq_none_iff.mpr (lower_exhausted (fits := fits) (entry := original left) (arm := arms)
    (suffix := suffix) (input := input))
#guard (observe blocked.replay.retained input initial).1.toNat == 8
#guard (observe (afterTwo left) input initial).1.toNat == 7

-- On the middle occurrence only, a distinct reader port evaluates to the
-- removed cell. The inferred proposal and entry facts still exist.
#guard (inferEntry 2 (original side)).map (fun facts => facts.check aliasInput) == some true
#guard (inferCandidate preds right arms).map (fun candidate =>
  List.ofFn fun i => checkArm right (arms i) (candidate i) aliasInput) == some [true, false, true]
#guard (find fits arms suffix aliasInput (original side)).isNone
#guard (lower preds fits (original side) arms suffix aliasInput).replay.deleted == 0

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Search
