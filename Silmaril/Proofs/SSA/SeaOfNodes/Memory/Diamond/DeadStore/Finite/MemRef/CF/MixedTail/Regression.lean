module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail

open RVSDG (Port Tuple)
open Quads.CFG (Predecessors)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

private abbrev Args : List ValueSort := [.address, .address, .address, .word, .word, .word]

private def target : Port Args .address := .head
private def reader : Port Args .address := .tail .head
private def sink : Port Args .address := .tail (.tail .head)
private def firstWord : Port Args .word := .tail (.tail (.tail .head))
private def secondWord : Port Args .word := .tail (.tail (.tail (.tail .head)))
private def thirdWord : Port Args .word := .tail (.tail (.tail (.tail (.tail .head))))

private def inputs (readCell : Address 4) : Tuple (Val 4) Args :=
  .cons (0 : Address 4) (.cons readCell (.cons (2 : Address 4)
    (.cons (11 : Word) (.cons (22 : Word) (.cons (99 : Word) .nil)))))

private def input := inputs 1
private def aliasInput := inputs 0

private def initial : Buffer 4 :=
  ⟨fun cell => if cell = 0 then 7 else if cell = 1 then 5 else if cell = 2 then 3 else 55⟩

-- The retained Store consumes the intervening Load. The final Load
-- reads the retained Store's word and supplies the entry Return.
private def mixedSuffix (version : Nat) : Memory.Body Args [[.word]] version :=
  .load (.latest version) (.arg reader)
    (.store (.latest version) (.arg sink) (.output 0 .head)
      (.load (.latest (version + 1)) (.arg sink) (.ret (.latest (version + 1)) (.output 0 .head))))

private def original : Memory.Graph Args :=
  .load (.latest 0) (.arg sink)
    (.store (.latest 0) (.arg target) (.output 0 .head) (mixedSuffix 1))

private def retained : Memory.Graph Args :=
  .load (.latest 0) (.arg sink) (mixedSuffix 0)

private def edit : LoadTail.PrefixWord.Cut Args [] 0 :=
  ⟨target, .load (.latest 0) (.arg sink) (.ret (.latest 0) (.output 0 .head)), retained⟩

example : inferCut 1 original = some (edit, [reader, sink, sink]) := rfl
example : LoadTail.PrefixWord.Sequence.Replay.Search.inferEntry 1 original = none := rfl

private def preds : Predecessors 2 := ⟨0, [0, 1]⟩
private theorem fits : Fits preds := by decide

example : List.ofFn preds.get = [0, 0, 1] := rfl

private def arms (i : Occurrence preds) : Memory.Graph Args :=
  match i.val with
  | 0 => .load (.latest 0) (.arg sink)
      (.store (.latest 0) (.arg target) (.arg firstWord) (.ret (.latest 1) (.output 0 .head)))
  | 1 => .store (.latest 0) (.arg reader) (.arg secondWord)
      (.load (.latest 1) (.arg sink)
        (.store (.latest 1) (.arg target) (.arg secondWord) (.ret (.latest 2) (.output 0 .head))))
  | _ => .store (.latest 0) (.arg target) (.arg thirdWord)
      (.load (.latest 1) (.arg sink) (.ret (.latest 1) (.output 0 .head)))

private def suffix : Memory.Graph (.word :: Args) :=
  .store (.latest 0) (.arg (.tail reader)) (.arg .head)
    (.load (.latest 1) (.arg (.tail target)) (.ret (.latest 1) (.output 0 .head)))

private def success := lower fits arms suffix input original

#guard success.map Result.version == some 1
#guard (success.map fun found => List.ofFn fun i => (found.candidate i).storeVersion) == some [1, 2, 1]

private def contents (buffer : Buffer 4) : List Nat :=
  List.ofFn fun i => (buffer.cell i).toNat

#guard (success.map fun found =>
  let programs := found.emission.programs
  [programs.original, programs.optimized].map fun program =>
    contents (entryTransition program programs.input 1 initial).2) ==
  some [[3, 5, 5, 55], [7, 5, 5, 55]]

private def snapshot (program : Program 4 Args preds) (values : Tuple (Val 4) Args) (arrival : Occurrence preds) :
    Option (Nat × List Nat × List Nat) := do
  let entered := entryTransition program values arrival initial
  let .inl ⟨.arm slot, _⟩ := entered.1 | none
  let joined := armTransition program values slot entered.2
  let .inl ⟨.join, words⟩ := joined.1 | none
  let final ← run program values arrival 3 initial
  some (slot.val, (words.get .here).toNat :: contents joined.2, final.1.toNat :: contents final.2)

private def expected : List (Option (Nat × List Nat × List Nat)) :=
  [some (0, [5, 11, 5, 5, 55], [11, 11, 5, 5, 55]),
   some (1, [5, 22, 22, 5, 55], [22, 22, 5, 5, 55]),
   some (2, [5, 99, 5, 5, 55], [99, 99, 5, 5, 55])]

#guard (success.map fun found =>
  let programs := found.emission.programs
  [programs.original, programs.optimized].map fun program =>
    List.ofFn fun i => snapshot program programs.input i) == some [expected, expected]
#guard (success.map fun found =>
  let programs := found.emission.programs
  [programs.original, programs.optimized].all fun program => (run program programs.input 1 2 initial).isNone) ==
  some true

private def probes (graph : Memory.Graph Args) (values : Tuple (Val 4) Args) : List (Option Nat) :=
  List.ofFn fun (index : Fin 4) => (Memory.DeadStore.throughLoad graph index.val).map fun block =>
    (observe block values initial).1.toNat

#guard probes original input == [some 3, some 5, some 5, none]
#guard (success.map fun found => probes found.emission.edit.retained found.emission.programs.input) ==
  some (probes original input)

-- The two address ports coincide only at this invocation. The observable
-- Load would change the retained Store, the entry Return and the join word.
#guard probes original aliasInput == [some 3, some 3, some 3, none]
#guard probes retained aliasInput == [some 3, some 7, some 7, none]
#guard (LoadTail.PrefixWord.Sequence.Replay.Search.inferCandidate preds target arms).map (fun candidate =>
  LoadTail.PrefixWord.checkArms preds target arms candidate aliasInput) == some true
#guard snapshot (lowerBank preds fits 4 (some original) arms suffix) aliasInput 0 ==
  some (0, [3, 11, 5, 3, 55], [3, 3, 5, 3, 55])
#guard snapshot (lowerBank preds fits 4 (some retained) arms suffix) aliasInput 0 ==
  some (0, [7, 11, 5, 7, 55], [7, 7, 5, 7, 55])
#guard (tryVersion fits arms suffix aliasInput original 1).isNone
#guard (lower fits arms suffix aliasInput original).isNone

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.MixedTail
