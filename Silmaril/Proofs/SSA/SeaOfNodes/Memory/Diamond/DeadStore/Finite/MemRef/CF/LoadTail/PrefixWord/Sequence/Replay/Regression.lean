module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay

open RVSDG (Port Tuple)
open Quads.CFG (Predecessors)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

private abbrev Args : List ValueSort := [.address, .address, .address, .address, .word, .word, .word]

private def left : Port Args .address := .head
private def middle : Port Args .address := .tail .head
private def right : Port Args .address := .tail (.tail .head)
private def side : Port Args .address := .tail (.tail (.tail .head))
private def firstWord : Port Args .word := .tail (.tail (.tail (.tail .head)))
private def secondWord : Port Args .word := .tail (.tail (.tail (.tail (.tail .head))))
private def thirdWord : Port Args .word := .tail (.tail (.tail (.tail (.tail (.tail .head)))))

private def input : Tuple (Val 5) Args :=
  .cons (0 : Address 5) (.cons (1 : Address 5) (.cons (2 : Address 5) (.cons (3 : Address 5)
    (.cons (11 : Word) (.cons (22 : Word) (.cons (99 : Word) .nil))))))

private def initial : Buffer 5 :=
  ⟨fun cell => if cell = 0 then 7 else if cell = 1 then 8 else if cell = 2 then 9
    else if cell = 3 then 40 else 55⟩

private abbrev ThreeWords := [[ValueSort.word], [ValueSort.word], [ValueSort.word]]
private abbrev FourWords := [ValueSort.word] :: ThreeWords

private def entryPrefix (rest : Memory.Body Args ThreeWords 0) : Memory.Graph Args :=
  .load (.latest 0) (.arg left)
    (.load (.latest 0) (.arg middle) (.load (.latest 0) (.arg right) rest))

private def finishEntry (version : Nat) : Memory.Body Args FourWords version :=
  .load (.latest version) (.arg side) (.ret (.latest version) (.output 1 .head))

private def original (reader : Port Args .address) : Memory.Graph Args :=
  entryPrefix (.store (.latest 0) (.arg left) (.output 0 .head)
    (.load (.latest 1) (.arg reader)
      (.store (.latest 1) (.arg middle) (.output 3 .head)
        (.store (.latest 2) (.arg right) (.output 2 .head) (finishEntry 3)))))

private def afterTwo (reader : Port Args .address) : Memory.Graph Args :=
  entryPrefix (.store (.latest 0) (.arg left) (.output 0 .head)
    (.load (.latest 1) (.arg reader) (finishEntry 1)))

private def afterThree (reader : Port Args .address) : Memory.Graph Args :=
  entryPrefix (.load (.latest 0) (.arg reader) (finishEntry 0))

private def preds : Predecessors 2 := ⟨0, [0, 1]⟩
private theorem fits : Fits preds := by decide

example : List.ofFn preds.get = [0, 0, 1] := rfl

private def route (value : Port Args .word) : Memory.Graph Args :=
  .store (.latest 0) (.arg left) (.arg value)
    (.store (.latest 1) (.arg middle) (.arg value)
      (.store (.latest 2) (.arg right) (.arg value)
        (.load (.latest 3) (.arg side) (.ret (.latest 3) (.output 0 .head)))))

private def arms (i : Occurrence preds) : Memory.Graph Args :=
  match i.val with
  | 0 => route firstWord
  | 1 => route secondWord
  | _ => route thirdWord

private def suffix : Memory.Graph (.word :: Args) :=
  .store (.latest 0) (.arg (.tail side)) (.arg .head)
    (.load (.latest 1) (.arg (.tail right)) (.ret (.latest 1) (.output 0 .head)))

private def request (version : Nat) (address : Port Args .address) : Request Args preds :=
  ⟨version, ⟨address, [side]⟩, fun _ => ⟨version, []⟩⟩

private def first : Request Args preds := request 3 right
private def second : Request Args preds := request 2 middle
private def third : Request Args preds := request 1 left

private def success := lower preds fits (original side) arms suffix input [first, second, third]

#guard success.deleted == 3
#guard success.remaining.isEmpty
example : success.retained = afterThree side := rfl
example : success.programs.optimized = lowerBank preds fits 5 (some (afterThree side)) arms suffix := rfl

private def contents (buffer : Buffer 5) : List Nat :=
  List.ofFn fun i => (buffer.cell i).toNat

private def artifacts (result : Result 5 Args preds) : List (Program 5 Args preds) :=
  result.programs.original :: result.admitted.map (fun stage => stage.programs.optimized)

example : success.admitted.map (fun stage => stage.programs.original) = (artifacts success).take 3 := rfl
example : success.admitted.map (fun stage => stage.programs.input) = List.replicate 3 input := rfl

#guard (artifacts success).map (fun program => contents (entryTransition program input 1 initial).2) ==
  [[9, 7, 8, 40, 55], [9, 7, 9, 40, 55], [9, 8, 9, 40, 55], [7, 8, 9, 40, 55]]

private def snapshot (program : Program 5 Args preds) (arrival : Occurrence preds) (fuel : Nat) :
    Option (Nat × List Nat × List Nat) := do
  let entered := entryTransition program input arrival initial
  let .inl ⟨.arm slot, _⟩ := entered.1 | none
  let joined := armTransition program input slot entered.2
  let .inl ⟨.join, words⟩ := joined.1 | none
  let final ← run program input arrival fuel initial
  some (slot.val, (words.get .here).toNat :: contents joined.2, final.1.toNat :: contents final.2)

private def observations (result : Result 5 Args preds) :
    List (List (Option (Nat × List Nat × List Nat))) :=
  List.ofFn fun i => (artifacts result).map fun program => snapshot program i 3

private def expected : List (Option (Nat × List Nat × List Nat)) :=
  [some (0, [40, 11, 11, 11, 40, 55], [11, 11, 11, 11, 40, 55]),
   some (1, [40, 22, 22, 22, 40, 55], [22, 22, 22, 22, 40, 55]),
   some (2, [40, 99, 99, 99, 40, 55], [99, 99, 99, 99, 40, 55])]

#guard observations success == expected.map (List.replicate 4)
#guard (artifacts success).all (fun program => (run program input 1 2 initial).isNone)

private def probes (graph : Memory.Graph Args) : List (Option Nat) :=
  List.ofFn fun (index : Fin 6) => (Memory.DeadStore.throughLoad graph index.val).map fun block =>
    (observe block input initial).1.toNat

#guard probes (original side) == [some 7, some 8, some 9, some 40, some 40, none]
#guard success.admitted.all (fun stage => probes stage.edit.retained == probes (original side))

-- This Load moves into the checked suffix for the third request.
-- It reads the oldest Store's cell, while both later cuts are still safe.
private def blocked := lower preds fits (original left) arms suffix input [first, second, third, first]

#guard blocked.deleted == 2
#guard blocked.remaining.map Request.version == [1, 3]
example : blocked.retained = afterTwo left := rfl
example : some blocked.programs.optimized = blocked.admitted.getLast?.map (fun stage => stage.programs.optimized) := rfl
#guard observations blocked == expected.map (List.replicate 3)
#guard (observe blocked.retained input initial).1.toNat == 9
#guard (observe (afterThree left) input initial).1.toNat == 7

-- An older request naming the previous cut's address refuses on the current table.
private def stale := lower preds fits (original side) arms suffix input [first, second, request 1 middle]

#guard stale.deleted == 2
#guard stale.remaining.map Request.version == [1]
example : stale.retained = afterTwo side := rfl

private def empty := lower preds fits (original side) arms suffix input []
example : empty.programs.optimized = empty.programs.original := rfl
#guard empty.deleted == 0 && empty.remaining.isEmpty

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Replay
