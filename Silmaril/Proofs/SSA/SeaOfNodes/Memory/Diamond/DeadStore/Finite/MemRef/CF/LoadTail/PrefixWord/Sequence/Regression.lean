module

import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Thms
meta import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence.Defs
meta import Silmaril.SSA.SeaOfNodes.Memory.MLIR.MemRef.Defs

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence

open RVSDG (Origin Port Tuple)
open Quads.CFG (Predecessors)
open Silmaril.MLIR.MemRef (Buffer)
open SeaOfNodes.Memory.MLIR.MemRef (observe)

private abbrev Args : List ValueSort := [.address, .address, .address, .word, .word, .word]

private def left : Port Args .address := .head
private def right : Port Args .address := .tail .head
private def side : Port Args .address := .tail (.tail .head)
private def firstWord : Port Args .word := .tail (.tail (.tail .head))
private def middleWord : Port Args .word := .tail (.tail (.tail (.tail .head)))
private def lastWord : Port Args .word := .tail (.tail (.tail (.tail (.tail .head))))

private def input : Tuple (Val 4) Args :=
  .cons (0 : Address 4) (.cons (1 : Address 4) (.cons (2 : Address 4)
    (.cons (11 : Word) (.cons (22 : Word) (.cons (99 : Word) .nil)))))

private def initial : Buffer 4 :=
  ⟨fun i => if i = 0 then 7 else if i = 1 then 8 else if i = 2 then 33 else 55⟩

private abbrev Bindings := [[ValueSort.word], [ValueSort.word]]

private def sharedPrefix (tail : Memory.Body Args Bindings 0) : Memory.Graph Args :=
  .load (.latest 0) (.arg left) (.load (.latest 0) (.arg right) tail)

private def loadTail (version : Nat) : Memory.Body Args Bindings version :=
  .load (.latest version) (.arg side)
    (.load (.latest version) (.arg side) (.ret (.latest version) (.output 0 .head)))

private def original : Memory.Graph Args :=
  sharedPrefix (.store (.latest 0) (.arg left) (.output 0 .head)
    (.store (.latest 1) (.arg right) (.output 1 .head) (loadTail 2)))

private def intermediate : Memory.Graph Args :=
  sharedPrefix (.store (.latest 0) (.arg left) (.output 0 .head) (loadTail 1))

private def retained : Memory.Graph Args := sharedPrefix (loadTail 0)

private def preds : Predecessors 2 := ⟨0, [0, 1]⟩
private theorem fits : Fits preds := by decide

example : List.ofFn preds.get = [0, 0, 1] := rfl

private def route (reader : Port Args .address) (word : Port Args .word) : Memory.Graph Args :=
  .store (.latest 0) (.arg right) (.arg word)
    (.load (.latest 1) (.arg reader)
      (.store (.latest 1) (.arg left) (.arg word) (.ret (.latest 2) (.output 0 .head))))

private def arms (middleReader : Port Args .address) (i : Occurrence preds) : Memory.Graph Args :=
  match i.val with
  | 0 => route side firstWord
  | 1 => route middleReader middleWord
  | _ => route side lastWord

private def suffix : Memory.Graph (.word :: Args) :=
  .store (.latest 0) (.arg (.tail side)) (.arg .head)
    (.load (.latest 1) (.arg (.tail left)) (.ret (.latest 1) (.output 0 .head)))

private def first : Request Args preds := ⟨2, ⟨right, [side]⟩, fun _ => ⟨1, []⟩⟩
private def second : Request Args preds := ⟨1, ⟨left, [side]⟩, fun _ => ⟨2, [side]⟩⟩

private def success := lower preds fits original (arms side) suffix input first second

example : success.map (fun result => result.first.edit.retained) = some intermediate := rfl
example : success.map Result.retained = some retained := rfl
#guard success.map Result.deleted == some 2

private def contents (buffer : Buffer 4) : List Nat :=
  List.ofFn fun i => (buffer.cell i).toNat

private def snapshot (program : Program 4 Args preds) (arrival : Occurrence preds) (fuel : Nat) :
    Option (Nat × List Nat × List Nat) := do
  let entered := entryTransition program input arrival initial
  let .inl ⟨.arm slot, _⟩ := entered.1 | none
  let joined := armTransition program input slot entered.2
  let .inl ⟨.join, words⟩ := joined.1 | none
  let final ← run program input arrival fuel initial
  some (slot.val, (words.get .here).toNat :: contents joined.2, final.1.toNat :: contents final.2)

private def snapshots (result : Result 4 Args preds) (arrival : Occurrence preds) (fuel : Nat) :
    Option (Nat × List Nat × List Nat) := do
  let next ← result.second
  let before ← snapshot result.programs.original arrival fuel
  let middle ← snapshot result.first.programs.optimized arrival fuel
  let reentry ← snapshot next.programs.original arrival fuel
  let after ← snapshot result.programs.optimized arrival fuel
  if before == middle && middle == reentry && reentry == after then some after else none

#guard (List.ofFn fun i => success.bind fun result => snapshots result i 3) ==
  [some (0, [33, 11, 11, 33, 55], [11, 11, 11, 33, 55]),
   some (1, [33, 22, 22, 33, 55], [22, 22, 22, 33, 55]),
   some (2, [33, 99, 99, 33, 55], [99, 99, 99, 33, 55])]

#guard (success.map fun result =>
  [result.programs.original, result.first.programs.optimized, result.programs.optimized].map fun program =>
    contents (entryTransition program input 1 initial).2) ==
  some [[8, 7, 33, 55], [8, 8, 33, 55], [7, 8, 33, 55]]

#guard (success.map fun result =>
  [result.programs.original, result.first.programs.optimized, result.programs.optimized].all fun program =>
    (run program input 1 2 initial).isNone) == some true

private def readbacks (graph : Memory.Graph Args) : List (Option Nat) :=
  List.ofFn fun (index : Fin 5) => (Memory.DeadStore.throughLoad graph index.val).map fun block =>
    (observe block input initial).1.toNat

#guard readbacks original == [some 7, some 8, some 33, some 33, none]
#guard (success.map fun result => [readbacks result.first.edit.retained, readbacks result.retained]) ==
  some [readbacks original, readbacks original]

-- Reusing version two would succeed on the original table but refuses on
-- the retained one. The first optimized artifact remains the result.
private def stale := lower preds fits original (arms side) suffix input first first
#guard stale.map Result.deleted == some 1
example : stale.map Result.retained = some intermediate := rfl

#guard (lower preds fits original (arms side) suffix input second first).isNone

private def uncovered := lower preds fits original (arms side) suffix input first
  { second with facts := ⟨left, []⟩ }
#guard uncovered.map Result.deleted == some 1
example : uncovered.map Result.retained = some intermediate := rfl

-- The middle occurrence reads the older candidate before its overwrite.
-- This read is after the latest candidate's overwrite, so that cut succeeds.
private def blocked := lower preds fits original (arms left) suffix input first second
#guard (List.ofFn fun i => checkArm left (arms left i) (second.candidate i) input) == [true, false, true]
#guard blocked.map Result.deleted == some 1
example : blocked.map Result.retained = some intermediate := rfl
#guard (blocked.bind fun result => snapshot result.programs.optimized 1 3) ==
  some (1, [8, 22, 22, 33, 55], [22, 22, 22, 8, 55])
#guard snapshot (lowerBank preds fits 4 (some retained) (arms left) suffix) 1 3 ==
  some (1, [7, 22, 22, 33, 55], [22, 22, 22, 7, 55])

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.MemRef.CF.LoadTail.PrefixWord.Sequence
