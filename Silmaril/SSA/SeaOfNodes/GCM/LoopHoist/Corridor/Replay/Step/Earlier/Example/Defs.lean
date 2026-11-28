module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Example.Defs

/-! # An earlier insertion between two dependent saved definitions -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Example

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Frame Terminator)
open Loop.MLIR.CF (Program evalOp)
open Corridor.Example (Inputs word entrySigs input)
open AfterReorder.Second.Example (first)
open Replay.Example (producer consumer)
open Step.Example (Schedule loop loopWith loopWithOlderSave words)

def nominate? (g : Program Inputs word word entrySigs Schedule) (request : Nomination) :
    Option ((saved : Width) × (second : Width) × Emission Inputs saved word word [second]) := do
  let .ok (.two record second seed) := replay g first.header [producer, consumer] | none
  let moved ← emit? (fromTwo record second seed) request
  pure ⟨_, _, moved⟩

structure Observation where
  physicalIndex : Nat
  physicalSaves : List Nat
  packets : List (List Nat)
  readsExitOccurrence : Bool
  runs : List (Option Nat)
  appendRuns : List (Option Nat)
  deriving BEq, Repr

/-- Origin 5 reads the older save, then origin 2 still reads that same
    older save after the insertion. Both feedbacks use logical packet order. -/
def observe : Option Observation := do
  let ⟨_, _, moved⟩ ← nominate? loopWithOlderSave ⟨5, 1⟩
  let cfg := moved.cfg
  let inputs := input 2 10 1
  let .inl entry := cfg.entry.eval evalOp (fun term env => Terminator.eval env term) inputs | none
  let step := fun (frame : Frame _) =>
    (cfg.block frame.label).eval evalOp (fun term env => Terminator.eval env term) (frame.args.append inputs)
  let .inl once := step entry | none
  let .inl twice := step once | none
  let .inl exit := step twice | none
  let readsExit := match moved.append.candidate.uses with
    | [.phi (some ⟨_, .header⟩) .onFalse 0] => true
    | _ => false
  let runs := fun code => [3, 4, 5].map fun fuel =>
    (code.run evalOp fuel inputs).map (fun env => (env.get .here).toNat)
  pure ⟨moved.splice.inserted.index, (words (moved.splice.leading.eval inputs)).take 3,
    [entry, once, twice, exit].map (fun frame => words frame.args), readsExit, runs cfg, runs moved.append.next.cfg⟩

/-- An immutable-only candidate can cross both old saves. Report its
    physical index and the newest-first order of all three definitions. -/
def beforeBoth : Option (Nat × List Nat) := do
  let ⟨_, _, moved⟩ ← nominate? (loopWith false true) ⟨5, 0⟩
  pure (moved.splice.inserted.index, (words (moved.splice.leading.eval (input 4 12 1))).take 3)

/-- Refuse a cut before a saved producer, a latch operand, and a stale origin. -/
def refused : List Bool :=
  [(nominate? loopWithOlderSave ⟨5, 0⟩).isNone,
    (nominate? loop ⟨5, 1⟩).isNone,
    (nominate? loopWithOlderSave ⟨0, 1⟩).isNone,
    (nominate? loopWithOlderSave ⟨2, 1⟩).isNone]

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Example
