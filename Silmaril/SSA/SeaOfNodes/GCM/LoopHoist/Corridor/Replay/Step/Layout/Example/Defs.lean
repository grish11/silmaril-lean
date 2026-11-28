module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.Example.Defs

/-! # Three placements with live dependencies across physical slot updates -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Example

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Frame Terminator)
open Loop.MLIR.CF (Program evalOp)
open Corridor.Example (Inputs word byte entrySigs input)
open AfterReorder.Second.Example (first)
open Replay.Example (producer consumer)
open Step.Example (words)
open Earlier.Follow.Example (Chain)

def appendFlow {Data : Type} {op : Diamond.Signature Data} {args : List (Diamond.Ty Data)}
    {suffix : List (List (Diamond.Ty Data))} :
    {past sigs : List (List (Diamond.Ty Data))} → Diamond.Dataflow op args past sigs →
      Diamond.Dataflow op args (RVSDG.extend past sigs) suffix → Diamond.Dataflow op args past (sigs ++ suffix)
  | _, _, .nil, tail => tail
  | _, _, .cons node reads rest, tail => .cons node reads (appendFlow rest tail)

/-- Origin 7 reads the live results of the first two physical splices. -/
def loop : Program Inputs word word entrySigs (Chain ++ [[byte]]) where
  preheader := Earlier.Follow.Example.loop.preheader
  header := appendFlow Earlier.Follow.Example.loop.header
    (.cons (.arithmetic (.binary .addi))
      (.cons (.output (6 : Fin 7) .head) (.cons (.output (5 : Fin 7) .head) .nil)) .nil)
  phiInputs
    | .entry => Earlier.Follow.Example.loop.phiInputs .entry
    | .backedge => .cons (.output (4 : Fin 8) .head) .nil
  predicate := .output (3 : Fin 8) .head
  result := .output (7 : Fin 8) .head

def seed? : Option ((saved : Width) × (second : Width) × State Inputs saved word word [second]) := do
  let .ok (.two record middle seed) := replay loop first.header [producer, consumer] | none
  let state ← initial? (Step.fromTwo record middle seed)
  pure ⟨_, _, state⟩

def requests : List Nomination := [⟨5, 1⟩, ⟨6, 2⟩, ⟨7, 3⟩]

structure Observation where
  logicalCuts : List Nat
  physicalCuts : List Nat
  slots : List (Option Nat)
  physicalSaves : List Nat
  packets : List (List Nat)
  exitOccurrence : Bool
  runs : List (Option Nat)
  appendRuns : List (Option Nat)
  deriving BEq, Repr

def observe : Option Observation := do
  let ⟨_, _, seed⟩ ← seed?
  let .ok ⟨_, prior⟩ := run seed 2 (requests.take 2) | none
  let third ← emit? prior ⟨7, 3⟩
  let .ok ⟨_, final⟩ := run seed 2 requests | none
  let cfg := final.cfg
  let inputs := input 2 10 1
  let .inl entry := cfg.entry.eval evalOp (fun term env => Terminator.eval env term) inputs | none
  let step := fun (frame : Frame _) =>
    (cfg.block frame.label).eval evalOp (fun term env => Terminator.eval env term) (frame.args.append inputs)
  let .inl once := step entry | none
  let .inl twice := step once | none
  let .inl exit := step twice | none
  let readsExit := match third.append.candidate.uses with
    | [.phi (some ⟨_, .header⟩) .onFalse 0] => true
    | _ => false
  let runs := fun code => [3, 4, 5].map fun fuel =>
    (code.run evalOp fuel inputs).map (fun env => (env.get .here).toNat)
  pure ⟨third.append.candidate.operands.map Point.cut,
    (prior.atLayout third.append.candidate).operands.map Point.cut,
    [7, 6, 5, 2, 1].map final.physicalSlot?, (words (final.leading.eval inputs)).take 5,
    [entry, once, twice, exit].map (fun frame => words frame.args), readsExit, runs cfg, runs final.reference.cfg⟩

/-- Check the third nomination after both accepted splices. -/
def refusal (request : Nomination) : Option Refusal := do
  let ⟨_, _, seed⟩ ← seed?
  match run seed 2 (requests.take 2 ++ [request]) with
  | .ok _ => none
  | .error reason => some reason

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Example
