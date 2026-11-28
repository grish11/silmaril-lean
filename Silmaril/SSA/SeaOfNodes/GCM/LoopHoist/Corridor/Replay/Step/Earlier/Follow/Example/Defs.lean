module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Example.Defs

/-! # Two earlier placements with a remapped dependency -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.Example

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Frame Terminator)
open Loop.MLIR.CF (Program evalOp)
open Corridor.Example (Inputs word byte entrySigs input)
open AfterReorder.Second.Example (first)
open Replay.Example (producer consumer)
open Step.Example (Schedule words)

abbrev Chain := Schedule ++ [[byte]]

/-- Origin 5 reads the first save. Origin 6 reads origin 5, so its earliest
    cut changes when origin 5 moves between the two prior saves. -/
def loop : Program Inputs word word entrySigs Chain where
  preheader := Step.Example.loopWithOlderSave.preheader
  header :=
    .cons (.arithmetic (.binary .addi))
      (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail (.tail .head))) .nil))
      (.cons (.arithmetic (.binary .addi))
        (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail .head))) .nil))
        (.cons (.arithmetic (.binary .addi))
          (.cons (.output (1 : Fin 2) .head) (.cons (.arg (.tail (.tail .head))) .nil))
          (.cons (.ult word)
            (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail .head)) .nil))
            (.cons (.arithmetic (.binary .addi))
              (.cons (.output (0 : Fin 4) .head) (.cons (.output (2 : Fin 4) .head) .nil))
              (.cons (.arithmetic (.binary .addi))
                (.cons (.arg .head) (.cons (.output (1 : Fin 5) .head) .nil))
                (.cons (.arithmetic (.binary .addi))
                  (.cons (.output (5 : Fin 6) .head) (.cons (.arg (.tail (.tail .head))) .nil)) .nil))))))
  phiInputs
    | .entry => Step.Example.loopWithOlderSave.phiInputs .entry
    | .backedge => .cons (.output (4 : Fin 7) .head) .nil
  predicate := .output (3 : Fin 7) .head
  result := .output (6 : Fin 7) .head

def follow? (request : Nomination) :
    Option ((saved : Width) × (second : Width) ×
      (prior : Earlier.Emission Inputs saved word word [second]) × Emission prior) := do
  let .ok (.two record middle seed) := replay loop first.header [producer, consumer] | none
  let prior ← Earlier.emit? (Step.fromTwo record middle seed) ⟨5, 1⟩
  let moved ← emit? prior request
  pure ⟨_, _, prior, moved⟩

structure Observation where
  logicalOperandCuts : List Nat
  physicalOperandCuts : List Nat
  onFalseExitUse : Bool
  physicalSaves : List Nat
  packets : List (List Nat)
  runs : List (Option Nat)
  appendRuns : List (Option Nat)
  deriving BEq, Repr

/-- Cut 2 is before the last physical save and after the remapped operand.
    The append-order witness places that operand at cut 3. -/
def observe : Option Observation := do
  let ⟨_, _, prior, moved⟩ ← follow? ⟨6, 2⟩
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
  pure ⟨moved.append.candidate.operands.map Point.cut,
    (atLayout prior moved.append.candidate).operands.map Point.cut, readsExit,
    (words (moved.splice.leading.eval inputs)).take 4,
    [entry, once, twice, exit].map (fun frame => words frame.args), runs cfg, runs moved.append.next.cfg⟩

/-- Reject a cut before the physically remapped producer, a stale origin,
    and an operand that depends on the latch. -/
def refused : List Bool :=
  [(follow? ⟨6, 1⟩).isNone, (follow? ⟨5, 2⟩).isNone, (follow? ⟨0, 2⟩).isNone]

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.Example
