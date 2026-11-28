module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Example.Defs

/-! # Continue the actual two-save emission with a dependent third move -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Example

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Frame Terminator)
open Loop.MLIR.CF (Program evalOp)
open Corridor.Example (word byte predicate Inputs entrySigs input)
open AfterReorder.Second.Example (first)
open Replay.Example (producer consumer)

abbrev Schedule : List (List (Diamond.Ty Width)) := [[byte], [byte], [byte], [predicate], [byte], [byte]]

def loopWithReads (immutableSecond immutableThird olderOnly : Bool) :
    Program Inputs word word entrySigs Schedule where
  preheader := (AfterReorder.Second.Example.loop false).preheader
  header :=
    .cons (.arithmetic (.binary .addi))
      (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail (.tail .head))) .nil))
      (.cons (.arithmetic (.binary .addi))
        (.cons (.arg (.tail (.tail .head))) (.cons (.arg (.tail (.tail .head))) .nil))
        (.cons (.arithmetic (.binary .addi))
          (.cons (if immutableSecond then .arg .head else .output (1 : Fin 2) .head)
            (.cons (if immutableSecond then .arg .head else .arg (.tail (.tail .head))) .nil))
          (.cons (.ult word)
            (.cons (.arg (.tail (.tail (.tail .head)))) (.cons (.arg (.tail .head)) .nil))
            (.cons (.arithmetic (.binary .addi))
              (.cons (.output (0 : Fin 4) .head) (.cons (.output (2 : Fin 4) .head) .nil))
              (.cons (.arithmetic (.binary .addi))
                (.cons (if immutableThird || olderOnly then .arg .head else .output (2 : Fin 5) .head)
                  (.cons (if immutableThird then .arg (.tail (.tail .head)) else .output (1 : Fin 5) .head)
                    .nil)) .nil)))))
  phiInputs
    | .entry => (AfterReorder.Second.Example.loop false).phiInputs .entry
    | .backedge => .cons (.output (4 : Fin 6) .head) .nil
  predicate := .output (3 : Fin 6) .head
  result := .output (5 : Fin 6) .head

/-- Bindings 2 and 5 can read the prior results or use immutable inputs.
The all-dependent variant uses both prior saved results in binding 5. -/
def loopWith (immutableSecond immutableThird : Bool) : Program Inputs word word entrySigs Schedule :=
  loopWithReads immutableSecond immutableThird false

/-- Binding 5 reads only the older saved value and an immutable input. -/
def loopWithOlderSave : Program Inputs word word entrySigs Schedule :=
  loopWithReads false false true

def loop := loopWith false false

def third : Nomination := ⟨5, 2⟩

def words : {widths : List Width} → Env widths → List Nat
  | _, .nil => []
  | _, .cons word rest => word.toNat :: words rest

/-- The observations include actual entry, two feedbacks, exact exit and
finite runs before and after the third rewrite. -/
def observe (requests : List Nomination) :
    Except Refusal (Option (List Nat × Nat × List (List Nat) × List (Option Nat))) := do
  let out ← replayAll loop first.header (producer :: consumer :: requests)
  let cfg := out.cfg
  let inputs := input 2 10 1
  pure do
    let .inl entry := cfg.entry.eval evalOp (fun term env => Terminator.eval env term) inputs | none
    let step := fun (frame : Frame _) =>
      (cfg.block frame.label).eval evalOp (fun term env => Terminator.eval env term) (frame.args.append inputs)
    let .inl once := step entry | none
    let .inl twice := step once | none
    let .inl exit := step twice | none
    pure (out.origins, (shape cfg none).bindings, [entry, once, twice, exit].map (fun frame => words frame.args),
      [3, 4, 5].map fun fuel => (cfg.run evalOp fuel inputs).map (fun env => (env.get .here).toNat))

/-- Check the nomination on the two-save CFG and show its current index and operand cuts. -/
def sites : Except Reason (Nat × List Nat) := do
  let .ok (.two firstMove secondMove two) := replay loop first.header [producer, consumer] | throw .rejected
  let edited ← emit (fromTwo firstMove secondMove two) third
  pure (edited.index, edited.candidate.operands.map Point.cut)

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Example
