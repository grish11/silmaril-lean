module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Defs

/-! # Checked availability for a second preheader binding -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block)
open Silmaril.MLIR.Pure (Operands)
open Loop.MLIR.CF (Program TargetOp evalOp lower)

variable {Input Γ extra : List Width} {saved carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}

def savedHeader : BlockId (Label saved carried result extra) := some ⟨_, .header⟩

/-- Read the saved argument as the new preheader result, the latch as
local, and the remaining arguments as the immutable inputs. -/
def savedOrigins : Origins (saved :: Input) (saved :: carried :: Input) :=
  Saved.origins [saved]

/-- A candidate captures its operands in the current saved-prefix scope. -/
structure Candidate (Input : List Width) (saved carried result : Width) (extra : List Width := []) where
  width : Width
  args : List Width
  op : TargetOp args width
  inputs : Operands ((extra ++ [saved]) ++ Input) args
  operands : List (Point (Label saved carried result extra))
  uses : List (Use (Label saved carried result extra))

/-- First cut after all captured definitions. Immutable inputs contribute
zero, including the empty operand list. -/
def Candidate.earliestCut (candidate : Candidate Input saved carried result extra) : Nat :=
  ((candidate.operands.map Point.cut).max?).getD 0

/-- Operand availability within the saved prefix. Uses are checked separately. -/
def Candidate.operandCut? (candidate : Candidate Input saved carried result extra) (cut : Nat) : Bool :=
  decide (candidate.earliestCut ≤ cut ∧ cut ≤ (extra ++ [saved]).length)

/-- Each operand's defining cut in the saved prefix or the immutable inputs. -/
def prefixSites : {args : List Width} → Operands ((extra ++ [saved]) ++ Input) args →
    List (Point (Label saved carried result extra))
  | _, .nil => []
  | _, .cons ref tail => ⟨none, Saved.definitionCut (extra ++ [saved]) ref⟩ :: prefixSites tail

abbrev savedSites {args : List Width} (operands : Operands (saved :: Input) args) :
    List (Point (Label saved carried result)) := prefixSites operands

def readsSaved {args : List Width} (operands : Operands Γ args) : Nat → Bool
  | 0 => false
  | n + 1 => !(positions n operands 0).isEmpty || readsSaved operands n

/-- Recover the original typed operands for a capture that reads only
immutable inputs. -/
def Candidate.immutableInputs? (candidate : Candidate Input saved carried result extra) :
    Option (Operands Input candidate.args) :=
  captureOrigins? (Saved.immutableOrigins (extra ++ [saved])) candidate.inputs

/-- Read the current typed binding. Capture accepts saved slots and
immutable inputs. The latch and preceding header bindings are local. -/
def findCaptured? : (index cut : Nat) → {Γ : List Width} → Origins ((extra ++ [saved]) ++ Input) Γ →
    Block TargetOp (Label saved carried result extra) Γ [result] →
    Option (Candidate Input saved carried result extra)
  | 0, cut, _, origins, .letOp op operands rest => do
    let inputs ← captureOrigins? origins operands
    pure ⟨_, _, op, inputs, prefixSites inputs, useSitesAt savedHeader 0 (cut + 1) rest⟩
  | index + 1, cut, _, origins, .letOp _ _ rest =>
    findCaptured? index (cut + 1) (afterBinding origins (cut + 1)) rest
  | _, _, _, _, .terminator _ => none

/-- Restrict the capture to the original saved-dependent admission profile. -/
def findCandidate? (index cut : Nat) {Γ : List Width} (origins : Origins ((extra ++ [saved]) ++ Input) Γ)
    (code : Block TargetOp (Label saved carried result extra) Γ [result]) :
    Option (Candidate Input saved carried result extra) :=
  (findCaptured? index cut origins code).filter fun candidate =>
    readsSaved candidate.inputs (extra ++ [saved]).length

/-- Return the value of the nominated binding in a single header activation. -/
def valueAt? : Nat → {Γ : List Width} → Block TargetOp (Label saved carried result extra) Γ [result] →
    Env Γ → Option ((w : Width) × BitVec w.val)
  | 0, _, .letOp op operands _, env => some ⟨_, evalOp op (operands.eval env)⟩
  | index + 1, _, .letOp op operands rest, env =>
    valueAt? index rest (.cons (evalOp op (operands.eval env)) env)
  | _, _, .terminator _, _ => none

def isExit (target : Target (Label saved carried result extra)) : Bool :=
  match target with
  | ⟨_, .exit⟩ => true
  | ⟨_, .header⟩ => false

def targetDecEqWith : DecidableEq (Target (Label saved carried result extra)) :=
  fun a b => decidable_of_iff (isExit a = isExit b)
    ⟨by rcases a with ⟨_, a⟩; rcases b with ⟨_, b⟩; cases a <;> cases b <;> simp_all [isExit],
      congrArg isExit⟩

abbrev targetDecEq : DecidableEq (Target (Label saved carried result)) := targetDecEqWith

def intermediateBlocks : List (Target (Label saved carried result extra)) :=
  [⟨_, .header⟩, ⟨_, .exit⟩]

/-- Check a cut in the saved prefix against the actual ordinary and incoming
Φ uses, retaining the source terminator slot for each Φ use. -/
def checkPrefixCut (cfg : Silmaril.MLIR.CF.Cfg TargetOp (Label saved carried result extra) Input [result])
    (candidate : Candidate Input saved carried result extra) (cut : Nat) : Bool :=
  let _ := targetDecEqWith (saved := saved) (carried := carried) (result := result) (extra := extra)
  candidate.operandCut? cut &&
    GCM.Dominance.Placement.checkCut cfg intermediateBlocks candidate.operands candidate.uses ⟨none, cut⟩

/-- The current replay emitter inserts at the end of the saved prefix. -/
def checkConsumer (cfg : Silmaril.MLIR.CF.Cfg TargetOp (Label saved carried result extra) Input [result])
    (candidate : Candidate Input saved carried result extra) : Bool :=
  checkPrefixCut cfg candidate (extra ++ [saved]).length

structure Prepared (Input : List Width) (carried result : Width) where
  intermediate : Output Input carried result
  origins : List Nat
  index : Nat
  consumer : Candidate Input intermediate.1 carried result

/-- Check the consumer at cut one using the actual one-save CFG and its
remaining header order. -/
def prepareOn? (intermediate : Output Input carried result) (origins : List Nat)
    (consumerOrigin : Nat) : Option (Prepared Input carried result) := do
  let index ← origins.idxOf? consumerOrigin
  let consumer ← findCaptured? index 0 savedOrigins (intermediate.2.block .header)
  if checkConsumer intermediate.2 consumer then
    pure ⟨intermediate, origins, index, consumer⟩
  else none

/-- Replay the first plan, delete the first original identity, and check the
second request at cut one of the actual intermediate preheader. -/
def prepare? (g : Program Input carried result entrySigs headerSigs)
    (first : AfterReorder.Plan) (consumerOrigin : Nat) : Option (Prepared Input carried result) := do
  let state ← Header.Sequence.run? (Header.Sequence.initial (lower g)) first.header
  let (firstIndex, _, intermediate) ← AfterReorder.resolveMove? state first.hoistOrigin
  prepareOn? intermediate (state.origins.eraseIdx firstIndex) consumerOrigin

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second
