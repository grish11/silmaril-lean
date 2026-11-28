module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Defs

/-! # Checked replay for the zero-, one- and two-save hoist corridor -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay

open Silmaril.MLIR.Arith (Var Width)
open Silmaril.MLIR.CF (Cfg)
open Header.Earlier (Operation operations)
open Header.Sequence (State)
open Loop.MLIR.CF (Program TargetOp lower)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}

/-- Original binding identity and cut in the current preheader. The block
is implicit because this replay profile only inserts in the preheader. -/
structure Nomination where
  origin : Nat
  cut : Nat
  deriving DecidableEq, Repr

inductive Reason where
  | wrongCut (expected : Nat)
  | rejected
  | capacity
  deriving DecidableEq, Repr

inductive Refusal where
  | header
  | nomination (position : Nat) (request : Nomination) (reason : Reason)
  deriving DecidableEq, Repr

/-- The cut is in the CFG before the move. The origin list describes the
emitted header after removal at the resolved current index. -/
structure First (Input : List Width) (carried result : Width) where
  nomination : Nomination
  index : Nat
  cut : Point (SourceLabel carried result)
  output : Output Input carried result
  origins : List Nat

inductive Snapshot (Input : List Width) (carried result : Width) where
  | zero (state : State Input carried result)
  | one (first : First Input carried result)
  | two (first : First Input carried result) (second : Nomination)
      (moved : AfterReorder.Second.Emit.Emission Input carried result)

def Snapshot.Labels : Snapshot Input carried result → List Width → Type
  | .zero _ => SourceLabel carried result
  | .one first => Label first.output.1 carried result
  | .two _ _ moved => Label moved.prepared.intermediate.1 carried result [moved.prepared.consumer.width]

def Snapshot.cfg : (state : Snapshot Input carried result) → Cfg TargetOp state.Labels Input [result]
  | .zero state => state.cfg
  | .one first => first.output.2
  | .two _ _ moved => moved.cfg

def Snapshot.origins : Snapshot Input carried result → List Nat
  | .zero state => state.origins
  | .one first => first.origins
  | .two _ _ moved => moved.prepared.origins.eraseIdx moved.prepared.index

def Snapshot.headerOperations : Snapshot Input carried result → List Operation
  | .zero state => operations (state.cfg.block .header)
  | .one first => operations (first.output.2.block .header)
  | .two _ _ moved => operations (moved.cfg.block .header)

def Snapshot.savedWidths : Snapshot Input carried result → List Width
  | .zero _ => []
  | .one first => [first.output.1]
  | .two _ _ moved => [moved.prepared.consumer.width, moved.prepared.intermediate.1]

/-- Original identities at the current CFG's typed saved positions. The
preheader's leading lets define these slots oldest first. -/
def Snapshot.savedSlots : (state : Snapshot Input carried result) → Saved.Slots state.savedWidths
  | .zero _ => .nil
  | .one first => .cons first.nomination.origin .nil
  | .two first second _ => .cons second.origin (.cons first.nomination.origin .nil)

/-- Locate an original identity in the current header or at a typed
saved position. A saved reference also determines its preheader cut. -/
def Snapshot.locate? (state : Snapshot Input carried result) (origin : Nat) :
    Option (Nat ⊕ ((w : Width) × Var state.savedWidths w)) :=
  match state.origins.idxOf? origin with
  | some index => some (.inl index)
  | none => (state.savedSlots.find? origin).map .inr

/-- The two-save profile retains the second cut in the one-save CFG's
label family. Its numeric coordinate is checked when advancing. -/
def secondCut (nomination : Nomination) (moved : AfterReorder.Second.Emit.Emission Input carried result) :
    Point (Label moved.prepared.intermediate.1 carried result) :=
  ⟨none, nomination.cut⟩

/-- Apply the first checked hoist to the current reordered header. -/
def first? (state : State Input carried result) (nomination : Nomination) :
    Except Reason (First Input carried result) :=
  if nomination.cut = 0 then
    match AfterReorder.resolveMove? state nomination.origin with
    | some (index, cut, output) => .ok ⟨nomination, index, cut, output, state.origins.eraseIdx index⟩
    | none => .error .rejected
  else .error (.wrongCut 0)

/-- Resolve and check the consumer on the stored first CFG. -/
def second? (first : First Input carried result) (nomination : Nomination) :
    Except Reason (AfterReorder.Second.Emit.Emission Input carried result) :=
  if nomination.cut = 1 then
    match AfterReorder.Second.prepareOn? first.output first.origins nomination.origin with
    | some prepared =>
      match AfterReorder.Second.Emit.emit? prepared with
      | some cfg => .ok ⟨prepared, cfg⟩
      | none => .error .rejected
    | none => .error .rejected
  else .error (.wrongCut 1)

def advance (state : Snapshot Input carried result) (nomination : Nomination) :
    Except Reason (Snapshot Input carried result) :=
  match state with
  | .zero before => (first? before nomination).map .one
  | .one first => (second? first nomination).map (.two first nomination)
  | .two .. => .error .capacity

/-- Process in order, returning the first failed nomination and no CFG
on error. The position counts nominations, starting from zero. -/
def run (state : Snapshot Input carried result) (position : Nat) :
    List Nomination → Except Refusal (Snapshot Input carried result)
  | [] => .ok state
  | nomination :: rest =>
    match advance state nomination with
    | .ok next => run next (position + 1) rest
    | .error reason => .error (.nomination position nomination reason)

/-- Replay an optional checked header reordering and then its nominated
cross-block hoists. An empty header and nomination list returns the
original lowering. -/
def replay (g : Program Input carried result entrySigs headerSigs)
    (header : List Header.Pair.Request) (nominations : List Nomination) :
    Except Refusal (Snapshot Input carried result) :=
  match Header.Sequence.run? (Header.Sequence.initial (lower g)) header with
  | some before => run (.zero before) 0 nominations
  | none => .error .header

/-- Each accepted nomination is attached to the step that checked it on
the preceding snapshot. -/
inductive Trace (before : State Input carried result) :
    List Nomination → Snapshot Input carried result → Prop where
  | zero : Trace before [] (.zero before)
  | one {nomination first} (moved : first? before nomination = .ok first) :
      Trace before [nomination] (.one first)
  | two {producer consumer first moved}
      (firstChecked : first? before producer = .ok first)
      (secondChecked : second? first consumer = .ok moved) :
      Trace before [producer, consumer] (.two first consumer moved)

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
