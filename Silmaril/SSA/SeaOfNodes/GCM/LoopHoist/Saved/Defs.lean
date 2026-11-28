module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Defs

/-! # Typed saved slots and a one-slot extension of a loop packet -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Cfg Frame Terminator)
open Loop.MLIR.CF (TargetOp evalOp)

variable {Input extra widths : List Width} {saved carried result w : Width}

/-- Original identities in header packet order, newest save first. The
preheader defines these values in the reverse order in its leading lets. -/
inductive Slots : List Width → Type where
  | nil : Slots []
  | cons {w : Width} {widths : List Width} (origin : Nat) (rest : Slots widths) : Slots (w :: widths)

def Slots.origins : {widths : List Width} → Slots widths → List Nat
  | _, .nil => []
  | _, .cons origin rest => origin :: rest.origins

def Slots.origin : {widths : List Width} → Slots widths → {w : Width} → Var widths w → Nat
  | _, .cons origin _, _, .here => origin
  | _, .cons _ rest, _, .there ref => rest.origin ref

def Slots.find? (origin : Nat) : {widths : List Width} → Slots widths → Option ((w : Width) × Var widths w)
  | _, .nil => none
  | _, .cons current rest =>
    if origin == current then some ⟨_, .here⟩
    else (rest.find? origin).map fun ⟨_, ref⟩ => ⟨_, .there ref⟩

/-- Cut after the defining let for a saved slot, or zero for an immutable
input. These coordinates count the contiguous leading saves. -/
def definitionCut (widths : List Width) (ref : Var (widths ++ Input) w) : Nat :=
  widths.length - ref.index

/-- Interpret a typed saved reference in a block scope with more variables
after the saved prefix. Its address is unchanged. -/
def prefixRef (suffix : List Width) : {widths : List Width} → Var widths w → Var (widths ++ suffix) w
  | _, .here => .here
  | _, .there ref => .there (prefixRef suffix ref)

/-- In the header environment, the latch is local and all saved slots
and immutable inputs can be captured into the current preheader. -/
def origins : (widths : List Width) → {w : Width} →
    Var ((widths ++ [carried]) ++ Input) w → Var (widths ++ Input) w ⊕ Nat
  | [], _, ref => match ref with
    | .here => .inr 0
    | .there ref => .inl ref
  | _ :: rest, _, ref => match ref with
    | .here => .inl .here
    | .there ref => (origins rest ref).map Var.there id

/-- Project immutable inputs out of a saved-prefix scope. A reference
to any saved slot remains local to that scope. -/
def immutableOrigins : (widths : List Width) → {w : Width} →
    Var (widths ++ Input) w → Var Input w ⊕ Nat
  | [], _, ref => .inl ref
  | _ :: _, _, .here => .inr 0
  | _ :: rest, _, .there ref => immutableOrigins rest ref

/-- Extend the header packet and preserve the old arguments in order.
An exit keeps its complete argument tuple. -/
def prependFrame (value : BitVec w.val) :
    Frame (Label saved carried result extra) → Frame (Label saved carried result (w :: extra))
  | ⟨.header, args⟩ => ⟨.header, .cons value args⟩
  | ⟨.exit, args⟩ => ⟨.exit, args⟩

/-- One checked edit inserts a saved slot. Equations compare actual
evaluated transfers on the pre-step invariant packets. -/
structure StepRoutes
    (source : Cfg TargetOp (Label saved carried result extra) Input [result])
    (target : Cfg TargetOp (Label saved carried result (w :: extra)) Input [result])
    (input : Env Input) (values : Env (extra ++ [saved])) (value : BitVec w.val) : Prop where
  entry :
    target.entry.eval evalOp (fun term env => Terminator.eval env term) input =
      (source.entry.eval evalOp (fun term env => Terminator.eval env term) input).map (prependFrame value) id
  block : ∀ frame : Frame (SourceLabel carried result),
    let old := carryFrameWith values frame
    let new := prependFrame value old
    (target.block new.label).eval evalOp (fun term env => Terminator.eval env term) (new.args.append input) =
      ((source.block old.label).eval evalOp (fun term env => Terminator.eval env term) (old.args.append input)).map
        (prependFrame value) id

/-- The current CFG routes a typed saved prefix over the unsaved CFG,
and the saved and surviving header identities account for the inventory. -/
structure Invariant
    (base : Cfg TargetOp (SourceLabel carried result) Input [result])
    (cfg : Cfg TargetOp (Label saved carried result extra) Input [result])
    (inventory header : List Nat) (slots : Slots (extra ++ [saved]))
    (input : Env Input) (values : Env (extra ++ [saved])) : Prop where
  partition : (slots.origins ++ header).Perm inventory
  routes : RoutesWith base cfg input values

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved
