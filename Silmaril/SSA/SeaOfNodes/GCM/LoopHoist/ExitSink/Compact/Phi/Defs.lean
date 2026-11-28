module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Defs
public import Silmaril.SSA.PhiView.Defs

/-! # Read positional Φ rows from the compactable CF exit's predecessors -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi

open Silmaril.MLIR.Arith (Atom Env Var Width word)
open Silmaril.MLIR.CF (Block Edge Frame Terminator)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.Isotope (Value)
open Loop.MLIR.CF (TargetOp evalOp)
open Corridor.Header.Typed (edgePackets)

variable {Input bank full Γ Δ : List Width} {saved carried result : Width} {extra : List Width}

/-- A compactable exit returns. Its incoming transfers originate in the
entry or header, and each predecessor can have multiple successor slots. -/
inductive Predecessor where
  | entry
  | header
  deriving DecidableEq, Repr

abbrev Occurrence := Predecessor × EdgeSlot

def Predecessor.scope (pred : Predecessor) (input bank : List Width) : List Width :=
  match pred with
  | .entry => input
  | .header => bank ++ input

def predecessor (cfg : TargetCfg Input saved carried result extra full) (pred : Predecessor) :
    Block TargetOp (ExitLabel (SavedBank saved carried extra) full)
      (pred.scope Input (SavedBank saved carried extra)) [result] :=
  match pred with
  | .entry => cfg.entry
  | .header => cfg.block .header

def terminal {Term : List Width → Type} : {Γ : List Width} →
    Silmaril.MLIR.Pure.Code TargetOp Term Γ → (scope : List Width) × Term scope
  | _, .terminator term => ⟨_, term⟩
  | _, .letOp _ _ rest => terminal rest

def terminalEnv {Term : List Width → Type} : {Γ : List Width} →
    (code : Silmaril.MLIR.Pure.Code TargetOp Term Γ) → Env Γ → Env (terminal code).1
  | _, .terminator _, env => env
  | _, .letOp op args rest, env => terminalEnv rest (.cons (evalOp op (args.eval env)) env)

/-- Select the slot before testing its destination, so parallel arrivals
with the same source and destination remain distinct. -/
def atSlot? : Terminator (ExitLabel bank full) Δ Γ → EdgeSlot → Option (Edge (ExitLabel bank full) Γ)
  | .br edge, .jump => some edge
  | .condBr _ yes _, .onTrue => some yes
  | .condBr _ _ no, .onFalse => some no
  | _, _ => none

def exitOperands? : Edge (ExitLabel bank full) Γ → Option (Operands Γ full)
  | ⟨.exit, args⟩ => some args
  | ⟨.header, _⟩ => none

def exitValues? : Frame (ExitLabel bank full) → Option (Env full)
  | ⟨.exit, values⟩ => some values
  | ⟨.header, _⟩ => none

variable (cfg : TargetCfg Input saved carried result extra full)

abbrev TerminalScope (pred : Predecessor) := (terminal (predecessor cfg pred)).1

def operandsAt? (occ : Occurrence) : Option (Operands (TerminalScope cfg occ.1) full) :=
  (atSlot? (terminal (predecessor cfg occ.1)).2 occ.2).bind exitOperands?

/-- An occurrence's typed row, with its own terminal scope. -/
def rowAt? (occ : Occurrence) : Option ((scope : List Width) × Operands scope full) :=
  (operandsAt? cfg occ).map (fun args => ⟨_, args⟩)

/-- Look up the typed exit packet in the actual CF block's occurrence
observations, in the environment at block entry. -/
def packetAt? (occ : Occurrence) (env : Env (occ.1.scope Input (SavedBank saved carried extra))) :
    Option (Env full) :=
  ((predecessor cfg occ.1).eval evalOp edgePackets env).findSome? fun (slot, frame) =>
    if slot = occ.2 then exitValues? frame else none

abbrev Incoming := { occ : Occurrence // (operandsAt? cfg occ).isSome }

variable {cfg}

def Incoming.operands (row : Incoming cfg) : Operands (TerminalScope cfg row.val.1) full :=
  (operandsAt? cfg row.val).get row.property

abbrev Types (widths : List Width) := widths.map Silmaril.Ty.base

def operand {w : Width} (v : Var Γ w) : PhiView.Operand (Types Γ) (.base w) :=
  ⟨v.index, by induction v with | here => rfl | there _ ih => exact ih⟩

def arguments : {Δ : List Width} → Operands Γ Δ → PhiView.Arguments (Types Γ) (Types Δ)
  | _, .nil => fun i => (Nat.not_lt_zero _ i.isLt).elim
  | _, .cons v rest => fun i => Fin.cases (operand v) (arguments rest) i

def pack : {Δ : List Width} → Env Δ → Value Atom
  | _, .nil => .unit
  | _, .cons value rest => .pair (word value) (pack rest)

variable (cfg)

/-- A local explicit Φ view of the exit transfers. Each source index is
the actual CF predecessor and slot, and label zero denotes this exit. -/
def terminators (row : Incoming cfg) : Silmaril.Isotope.LambdaSSA.Terminator Silmaril.MLIR.Arith.Prim :=
  .br 0 (PhiView.packTerm (arguments row.operands))

def typing : PhiView.SourceTyping (τ := Silmaril.Ty Width) (terminators cfg) where
  context row := Types (TerminalScope cfg row.val.1)
  cases _ := .jump

def view : PhiView.View (typing cfg) (fun _ => Types full) :=
  PhiView.ofBlockArgs (fun ⟨row, .jump⟩ => ⟨arguments row.operands, rfl⟩)

variable {cfg}

def Incoming.edge (row : Incoming cfg) : PhiView.EdgeOcc (terminators cfg) := ⟨row, .jump⟩

def Incoming.latch (row : Incoming cfg) (env : Env (row.val.1.scope Input (SavedBank saved carried extra))) :
    Value Atom :=
  PhiView.latch (view cfg) row.edge (terminalEnv (predecessor cfg row.val.1) env).toLambdaSSA

/-- Latch the certified explicit Φ row at the given actual CF occurrence. -/
def latchAt? (cfg : TargetCfg Input saved carried result extra full) (occ : Occurrence)
    (env : Env (occ.1.scope Input (SavedBank saved carried extra))) : Option (Value Atom) :=
  if present : (operandsAt? cfg occ).isSome then some (Incoming.latch (cfg := cfg) ⟨occ, present⟩ env)
  else none

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi
