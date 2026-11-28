module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs

/-! Remove the unused exit block after feedback-only pruning in the typed carried-bank CFG. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.DeleteExit

open PruneExit (InputFacts)
open Loop.MLIR.CF (TargetOp evalOp)
open Loop.MLIR.CF.Bank (Label)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Cfg Frame Terminator)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)

inductive HeaderLabel (carried : List Width) : List Width → Type where
  | header : HeaderLabel carried carried

def HeaderLabel.embed {carried : List Width} {result : Width} {args : List Width} :
    HeaderLabel carried args → Label carried result args
  | .header => .header

def embedFrame {carried : List Width} {result : Width} (frame : Frame (HeaderLabel carried)) :
    Frame (Label carried result) :=
  ⟨frame.label.embed, frame.args⟩

abbrev FullCfg (Γ carried : List Width) (result : Width) :=
  Cfg TargetOp (Label carried result) Γ [result]

abbrev HeaderCfg (Γ carried : List Width) (result : Width) :=
  Cfg TargetOp (HeaderLabel carried) Γ [result]

variable {Γ carried : List Width} {result : Width}

/-- Keep a direct header edge verbatim, changing only the label family. -/
def restrictTerm {Δ : List Width} :
    Terminator (Label carried result) [result] Δ → Option (Terminator (HeaderLabel carried) [result] Δ)
  | .br ⟨.header, operands⟩ => some (.br ⟨.header, operands⟩)
  | _ => none

/-- Retain every binding and check that the terminator targets only the header. -/
def restrictBlock : {Δ : List Width} →
    Block TargetOp (Label carried result) Δ [result] → Option (Block TargetOp (HeaderLabel carried) Δ [result])
  | _, .terminator term => (restrictTerm term).map .terminator
  | _, .letOp op operands rest => (restrictBlock rest).map (.letOp op operands)

/-- Accept precisely the two retained blocks with direct header edges.
The output has no exit label or exit block. -/
def delete (cfg : FullCfg Γ carried result) : Option (HeaderCfg Γ carried result) :=
  (restrictBlock cfg.entry).bind fun entry =>
    (restrictBlock (cfg.block .header)).map fun header => ⟨entry, fun | .header => header⟩

inductive Output (Γ carried : List Width) (result : Width) where
  | kept (cfg : FullCfg Γ carried result)
  | deleted (cfg : HeaderCfg Γ carried result)

def Output.run (output : Output Γ carried result) (fuel : Nat) (input : Env Γ) : Option (Env [result]) :=
  match output with
  | .kept cfg => cfg.run evalOp fuel input
  | .deleted cfg => cfg.run evalOp fuel input

noncomputable def Output.denotePart (output : Output Γ carried result) (input : Env Γ) : Part (Outcome [result]) :=
  match output with
  | .kept cfg => (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed cfg).denotePart evalOp input
  | .deleted cfg => (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed cfg).denotePart evalOp input

/-- Consume the unified pruning result. Refusal stays `none`. The exit branch
keeps its original CFG, and the feedback branch drops its unused exit block. -/
def rewrite {entrySigs headerSigs : List (List (Diamond.Ty Width))}
    (g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs) (facts : InputFacts Γ) :
    Option (Output Γ carried result) :=
  (Prune.rewrite g facts).map fun cfg =>
    match delete cfg with
    | some restricted => .deleted restricted
    | none => .kept cfg

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.DeleteExit
