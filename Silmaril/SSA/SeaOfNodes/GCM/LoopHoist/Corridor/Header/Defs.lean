module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Defs

/-! # Move a nominated binding earlier by one position in the typed loop header -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Cfg Edge Frame Terminator)
open Silmaril.MLIR.SCF.For (renameOperands)
open Loop.MLIR.CF (Program TargetOp lower)

variable {Input Γ Δ : List Width} {carried result first second : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}

/-- The two results change de Bruijn positions; every older reference stays put. -/
def swapNames : Rename (second :: first :: Γ) (first :: second :: Γ)
  | _, .here => .there .here
  | _, .there .here => .here
  | _, .there (.there ref) => .there (.there ref)

/-- Reindex a suffix while retaining each branch slot, target and argument order. -/
def renameEdge (rename : Rename Γ Δ) (edge : Edge (SourceLabel carried result) Γ) :
    Edge (SourceLabel carried result) Δ :=
  ⟨edge.label, renameOperands rename edge.args⟩

def renameTerm (rename : Rename Γ Δ) :
    Terminator (SourceLabel carried result) [result] Γ →
      Terminator (SourceLabel carried result) [result] Δ
  | .br dest => .br (renameEdge rename dest)
  | .condBr test onTrue onFalse => .condBr (rename test)
      (renameEdge rename onTrue) (renameEdge rename onFalse)
  | .ret values => .ret (renameOperands rename values)

def renameSuffix : {Γ Δ : List Width} → Rename Γ Δ →
    Block TargetOp (SourceLabel carried result) Γ [result] →
      Block TargetOp (SourceLabel carried result) Δ [result]
  | _, _, rename, .terminator term => .terminator (renameTerm rename term)
  | _, _, rename, .letOp op operands rest =>
    .letOp op (renameOperands rename operands) (renameSuffix (under rename) rest)

/-- At a cut in the surviving prefix, exchange the next two bindings if the
second one's operands can be read without the first result. -/
def swapAt? : (insertion : Nat) → {Γ : List Width} →
    Block TargetOp (SourceLabel carried result) Γ [result] →
      Option (Block TargetOp (SourceLabel carried result) Γ [result])
  | 0, _, .letOp firstOp firstArgs (.letOp secondOp secondArgs rest) => do
    let earlierArgs ← capture? secondArgs
    pure (.letOp secondOp earlierArgs
      (.letOp firstOp (renameOperands Var.there firstArgs) (renameSuffix swapNames rest)))
  | n + 1, _, .letOp op operands rest => (swapAt? n rest).map (.letOp op operands)
  | _, _, _ => none

namespace Typed

variable {Labels : List Width → Type} {Result : List Width}

/-- Reindex an edge while retaining its typed target and argument order. -/
def renameEdge (rename : Rename Γ Δ) (edge : Edge Labels Γ) : Edge Labels Δ :=
  ⟨edge.label, renameOperands rename edge.args⟩

def renameTerm (rename : Rename Γ Δ) : Terminator Labels Result Γ → Terminator Labels Result Δ
  | .br dest => .br (renameEdge rename dest)
  | .condBr test onTrue onFalse => .condBr (rename test)
      (renameEdge rename onTrue) (renameEdge rename onFalse)
  | .ret values => .ret (renameOperands rename values)

def renameSuffix : {Γ Δ : List Width} → Rename Γ Δ →
    Block TargetOp Labels Γ Result → Block TargetOp Labels Δ Result
  | _, _, rename, .terminator term => .terminator (renameTerm rename term)
  | _, _, rename, .letOp op operands rest =>
    .letOp op (renameOperands rename operands) (renameSuffix (under rename) rest)

/-- Exchange two adjacent pure lets if the second can read its operands
    without the first result. Both terminator occurrences keep their slots. -/
def swapAt? : (insertion : Nat) → {Γ : List Width} →
    Block TargetOp Labels Γ Result → Option (Block TargetOp Labels Γ Result)
  | 0, _, .letOp firstOp firstArgs (.letOp secondOp secondArgs rest) => do
    let earlierArgs ← capture? secondArgs
    pure (.letOp secondOp earlierArgs
      (.letOp firstOp (renameOperands Var.there firstArgs) (renameSuffix swapNames rest)))
  | n + 1, _, .letOp op operands rest => (swapAt? n rest).map (.letOp op operands)
  | _, _, _ => none

/-- Read both incoming-edge argument packets by terminator occurrence,
    independently of which edge the guard takes. -/
def edgePackets (term : Terminator Labels Result Γ) (env : Env Γ) :
    List (EdgeSlot × Frame Labels) :=
  match term with
  | .br edge => [(.jump, edge.eval env)]
  | .condBr _ onTrue onFalse => [(.onTrue, onTrue.eval env), (.onFalse, onFalse.eval env)]
  | .ret _ => []

end Typed

/-- Translate a cut in the original binding list into an insertion index after
deleting binding `index`. The cuts immediately before and after it coincide. -/
def afterRemoval (index originalCut : Nat) : Nat :=
  originalCut - (if index < originalCut then 1 else 0)

/-- Keep the entry, exit, and every block argument type of the lowered CFG. -/
def withHeader (cfg : Cfg TargetOp (SourceLabel carried result) Input [result])
    (header : Block TargetOp (SourceLabel carried result) (carried :: Input) [result]) :
    Cfg TargetOp (SourceLabel carried result) Input [result] where
  entry := cfg.entry
  block
    | .header => header
    | .exit => cfg.block .exit

/-- Realize the selected header cut when its translated insertion index is
exactly one position earlier. The local typed check also guards the splice. -/
def moveAt? (cfg : Cfg TargetOp (SourceLabel carried result) Input [result])
    (index : Nat) (cut : Point (SourceLabel carried result)) :
    Option (Cfg TargetOp (SourceLabel carried result) Input [result]) :=
  let _ := sourceTargetDecEq carried result
  let insertion := afterRemoval index cut.cut
  if cut.block = headerId ∧ insertion + 1 = index then
    (swapAt? insertion (cfg.block .header)).map (withHeader cfg)
  else none

/-- Resolve and rank the nominated binding on the input CFG, then ask the
emitter to realize the chosen cut. -/
def pickAndEmit? (g : Program Input carried result entrySigs headerSigs) (index : Nat)
    (emit : Cfg TargetOp (SourceLabel carried result) Input [result] →
      Nat → Point (SourceLabel carried result) →
      Option (Cfg TargetOp (SourceLabel carried result) Input [result])) :
    Option (Point (SourceLabel carried result) × Cfg TargetOp (SourceLabel carried result) Input [result]) := do
  let cfg := lower g
  let ⟨_, binding⟩ ← findBinding index 0 headerOrigins (cfg.block .header)
  let cut ← chooseCut? g binding.operands binding.uses
  let moved ← emit cfg index cut
  pure (cut, moved)

/-- Try the selected adjacent earlier cut. Preheader scheduling uses the
existing `Corridor.pickAndHoist?` entry point. -/
def pickAndMove? (g : Program Input carried result entrySigs headerSigs) (index : Nat) :
    Option (Point (SourceLabel carried result) × Cfg TargetOp (SourceLabel carried result) Input [result]) :=
  pickAndEmit? g index moveAt?

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header
