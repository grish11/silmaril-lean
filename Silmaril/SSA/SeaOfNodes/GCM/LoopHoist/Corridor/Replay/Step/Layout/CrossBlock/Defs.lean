module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopForest.Defs

/-! # Check and rank a retained header cut and a physical preheader splice -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Block)
open Silmaril.MLIR.Pure (Operands)
open AfterReorder.Second (intermediateBlocks savedHeader targetDecEqWith)
open Loop.MLIR.CF (TargetOp)

variable {Input extra Γ : List Width} {saved carried result : Width}

def blockNumber : BlockId (Label saved carried result extra) → Nat
  | none => 0
  | some ⟨_, .header⟩ => 1
  | some ⟨_, .exit⟩ => 2

def blockAt : Nat → BlockId (Label saved carried result extra)
  | 1 => savedHeader
  | 2 => some ⟨_, .exit⟩
  | _ => none

theorem blockNumber_injective :
    Function.Injective (blockNumber : BlockId (Label saved carried result extra) → Nat) :=
  (show Function.LeftInverse blockAt blockNumber from by
    rintro (_ | ⟨_, label⟩) <;> first | rfl | cases label <;> rfl).injective

structure Control (state : Layout.State Input saved carried result extra) where
  tree : DominatorTree state.cfg
  complete : tree.Complete
  loops : List (LoopForest.HeaderLoop (Label saved carried result extra))
  checked : LoopForest.forest? tree intermediateBlocks = some loops

/-- Compute the actual dominance and loop forest on the physical CFG. -/
def Control.check? (state : Layout.State Input saved carried result extra) : Option (Control state) := do
  let _ := targetDecEqWith (saved := saved) (carried := carried) (result := result) (extra := extra)
  let tree ← GCM.Dominance.Tree.Synthesis.synthesize? state.cfg intermediateBlocks blockNumber blockNumber_injective
  match checked : LoopForest.forest? tree.1 intermediateBlocks with
  | none => none
  | some loops => some ⟨tree.1, tree.2, loops, checked⟩

def Control.depth {state : Layout.State Input saved carried result extra} (control : Control state) :
    BlockId (Label saved carried result extra) → Nat :=
  LoopForest.depth control.tree control.loops

structure HeaderSites (Labels : List Width → Type) where
  operands : List (Point Labels)
  uses : List (Use Labels)

/-- Saved and immutable operands use their physical preheader definitions.
    The latch and previous header lets remain at their actual local cuts. -/
def operandSites (state : Layout.State Input saved carried result extra)
    (origins : Origins ((extra ++ [saved]) ++ Input) Γ) :
    {args : List Width} → Operands Γ args → List (Point (Label saved carried result extra))
  | _, .nil => []
  | _, .cons ref tail =>
    let site := match origins ref with
      | .inl captured => ⟨none, state.savedCount - (state.toPhysical captured).index⟩
      | .inr cut => ⟨savedHeader, cut⟩
    site :: operandSites state origins tail

def findSites? (state : Layout.State Input saved carried result extra) :
    (index cursor : Nat) → {Γ : List Width} → Origins ((extra ++ [saved]) ++ Input) Γ →
    Block TargetOp (Label saved carried result extra) Γ [result] →
    Option (HeaderSites (Label saved carried result extra))
  | 0, cursor, _, origins, .letOp _ operands tail =>
    some ⟨operandSites state origins operands, useSitesAt savedHeader 0 (cursor + 1) tail⟩
  | index + 1, cursor, _, origins, .letOp _ _ tail =>
    findSites? state index (cursor + 1) (afterBinding origins (cursor + 1)) tail
  | _, _, _, _, .terminator _ => none

structure Kept (Labels : List Width → Type) where
  index : Nat
  sites : HeaderSites Labels

def Kept.point (kept : Kept (Label saved carried result extra)) : Point (Label saved carried result extra) :=
  ⟨savedHeader, kept.index⟩

/-- Retain the original position only for a live binding whose operands
    and uses pass the actual cut check. -/
def keep? (state : Layout.State Input saved carried result extra) (origin : Nat) :
    Option (Kept (Label saved carried result extra)) := do
  let index ← state.reference.origins.idxOf? origin
  let sites ← findSites? state index 0 (Saved.origins (extra ++ [saved])) (state.cfg.block .header)
  let kept : Kept _ := ⟨index, sites⟩
  let _ := targetDecEqWith (saved := saved) (carried := carried) (result := result) (extra := extra)
  if !sites.uses.isEmpty &&
      GCM.Dominance.Placement.checkCut state.cfg intermediateBlocks sites.operands sites.uses kept.point
    then some kept else none

structure Analysis (state : Layout.State Input saved carried result extra) where
  request : Nomination
  kept : Kept (Label saved carried result extra)
  preheader : Option (Layout.Move state)
  control : Control state

/-- Admit the unchanged header and try the nominated physical preheader
    cut with the existing typed splice. -/
def analyze? (state : Layout.State Input saved carried result extra) (request : Nomination) :
    Option (Analysis state) := do
  if Discovery.supported? state then
    let kept ← keep? state request.origin
    let control ← Control.check? state
    pure ⟨request, kept, Layout.emit? state request, control⟩
  else none

/-- Prefer shallower loops, then retain the later control position at
    equal depth. The supported header follows the anonymous entry. -/
def Analysis.selectedMove? {state : Layout.State Input saved carried result extra} (analysis : Analysis state) :
    Option (Layout.Move state) :=
  if analysis.control.depth none < analysis.control.depth savedHeader then analysis.preheader else none

def Analysis.point {state : Layout.State Input saved carried result extra} (analysis : Analysis state) :
    Point (Label saved carried result extra) :=
  if analysis.selectedMove?.isSome then ⟨none, analysis.request.cut⟩ else analysis.kept.point

def Analysis.requests {state : Layout.State Input saved carried result extra} (analysis : Analysis state) :
    List Nomination :=
  if analysis.selectedMove?.isSome then [analysis.request] else []

def Analysis.output {state : Layout.State Input saved carried result extra} (analysis : Analysis state) :
    Layout.Output Input saved carried result :=
  match analysis.selectedMove? with
  | none => ⟨extra, state⟩
  | some moved => ⟨_, moved.next⟩

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock
