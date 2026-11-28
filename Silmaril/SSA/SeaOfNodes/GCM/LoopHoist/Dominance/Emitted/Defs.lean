module

public import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Tree.Synthesis.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Defs

/-! # Dominator-tree synthesis for the emitted (post-hoist) loop CFG

`GCM.LoopHoist.Dominance.stage` numbers the three blocks of the *source*
single-latch loop (preheader/header/exit) before any hoist. Composed
executors such as `GCM.LoopHoist.Corridor.pickAndHoist?` emit a *different*
typed CFG, over `GCM.LoopHoist.Label saved carried result extra` instead of
`SourceLabel carried result`, with a widened header bank. No numbering or
certified `DominatorTree` synthesis existed for that emitted label family;
`GCM.Dominance.Tree.Synthesis.synthesize?` is generic over any label and
injective numbering, so this file supplies only the numbering it needs.

This is a reachability/dominance prerequisite only. It does not resolve
operand origins in the emitted header, and it does not make the pinned Φ
read at the exit (or any other use) movable — both stay open, as recorded
in the ExitSink coverage gap. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Emitted

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)

variable {Op : OpSignature} {Input : List Width} {saved carried result : Width} {extra : List Width}

/-- The structural chain from the emitted entry through the header to the exit. -/
def stage : BlockId (Label saved carried result extra) → Nat
  | none => 0
  | some ⟨_, .header⟩ => 1
  | some ⟨_, .exit⟩ => 2

/-- The closed two-block inventory of the emitted CFG, beyond the anonymous entry. -/
def blocks : List (Target (Label saved carried result extra)) :=
  [⟨_, .header⟩, ⟨_, .exit⟩]

private theorem stage_injective {a b : BlockId (Label saved carried result extra)}
    (same : stage a = stage b) : a = b := by
  rcases a with _ | ⟨_, a⟩ <;> rcases b with _ | ⟨_, b⟩
  · rfl
  · cases b <;> simp [stage] at same
  · cases a <;> simp [stage] at same
  · cases a <;> cases b <;> simp_all [stage]

/-- Compare the two emitted blocks by their fixed stage number. -/
def targetDecEq (saved carried result : Width) (extra : List Width) :
    DecidableEq (Target (Label saved carried result extra)) :=
  fun a b => decidable_of_iff (stage (some a) = stage (some b))
    ⟨by exact fun same => Option.some.inj (stage_injective same),
      congrArg (fun label => stage (some label))⟩

/-- Synthesize a certified dominator tree for an emitted CFG with this label
family, given a successor-closed two-block inventory. This reuses the
general synthesis machinery and the existing `Label` constructors; it adds
only the injective numbering `GCM.Dominance.Tree.Synthesis.synthesize?`
needs for this emitted label family. -/
def synthesize? (cfg : Cfg Op (Label saved carried result extra) Input [result]) :
    Option {tree : DominatorTree cfg // tree.Complete} :=
  letI := targetDecEq saved carried result extra
  GCM.Dominance.Tree.Synthesis.synthesize? cfg blocks stage (by exact fun {_ _} same => stage_injective same)

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Emitted
