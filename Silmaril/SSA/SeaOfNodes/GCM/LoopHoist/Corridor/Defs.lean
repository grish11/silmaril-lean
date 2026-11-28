module

public import Silmaril.SSA.SeaOfNodes.GCM.Corridor.Defs
public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Dominance.Defs

/-! # Hoist one nominated binding using the synthesized placement corridor -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Loop.MLIR.CF (Program TargetOp lower)
open LoopHoist.Dominance (stage)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}

private theorem stage_injective {a b : BlockId (SourceLabel carried result)} (same : stage a = stage b) :
    a = b := by
  rcases a with _ | ⟨_, a⟩ <;> rcases b with _ | ⟨_, b⟩
  · rfl
  · cases b <;> simp [stage] at same
  · cases a <;> simp [stage] at same
  · cases a <;> cases b <;> simp_all [stage]

/-- Compare the three typed labels by their fixed enumeration. -/
def sourceTargetDecEq (carried result : Width) : DecidableEq (Target (SourceLabel carried result)) :=
  fun a b => decidable_of_iff (stage (some a) = stage (some b))
    ⟨fun same => by exact Option.some.inj (stage_injective same),
      congrArg (fun label => stage (some label))⟩

/-- Synthesize dominance from the lowered CFG using the label numbering. -/
def synthesizedTree? (g : Program Input carried result entrySigs headerSigs) :
    Option {tree : DominatorTree (lower g) // tree.Complete} :=
  letI := sourceTargetDecEq carried result
  GCM.Dominance.Tree.Synthesis.synthesize? (lower g) blocks stage (by exact fun {_ _} same => stage_injective same)

/-- Choose on the supplied typed CFG, using its actual edges and local cuts. -/
def chooseCfgCut? (cfg : Cfg TargetOp (SourceLabel carried result) Input [result])
    (operands : List (Point (SourceLabel carried result))) (uses : List (Use (SourceLabel carried result))) :
    Option (Point (SourceLabel carried result)) :=
  letI := sourceTargetDecEq carried result
  GCM.Corridor.chooseSynthesized? cfg blocks stage
    (by exact fun {_ _} same => stage_injective same) operands uses

/-- Choose a source cut using the synthesized corridor. The chooser accepts
any legal result of ranking, including cuts outside the hoist's destination. -/
def chooseCut? (g : Program Input carried result entrySigs headerSigs)
    (operands : List (Point (SourceLabel carried result))) (uses : List (Use (SourceLabel carried result))) :
    Option (Point (SourceLabel carried result)) :=
  chooseCfgCut? (lower g) operands uses

/-- Find the nominated binding, rank its exact definition and use sites,
and pass the selected cut to the existing typed hoist. -/
def pickAndHoist? (g : Program Input carried result entrySigs headerSigs) (index : Nat) :
    Option (Point (SourceLabel carried result) × Output Input carried result) :=
  hoistBindingWith? g index (chooseCut? g)

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
