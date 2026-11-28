module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Equation.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Equation.Example.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Categorical.Thms

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Equation

open CF.Example (checked width)
open Pruned.Example (accepted)
open Reindex.Example (original external)
open Composition.Example (first second paired predecessors)
open Pruned.Equation.Example (variant variantSource projectedVariant)
open SeaOfNodes.Loop.MLIR.CF (model evalOp)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.CF.SwitchAssert (Cfg)
open Blocks (Bank)

example : (variant.trace model 3 ((variantSource 4).body.eval model (pull first (pull second paired)))).map
    (fun occurrence => (variant.predecessor occurrence).val) = predecessors := by
  rw [pull_trans, paired, pull_roundtrip]
  rfl

private theorem native_ne :
    checked.lower.denotePart (Join.model model) original ≠ variant.lower.denotePart (Join.model model) original := by
  have lhs : checked.lower.denotePart (Join.model model) original = Part.some (.cons (22 : Word width) .nil) :=
    (checked.lower.denotePart_eq_some (Join.model model) original _).mpr ⟨3, checked.lower_run model 3 original⟩
  have rhs : variant.lower.denotePart (Join.model model) original = Part.some (.cons (24 : Word width) .nil) :=
    (variant.lower.denotePart_eq_some (Join.model model) original _).mpr ⟨3, variant.lower_run model 3 original⟩
  rw [lhs, rhs, ne_eq, Part.some_inj]
  intro same
  exact (by decide : (22 : Word width) ≠ 24) (congrArg (fun values => values.get .head) same)

private theorem native_ne_at_paired :
    checked.lower.denotePart (Join.model model) (pull first (pull second paired)) ≠
      variant.lower.denotePart (Join.model model) (pull first (pull second paired)) := by
  rw [pull_trans, paired, pull_roundtrip]
  exact native_ne

example :
    (graph second (graph first accepted.lower)).denotePart (Join.model model) paired ≠
      (graph second (graph first projectedVariant.lower)).denotePart (Join.model model) paired :=
  fun equal => native_ne_at_paired ((rvsdg_at_trans_iff first second accepted projectedVariant paired).mp equal)

example :
    (Cfg.embed (lowerWith accepted (pull first (cfNames second)))).denotePart evalOp (encodeValues paired) ≠
      (Cfg.embed (lowerWith projectedVariant (pull first (cfNames second)))).denotePart evalOp (encodeValues paired) :=
  fun equal => native_ne_at_paired ((cf_at_trans_iff first second accepted projectedVariant paired).mp equal)

example : ¬ ∀ input : Bank (regs := external) model,
    (graph second (graph first accepted.lower)).denotePart (Join.model model) input =
      (graph second (graph first projectedVariant.lower)).denotePart (Join.model model) input :=
  fun holds => native_ne (((rvsdg_satisfaction_trans first second accepted projectedVariant).mp holds) original)

example : ¬ ∀ input : Env (Widths external),
    (Cfg.embed (lowerWith accepted (pull first (cfNames second)))).denotePart evalOp input =
      (Cfg.embed (lowerWith projectedVariant (pull first (cfNames second)))).denotePart evalOp input :=
  fun holds => native_ne (((cf_satisfaction_trans first second accepted projectedVariant).mp holds) original)

example : graph (first.trans second).symm (graph second (graph first accepted.lower)) = accepted.lower := by
  rw [graph_trans first second, graph_roundtrip]

example : lowerWith projectedVariant (pull first (pull second (cfNames (first.trans second).symm))) =
    Pruned.lower projectedVariant := by
  rw [pull_trans, lowerCF_roundtrip]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Equation
