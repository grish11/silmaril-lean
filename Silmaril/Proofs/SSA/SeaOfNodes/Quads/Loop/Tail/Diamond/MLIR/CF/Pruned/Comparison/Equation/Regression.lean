module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison.Equation.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison.Equation.Example.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Categorical.Thms

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Equation

open CF.Example (checked input source regs width)
open Pruned.Example (accepted)
open Equation.Example (variant variantSource projectedVariant)
open SeaOfNodes.Loop.MLIR.CF (model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Env)
open SeaOfNodes.MLIR.Lowering (encodeValues)

example : (variant.trace model 3 ((variantSource 4).body.eval model input)).map
    variant.predecessor = [6, 0, 6] := rfl

example : checked.nextBank model ((source 4).body.eval model input) =
    variant.nextBank model ((variantSource 4).body.eval model input) := rfl

private theorem baseObservation :
    checked.lower.denotePart (Join.model model) input = Part.some (.cons (22 : Word width) .nil) :=
  (checked.lower.denotePart_eq_some (Join.model model) input _).mpr ⟨3, checked.lower_run model 3 input⟩

private theorem variantObservation :
    variant.lower.denotePart (Join.model model) input = Part.some (.cons (24 : Word width) .nil) :=
  (variant.lower.denotePart_eq_some (Join.model model) input _).mpr ⟨3, variant.lower_run model 3 input⟩

private theorem native_ne_at :
    checked.lower.denotePart (Join.model model) input ≠ variant.lower.denotePart (Join.model model) input := by
  rw [baseObservation, variantObservation, ne_eq, Part.some_inj]
  intro same
  exact (by decide : (22 : Word width) ≠ 24) (congrArg (fun values => values.get .head) same)

example : observeCF accepted (encodeValues input) ≠ observeCF projectedVariant (encodeValues input) :=
  fun equal => native_ne_at ((cf_at_iff accepted projectedVariant input).mp equal)

example : ¬ (prunedEquation accepted projectedVariant).Holds (Join.model model) :=
  fun holds => native_ne_at (((rvsdg_satisfaction accepted projectedVariant).mp holds) input)

example : ¬ ∀ env : Env (Widths regs), observeCF accepted env = observeCF projectedVariant env :=
  fun holds => native_ne_at (((cf_satisfaction accepted projectedVariant).mp holds) input)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Equation
