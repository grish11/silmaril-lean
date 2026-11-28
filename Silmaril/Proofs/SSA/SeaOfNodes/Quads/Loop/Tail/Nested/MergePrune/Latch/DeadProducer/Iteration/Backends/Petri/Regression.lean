module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Example.Defs
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Thms

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends

open Diamond.MLIR.CF.Example (input width)
open SeaOfNodes.Loop.MLIR.CF (model)
open SeaOfNodes.MLIR (Word)
open Relation (ReflTransGen)
open RVSDG.NestedTheta.Petri (Finishes Step result)

private def targets : Targets Example.source 0 := ((compile Example.source 0).toOption).get (by rfl)

example : ∃ final, ReflTransGen (Step (Join.model model) targets.numbered input)
    (RVSDG.NestedTheta.Petri.initial (Join.model model) targets.numbered) final ∧
    (result (Join.model model) targets.numbered input final).map (fun packet => packet.get .head) =
      some (16 : Word width) :=
  (targets.petri_firing_iff input (16 : Word width)).mpr ⟨14, rfl⟩

example : ¬ Finishes (Join.model model) targets.numbered input (.cons (17 : Word width) .nil) := by
  intro witness
  obtain ⟨fuel, returned⟩ := (targets.petri_finishes_iff input (17 : Word width)).mp witness
  have original : Example.source.runFrom model 14 0 input = some (16 : Word width) := rfl
  have later := Tail.Source.runFrom_mono model (Nat.le_max_left fuel 14) returned
  have known := Tail.Source.runFrom_mono model (Nat.le_max_right fuel 14) original
  exact (show (17 : Word width) ≠ 16 by decide) (Option.some.inj (later.symm.trans known))

example : compile Example.skipsMerge 0 = .error .shape := compile_shape_refusal rfl

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends
