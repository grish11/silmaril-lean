module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs
import Silmaril.SSA.RVSDG.NestedTheta.Petri.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Petri.Proofs

open SeaOfNodes.Diamond (ValueSort sortValue)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR (Word)
open Silmaril.MLIR.Arith (Width)
open Relation (ReflTransGen)
open RVSDG (Tuple)
open RVSDG.NestedTheta.Petri (Finishes Step result finishes_iff)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (targets : Targets src entry) (input : Bank (regs := regs) model)

theorem decoded_iff_finishes (value : sortValue Word out) :
    (∃ final, ReflTransGen (Step (Join.model model) targets.numbered input)
        (RVSDG.NestedTheta.Petri.initial (Join.model model) targets.numbered) final ∧
      (result (Join.model model) targets.numbered input final).map (fun packet => packet.get .head) = some value) ↔
    Finishes (Join.model model) targets.numbered input (.cons value .nil) := by
  unfold Finishes
  refine exists_congr fun final => and_congr Iff.rfl ?_
  cases result (Join.model model) targets.numbered input final with
  | none => simp
  | some packet =>
    cases packet with
    | cons word tail =>
      cases tail
      constructor
      · intro same
        have decoded : some word = some value := same
        exact congrArg (fun word => some (Tuple.cons word .nil)) (Option.some.inj decoded)
      · intro same
        exact congrArg (Option.map (fun packet => packet.get .head)) same

theorem no_completion_iff_numbered :
    (∀ packet, ¬ Finishes (Join.model model) targets.numbered input packet) ↔
      ∀ activations, targets.numbered.run (Join.model model) activations input = none := by
  simp only [finishes_iff, RVSDG.NestedTheta.Graph.Returns, not_exists, Option.eq_none_iff_forall_ne_some]
  exact forall_comm

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Petri.Proofs
