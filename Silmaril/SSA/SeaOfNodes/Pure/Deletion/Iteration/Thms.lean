module

public import Silmaril.SSA.SeaOfNodes.Pure.Deletion.Iteration.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Pure.Deletion.Iteration.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Pure.Deletion.Iteration

open Diamond (Model Signature Ty Val)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data} {args ports : List (Ty Data)}
variable {start : Table Op args ports} (result : Result start)

theorem first?_eq_none_iff (table : Table Op args ports) : first? table = none ↔ NoEligible table :=
  Proofs.SSA.SeaOfNodes.Pure.Deletion.Iteration.first_none table

theorem Step.shorter {table : Table Op args ports} (step : Step table) :
    step.next.sigs.length + 1 = table.sigs.length :=
  step.deleted.erasure.shorter

theorem Step.decreases {table : Table Op args ports} (step : Step table) :
    step.next.sigs.length < table.sigs.length :=
  step.shorter ▸ Nat.lt_succ_self _

/-- The trace logs one deletion per removed binding, at most the initial size. -/
theorem Result.count : result.final.sigs.length + result.positions.length = start.sigs.length ∧
    result.positions.length ≤ start.sigs.length :=
  let size := Proofs.SSA.SeaOfNodes.Pure.Deletion.Iteration.count result.trace
  ⟨size, size ▸ Nat.le_add_left _ _⟩

/-- No current producer is deletable by this checker with this complete packet. -/
theorem Result.noEligible : NoEligible result.final :=
  Proofs.SSA.SeaOfNodes.Pure.Deletion.Iteration.stopped result.trace

theorem Result.eval_eq (m : Model.{u, v, w} Op) (input : Tuple (Val m.value) args) :
    result.final.eval m input = start.eval m input :=
  Proofs.SSA.SeaOfNodes.Pure.Deletion.Iteration.packet_eq result.trace m input

end Silmaril.SSA.SeaOfNodes.Pure.Deletion.Iteration
