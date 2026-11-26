module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Replay.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BitQueryTreeExecution

/-! # Native replay and exact packed traces of selected finite request trees -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Expr Assignment)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

/-- Execute the actual packed arrow under the all-replies trace model.
The trace retains request order, every query and reply, and the typed exit. -/
theorem packed_outcomes (t : Tree 1) (input : Bool) :
    t.observations input = t.outcomes (fun _ => input) :=
  BitQueryTreeExecution.packed_outcomes t input

/-- The example's changed last query differs at one guard and reply history. -/
theorem last_query_difference (input firstTag firstPayload secondTag secondPayload : Bool) :
    let env := Assignment.push (Assignment.push (fun _ : Fin 1 => input) firstPayload) secondPayload
    let askQuery := fun altered => if altered && firstTag && secondTag then Expr.literal false else Example.lastQuery
    (askQuery false).eval env ≠ (askQuery true).eval env ↔
      input = true ∧ firstTag = true ∧ firstPayload = true ∧ secondTag = true ∧ secondPayload = false :=
  BitQueryTreeExecution.last_query_difference input firstTag firstPayload secondTag secondPayload

/-- Hold the first two ordered events and final reply fixed. The log from the
original packed program is absent from the altered one's actual observations. -/
theorem three_request_witness :
    Example.observation true ∈ (Example.program false).observations true ∧
    Example.observation false ∈ (Example.program true).observations true ∧
    Example.observation true ∉ (Example.program true).observations true :=
  BitQueryTreeExecution.three_request_witness

theorem three_request_ne : (Example.program false).packed ≠ (Example.program true).packed :=
  BitQueryTreeExecution.three_request_ne

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree
