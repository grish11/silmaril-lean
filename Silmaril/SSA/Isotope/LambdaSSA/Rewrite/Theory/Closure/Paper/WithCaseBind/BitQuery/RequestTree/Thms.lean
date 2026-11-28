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

/-- The forwarded operand carries its bound Bit to the same validated
ordered-trace interpreter. -/
theorem written_packed_outcomes (t : Tree 1) (input : Bool) :
    t.writtenObservations input = t.outcomes (fun _ => input) :=
  BitQueryTreeExecution.written_packed_outcomes t input

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (bit)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (InstructionModel)

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => types

noncomputable local instance : InstructionModel J M signature.Instr := instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

/-- The same observations at the named categorical denotation of the
literal packed written syntax, before choosing a native quotient. -/
theorem written_singleton_outcomes (t : Tree 1) (g : Bool) :
    ((denoteSingletonRegion J M (t.written_typed inputSlots).packExits.hasType).of (bit g)).outcomes =
      t.outcomes (fun _ => g) :=
  BitQueryTreeExecution.written_singleton_outcomes t g

/-- Strip one ordered event at its exact tag and payload to advance the environment. -/
theorem outcome_with_head {n : Nat} (env : Assignment n) (label : Bool) (query : Expr n)
    (l r : Tree (n + 1)) (e : Event) (tail : Word) (result : Except Bool Result) :
    (result, FreeMonoid.of e * tail) ∈ (Tree.ask label query l r).outcomes env ↔
      e.label = label ∧ e.query = query.eval env ∧
        (result, tail) ∈ (if e.right then r.outcomes (env.push e.payload) else l.outcomes (env.push e.payload)) :=
  BitQueryTreeExecution.outcome_with_head env label query l r e tail result

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
