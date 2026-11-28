module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Script

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open CFG.Dependent (Packet pack unpack unpack_pack)
open Syntax (Payload Primitives)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty} {states : Nat}
  {g : Table S R} {h : Table S T}
  {caller : Payload (R.get g.entry)} {caller' : Payload (T.get h.entry)}

theorem schedule_path [DecidableEq Φ] {replies : ReplyEnumeration S} {start point : ProductConfig R T}
    {path : List (ProductEdge S R T)}
    (walk : ProductPath (g.productEdges h caller caller' replies) start path point)
    (initial : Fin states) (stores : List (Fin states)) (length : stores.length = path.length) :
    ∃ final rows, ScheduledPath g h caller caller' start initial path stores point final rows := by
  induction walk generalizing stores with
  | start =>
    obtain rfl := List.eq_nil_of_length_eq_zero length
    exact ⟨initial, [], .start⟩
  | @step past p edge earlier listed ih =>
    have nonempty : stores ≠ [] := by
      intro nil
      simp [nil] at length
    have parts := List.dropLast_concat_getLast nonempty
    have priorLength : stores.dropLast.length = past.length := by
      apply Nat.add_right_cancel (m := 1)
      simpa using (congrArg List.length parts).trans length
    obtain ⟨s, rows, scheduled⟩ := ih stores.dropLast priorLength
    obtain ⟨f, arg, next, next', reply, lower, upper, rfl⟩ :=
      Table.product_edge_forms replies listed
    exact ⟨_, _, parts ▸ scheduled.step lower upper reply (stores.getLast nonempty)⟩

private theorem execute_success {X : List Syntax.Ty} (prim : Primitives Φ states)
    (q : InterpreterScript.Query Φ states) (reply : Packet (S.replies q.op)) (t : Fin states)
    (next : (i : Fin (S.replies q.op).length) → Payload ((S.replies q.op).get i) → Packet X)
    (runs : q.read prim = (InterpreterScript.Row.success q reply t).2) :
    (Head.request q.op q.arg next).execute prim q.state = .repeat (next reply.1 reply.2) t := by
  let typeEq := congrArg Payload (S.target q.op)
  change prim q.op q.arg q.state = .ret (cast typeEq.symm (pack reply)) t at runs
  rw [Head.execute, runs]
  have casts : cast typeEq (cast typeEq.symm (pack reply)) = pack reply := by simp only [cast_cast, cast_eq]
  let advance (p : Packet (S.replies q.op)) := Transition.repeat (next p.1 p.2) t
  change advance (unpack (cast typeEq (cast typeEq.symm (pack reply)))) = advance reply
  rw [casts, unpack_pack]

theorem scheduled_observes {start point : ProductConfig R T} {initial final : Fin states}
    {path : List (ProductEdge S R T)} {stores : List (Fin states)} {rows : List (InterpreterScript.Row Φ states)}
    (scheduled : ScheduledPath g h caller caller' start initial path stores point final rows)
    {prim : Primitives Φ states} (run : InterpreterScript.Realizes prim rows) :
    g.observeAt caller prim start.1 initial = g.observeAt caller prim point.1 final ∧
    h.observeAt caller' prim start.2 initial = h.observeAt caller' prim point.2 final := by
  induction scheduled with
  | start => exact ⟨rfl, rfl⟩
  | @step past stores p s rows f arg next next' earlier lower upper reply t ih =>
    obtain ⟨left, right⟩ := ih (fun row mem => run row (List.mem_append_left _ mem))
    have last := run _ (List.mem_append_right rows (List.mem_singleton_self
      (InterpreterScript.Row.success (S := S) ⟨f, arg, s⟩ reply t)))
    constructor
    · refine left.trans ?_
      rw [g.observe_step, lower, execute_success prim ⟨f, arg, s⟩ reply t next last]
    · refine right.trans ?_
      rw [h.observe_step, upper, execute_success prim ⟨f, arg, s⟩ reply t next' last]

theorem scheduled_feasible_iff [DecidableEq Φ] {start point : ProductConfig R T} {initial final : Fin states}
    {path : List (ProductEdge S R T)} {stores : List (Fin states)} {rows : List (InterpreterScript.Row Φ states)}
    (scheduled : ScheduledPath g h caller caller' start initial path stores point final rows) :
    (∃ prim : Primitives Φ states, InterpreterScript.Realizes prim rows ∧
      g.observeAt caller prim start.1 initial = g.observeAt caller prim point.1 final ∧
      h.observeAt caller' prim start.2 initial = h.observeAt caller' prim point.2 final) ↔
      InterpreterScript.Consistent rows := by
  rw [← InterpreterScript.feasible_iff rows]
  exact ⟨fun ⟨prim, run, _, _⟩ => ⟨prim, run⟩,
    fun ⟨prim, run⟩ => ⟨prim, run, scheduled_observes scheduled run⟩⟩

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
