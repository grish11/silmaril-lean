module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Schedule.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Schedule.Replay

/-! # Correctness of fixed-carrier schedule search -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open ScheduleSearch (StateInventory Witness)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ} {R T : List Syntax.Ty}
  {states : Nat} {g : Table S R} {h : Table S T} {caller : Syntax.Payload (R.get g.entry)}
  {caller' : Syntax.Payload (T.get h.entry)} {replies : ReplyEnumeration S} {start point : ProductConfig R T}
  {path : List (ProductEdge S R T)} {initial : Fin states} {inventory : StateInventory states}
  {tests : Fin states → List (InterpreterScript.Row Φ states)}

/-- A successful search reconstructs one interpreter for the actual shared
path and the tests at its final state. -/
theorem Table.searchSchedule_sound (walk : ProductPath (g.productEdges h caller caller' replies) start path point)
    {w : Witness Φ states} (found : g.searchSchedule caller start path initial inventory tests = some w) :
    ScheduledPath g h caller caller' start initial path w.stores point w.final w.rows ∧
      w.tests = tests w.final ∧ InterpreterScript.Realizes w.interpreter (w.rows ++ w.tests) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch.searchSchedule_sound
    walk found

/-- Over the supplied exhaustive carrier, success is equivalent to a
schedule of this path whose prefix and terminal tests fit one interpreter. -/
theorem Table.searchSchedule_success_iff
    (walk : ProductPath (g.productEdges h caller caller' replies) start path point) :
    (∃ w, g.searchSchedule caller start path initial inventory tests = some w) ↔
      ∃ stores final rows, ScheduledPath g h caller caller' start initial path stores point final rows ∧
        InterpreterScript.Consistent (rows ++ tests final) :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch.searchSchedule_success_iff
    walk

/-- Failure rules out a schedule meeting these tests for this path and initial state. -/
theorem Table.searchSchedule_none_iff
    (walk : ProductPath (g.productEdges h caller caller' replies) start path point) :
    g.searchSchedule caller start path initial inventory tests = none ↔
      ¬ ∃ stores final rows, ScheduledPath g h caller caller' start initial path stores point final rows ∧
        InterpreterScript.Consistent (rows ++ tests final) := by
  rw [← Table.searchSchedule_success_iff (initial := initial) (inventory := inventory) (tests := tests) walk]
  cases g.searchSchedule caller start path initial inventory tests <;> simp

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
