module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Schedule.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Schedule.Recording
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Schedule.Search

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch
  (StateInventory Witness requests?)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ} {R T : List Syntax.Ty}
  {states : Nat} {g : Table S R} {h : Table S T} {caller : Syntax.Payload (R.get g.entry)}
  {caller' : Syntax.Payload (T.get h.entry)} {replies : ReplyEnumeration S} {start point : ProductConfig R T}
  {path : List (ProductEdge S R T)} {initial : Fin states} {inventory : StateInventory states}
  {tests : Fin states → List (InterpreterScript.Row Φ states)}

theorem searchSchedule_sound (walk : ProductPath (g.productEdges h caller caller' replies) start path point)
    {w : Witness Φ states} (found : g.searchSchedule caller start path initial inventory tests = some w) :
    ScheduledPath g h caller caller' start initial path w.stores point w.final w.rows ∧
      w.tests = tests w.final ∧ InterpreterScript.Realizes w.interpreter (w.rows ++ w.tests) := by
  unfold Table.searchSchedule at found
  cases read : requests? g caller start path with
  | none => simp [read] at found
  | some data =>
    obtain ⟨requests, endPoint⟩ := data
    simp only [read] at found
    have empty : InterpreterScript.Consistent ([] : List (InterpreterScript.Row Φ states)) := by
      simp [InterpreterScript.Consistent]
    obtain ⟨rows, assigned, built, terminal, consistent⟩ := search_found inventory tests empty found
    obtain ⟨final', rows', scheduled⟩ :=
      walk.schedule initial w.stores ((schedule_length assigned).trans (requests_length read))
    obtain ⟨requests', read', assigned'⟩ := recorded scheduled
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj (read.symm.trans read'))
    obtain ⟨sameFinal, sameRows⟩ := schedule_unique assigned assigned'
    simp only [List.nil_append] at built
    exact ⟨by rwa [sameFinal, built, sameRows], terminal, InterpreterScript.extend_realizes consistent _⟩

theorem searchSchedule_success_iff
    (walk : ProductPath (g.productEdges h caller caller' replies) start path point) :
    (∃ w, g.searchSchedule caller start path initial inventory tests = some w) ↔
      ∃ stores final rows, ScheduledPath g h caller caller' start initial path stores point final rows ∧
        InterpreterScript.Consistent (rows ++ tests final) := by
  constructor
  · rintro ⟨w, found⟩
    obtain ⟨scheduled, terminal, realized⟩ := searchSchedule_sound walk found
    rw [terminal] at realized
    exact ⟨w.stores, w.final, w.rows, scheduled, (InterpreterScript.feasible_iff _).mp ⟨_, realized⟩⟩
  · rintro ⟨stores, final, rows, scheduled, consistent⟩
    obtain ⟨requests, read, assigned⟩ := recorded scheduled
    have empty : InterpreterScript.Consistent ([] : List (InterpreterScript.Row Φ states)) := by
      simp [InterpreterScript.Consistent]
    obtain ⟨w, found⟩ := search_exists inventory tests assigned empty (by simpa using consistent)
    exact ⟨w, by simpa [Table.searchSchedule, read] using found⟩

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch
