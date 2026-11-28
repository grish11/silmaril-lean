module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Schedule.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Schedule.Consistency

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch
  (Request Schedules Witness StateInventory)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] [DecidableEq Φ] {S : RequestSignature Φ} {states : Nat}

variable (inventory : StateInventory states) (tests : Fin states → List (InterpreterScript.Row Φ states))

theorem search_found {requests : List (Request S)} {initial : Fin states}
    {prefixRows : List (InterpreterScript.Row Φ states)} {w : Witness Φ states}
    (consistent : InterpreterScript.Consistent prefixRows)
    (found : ScheduleSearch.search inventory tests requests initial prefixRows = some w) :
    ∃ rows, Schedules requests initial w.stores w.final rows ∧
      w.rows = prefixRows ++ rows ∧ w.tests = tests w.final ∧
      InterpreterScript.Consistent (w.rows ++ w.tests) := by
  induction requests generalizing initial prefixRows w with
  | nil =>
    rw [ScheduleSearch.search] at found
    split at found
    · rename_i allowed
      obtain rfl := (Option.some.inj found).symm
      exact ⟨[], .nil _, (List.append_nil _).symm, rfl, (can_append_all_iff consistent _).mp allowed⟩
    · cases found
  | cons req rest ih =>
    rw [ScheduleSearch.search] at found
    obtain ⟨t, _, hit⟩ := List.exists_of_findSome?_eq_some found
    by_cases allowed : InterpreterScript.canAppend prefixRows (req.row initial t) = true
    · simp only [allowed, ite_true] at hit
      cases tail : ScheduleSearch.search inventory tests rest t (prefixRows ++ [req.row initial t]) with
      | none => simp [tail] at hit
      | some candidate =>
        have same : { candidate with stores := t :: candidate.stores } = w := by simpa [tail] using hit
        subst w
        obtain ⟨rows, assigned, built, terminal, ok⟩ := ih ((can_append_iff consistent).mp allowed) tail
        exact ⟨_, .cons assigned, by simpa [List.append_assoc] using built, terminal, ok⟩
    · simp [allowed] at hit

theorem search_exists {requests : List (Request S)} {initial final : Fin states} {stores : List (Fin states)}
    {prefixRows rows : List (InterpreterScript.Row Φ states)}
    (assigned : Schedules requests initial stores final rows)
    (consistent : InterpreterScript.Consistent prefixRows)
    (all : InterpreterScript.Consistent (prefixRows ++ rows ++ tests final)) :
    ∃ w, ScheduleSearch.search inventory tests requests initial prefixRows = some w := by
  induction assigned generalizing prefixRows with
  | nil s =>
    have allowed : InterpreterScript.canAppendAll prefixRows (tests s) = true :=
      (can_append_all_iff consistent _).mpr (by simpa using all)
    exact ⟨⟨[], s, prefixRows, tests s⟩, by simp [ScheduleSearch.search, allowed]⟩
  | @cons req rest s t stores final rows prior ih =>
    have ok : InterpreterScript.Consistent (prefixRows ++ [req.row s t]) :=
      consistent_subset (fun _ mem => by
        simpa [List.append_assoc] using List.mem_append_left (rows ++ tests final) mem) all
    have allowed := (can_append_iff consistent).mpr ok
    obtain ⟨candidate, tail⟩ := ih ok (by simpa [List.append_assoc] using all)
    cases found : ScheduleSearch.search inventory tests (req :: rest) s prefixRows with
    | some w => exact ⟨w, rfl⟩
    | none =>
      rw [ScheduleSearch.search] at found
      have missed := (List.findSome?_eq_none_iff.mp found) t (inventory.complete t)
      simp [allowed, tail] at missed

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch
