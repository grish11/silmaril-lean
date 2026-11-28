module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Schedule.Defs

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch
  (Request Schedules requests?)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R T : List Syntax.Ty} {states : Nat}

theorem schedule_length {requests : List (Request S)} {initial final : Fin states} {stores : List (Fin states)}
    {rows : List (InterpreterScript.Row Φ states)} (assigned : Schedules requests initial stores final rows) :
    stores.length = requests.length := by
  induction assigned with
  | nil => rfl
  | cons _ ih => simp [ih]

theorem schedule_unique {requests : List (Request S)} {initial final final' : Fin states} {stores : List (Fin states)}
    {rows rows' : List (InterpreterScript.Row Φ states)}
    (assigned : Schedules requests initial stores final rows) (other : Schedules requests initial stores final' rows') :
    final = final' ∧ rows = rows' := by
  induction assigned generalizing final' rows' with
  | nil => cases other; exact ⟨rfl, rfl⟩
  | cons _ ih =>
    cases other with
    | cons tail =>
      obtain ⟨rfl, rfl⟩ := ih tail
      exact ⟨rfl, rfl⟩

private theorem schedule_snoc {requests : List (Request S)} {initial final : Fin states} {stores : List (Fin states)}
    {rows : List (InterpreterScript.Row Φ states)} (assigned : Schedules requests initial stores final rows)
    (req : Request S) (next : Fin states) :
    Schedules (requests ++ [req]) initial (stores ++ [next]) next (rows ++ [req.row final next]) := by
  induction assigned with
  | nil => exact .cons (.nil next)
  | cons _ ih => exact .cons ih

variable [DecidableEq Φ]
  {g : Table S R} {h : Table S T}
  {caller : Syntax.Payload (R.get g.entry)} {caller' : Syntax.Payload (T.get h.entry)}

private theorem requests_append (p : ProductConfig R T) (first rest : List (ProductEdge S R T)) :
    requests? g caller p (first ++ rest) = (do
      let (left, mid) ← requests? g caller p first
      let (right, last) ← requests? g caller mid rest
      return (left ++ right, last)) := by
  induction first generalizing p with
  | nil =>
    cases next : requests? g caller p rest <;> simp [requests?, next]
  | cons edge first ih =>
    cases head : Request.ofHead? (g.head caller p.1) edge.1 with
    | none => simp [requests?, head]
    | some req =>
      simp [requests?, head, ih]
      cases requests? g caller edge.2 first <;> simp
      next data =>
        obtain ⟨left, mid⟩ := data
        cases requests? g caller mid rest <;> simp

theorem requests_length {p q : ProductConfig R T} {path : List (ProductEdge S R T)} {requests : List (Request S)}
    (found : requests? g caller p path = some (requests, q)) : requests.length = path.length := by
  induction path generalizing p q requests with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
    rfl
  | cons edge rest ih =>
    cases head : Request.ofHead? (g.head caller p.1) edge.1 with
    | none => simp [requests?, head] at found
    | some req =>
      cases tail : requests? g caller edge.2 rest with
      | none => simp [requests?, head, tail] at found
      | some data =>
        obtain ⟨recorded, endPoint⟩ := data
        simp [requests?, head, tail] at found
        obtain ⟨rfl, rfl⟩ := found
        simp [ih tail]

theorem recorded {start point : ProductConfig R T} {initial final : Fin states}
    {path : List (ProductEdge S R T)} {stores : List (Fin states)} {rows : List (InterpreterScript.Row Φ states)}
    (scheduled : ScheduledPath g h caller caller' start initial path stores point final rows) :
    ∃ requests, requests? g caller start path = some (requests, point) ∧
      Schedules requests initial stores final rows := by
  induction scheduled with
  | start => exact ⟨[], rfl, .nil _⟩
  | @step past stores p s rows f arg next next' earlier lower _ reply t ih =>
    obtain ⟨requests, seen, prior⟩ := ih
    let req : Request S := ⟨f, arg, reply⟩
    refine ⟨requests ++ [req], ?_, schedule_snoc prior req t⟩
    rw [requests_append, seen]
    simp [requests?, Request.ofHead?, lower, req]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch
