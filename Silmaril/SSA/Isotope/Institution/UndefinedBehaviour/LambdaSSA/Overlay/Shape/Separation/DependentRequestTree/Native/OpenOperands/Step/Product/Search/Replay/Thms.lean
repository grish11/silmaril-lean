module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Separation
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Paths
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Script

/-! # Feasible replay and directed separation of guarded native endpoints -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent (Packet)
open CFG.Dependent.Native (withExitUB)
open Syntax (Payload Primitives model)
open TwoRequest (Exits Tag)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {states : Nat}

namespace InterpreterScript

theorem extend_realizes [DecidableEq Φ] {rows : List (Row Φ states)} (ok : Consistent rows)
    (fallback : Primitives Φ states) : Realizes (extend rows fallback) rows :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.InterpreterScript.extend_realizes
    ok fallback

/-- Determinism is exactly agreement of repeated full query keys. Total
extension can use ordinary divergence on unlisted keys. -/
theorem feasible_iff [DecidableEq Φ] (rows : List (Row Φ states)) :
    (∃ prim : Primitives Φ states, Realizes prim rows) ↔ Consistent rows :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.InterpreterScript.feasible_iff
    rows

end InterpreterScript

variable {S : RequestSignature Φ} {R T : List Syntax.Ty} {g : Table S R} {h : Table S T}
  {caller : Payload (R.get g.entry)} {caller' : Payload (T.get h.entry)}
  {start point : ProductConfig R T} {initial final : Fin states}
  {path : List (ProductEdge S R T)} {stores : List (Fin states)} {rows : List (InterpreterScript.Row Φ states)}

/-- A syntactic path admits a script for every length-matched assignment of
reply states. The script may have conflicting entries for repeated queries. -/
theorem ProductPath.schedule [DecidableEq Φ] {replies : ReplyEnumeration S}
    (walk : ProductPath (g.productEdges h caller caller' replies) start path point)
    (initial : Fin states) (stores : List (Fin states)) (length : stores.length = path.length) :
    ∃ final rows, ScheduledPath g h caller caller' start initial path stores point final rows :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.schedule_path
    walk initial stores length

theorem Table.schedule_rejection [DecidableEq Φ] {replies : ReplyEnumeration S}
    {left : ConfigurationEnumeration R} {right : ConfigurationEnumeration T}
    (found : g.searchProduct h caller caller' replies left right = .mismatch point path)
    (initial : Fin states) (stores : List (Fin states)) (length : stores.length = path.length) :
    ∃ final rows, ScheduledPath g h caller caller' (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩)
      initial path stores point final rows := by
  have proof := g.searchProduct_correct h caller caller' replies left right
  rw [found] at proof
  exact proof.1.schedule initial stores length

/-- A single interpreter realizes the scheduled replies, and the installed
observations at the start equal those at the end, exactly under consistency. -/
theorem ScheduledPath.feasible_iff [DecidableEq Φ]
    (scheduled : ScheduledPath g h caller caller' start initial path stores point final rows) :
    (∃ prim : Primitives Φ states, InterpreterScript.Realizes prim rows ∧
      g.observeAt caller prim start.1 initial = g.observeAt caller prim point.1 final ∧
      h.observeAt caller' prim start.2 initial = h.observeAt caller' prim point.2 final) ↔
      InterpreterScript.Consistent rows :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.scheduled_feasible_iff
    scheduled

section Native

variable [DecidableEq Φ]
  {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits}
  {raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits}

/-- A reached ordinary target exit exposes the ordered position. A
different source exit, or source literal UB, refutes refinement. -/
theorem ScheduledPath.refutes_exits (readback : g.checkNative raw = true) (readback' : h.checkNative raw' = true)
    (scheduled : ScheduledPath g h caller caller' (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩)
      initial path stores point final rows)
    (consistent : InterpreterScript.Consistent rows) {i j : Tag} {marked : Bool}
    (lower : g.head caller point.1 = .exit i marked) (upper : h.head caller' point.2 = .exit j false)
    (different : marked = true ∨ i ≠ j) :
    ∃ prim : Primitives Φ states,
      ¬ Shape.denote (withExitUB raw g.selected) (model prim (g.bindings caller)) initial ≤
        Shape.denote (withExitUB raw' h.selected) (model prim (h.bindings caller')) initial :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.refutes_exits
    readback readback' scheduled consistent lower upper different

/-- A fault versus divergence separates pending queries if the final test
extends the successful prefix in one consistent interpreter. -/
theorem ScheduledPath.refutes_queries (readback : g.checkNative raw = true) (readback' : h.checkNative raw' = true)
    (scheduled : ScheduledPath g h caller caller' (⟨g.entry, caller⟩, ⟨h.entry, caller'⟩)
      initial path stores point final rows)
    {f k : Φ} {arg : Payload (instrSrc f)} {arg' : Payload (instrSrc k)}
    {next : (i : Fin (S.replies f).length) → Payload ((S.replies f).get i) → Packet R}
    {next' : (i : Fin (S.replies k).length) → Payload ((S.replies k).get i) → Packet T}
    (lower : g.head caller point.1 = .request f arg next)
    (upper : h.head caller' point.2 = .request k arg' next') (faultState : Fin states)
    (consistent : InterpreterScript.Consistent
      (rows ++ [⟨⟨f, arg, final⟩, .fault faultState⟩, ⟨⟨k, arg', final⟩, .diverge⟩])) :
    ∃ prim : Primitives Φ states,
      ¬ Shape.denote (withExitUB raw g.selected) (model prim (g.bindings caller)) initial ≤
        Shape.denote (withExitUB raw' h.selected) (model prim (h.bindings caller')) initial :=
  Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.refutes_queries
    readback readback' scheduled lower upper faultState consistent

end Native
end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
