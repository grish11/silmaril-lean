module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition.Ranked.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RankedReplyRecognition

/-! # Standard Paper certificates for ranked reply-table recognition -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition.Ranked

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open CategoryTheory
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {Φ : Type} [Profile Φ] [DecidableEq Φ] {n : Nat}

/-- Recognition certifies literal block inlining in standard Paper. -/
theorem eqv (R : Fin n → ReplyShape) (rank : Fin n → Nat) {s t : ReplyShape}
    {r : Region Φ} {p : Control Φ s t} {policy : RequestPolicy Φ n}
    (accepted : recognize R rank s t r policy = some p) :
    Paper.Eqv [s.ty] r p.region [t.ty] :=
  RankedReplyRecognition.sound R rank accepted

/-- The computed control represents the original exactly typed singleton arrow. -/
theorem ofRegion_eq_native (R : Fin n → ReplyShape) (rank : Fin n → Nat) {s t : ReplyShape}
    {r : Region Φ} {p : Control Φ s t} {policy : RequestPolicy Φ n}
    (hr : ValueBranches [s.ty] r [t.ty])
    (accepted : recognize R rank s t r policy = some p) : Paper.TypeCategory.ofRegion hr = p.native :=
  ((Paper.TypeCategory.ofRegion_eq_iff hr p.region_typed).2 (eqv R rank accepted)).trans
    p.native_eq_ofRegion.symm

/-- The finite-reply renderer gives the native arrow at each point of the exact input shape. -/
theorem ofRegion_eq_render (R : Fin n → ReplyShape) (rank : Fin n → Nat) {s t : ReplyShape}
    {r : Region Φ} {p : Control Φ s t} {policy : RequestPolicy Φ n}
    (hr : ValueBranches [s.ty] r [t.ty])
    (accepted : recognize R rank s t r policy = some p) (x : s.Value) :
    point s x ≫ Paper.TypeCategory.ofRegion hr = (p.readback x).render (point t) := by
  rw [ofRegion_eq_native R rank hr accepted, p.native_eq_ofRegion, p.ofRegion_eq_readback, point_dispatch]

/-- Run the checker on an existing typed row and return the computed control and its certificate.
The packet profile supplies the exact local binder types absent from the erased table. -/
def recognizeTyped (R : Fin n → ReplyShape) (rank : Fin n → Nat) (s t : ReplyShape)
    {r : Region Φ} (hr : ValueBranches [s.ty] r [t.ty])
    (policy : RequestPolicy Φ n := nativeRequestPolicy Φ n) :
    Option {p : Control Φ s t // Paper.TypeCategory.ofRegion hr = p.native} :=
  match found : recognize R rank s t r policy with
  | none => none
  | some p => some ⟨p, ofRegion_eq_native R rank hr found⟩

namespace Example

theorem accepted_typed : ValueBranches [Reply.ty] accepted [Reply.ty] :=
  RankedReplyRecognition.accepted_typed

theorem backEdge_typed : ValueBranches [Reply.ty] backEdge [Reply.ty] :=
  RankedReplyRecognition.backEdge_typed

theorem captured_typed : ValueBranches [Reply.ty] captured [Reply.ty] :=
  RankedReplyRecognition.captured_typed

theorem accepts : recognize packets rank Reply Reply accepted = some expected := rfl

theorem rejects_backEdge : recognize packets rank Reply Reply backEdge = none := rfl

theorem rejects_capture : recognize packets rank Reply Reply captured = none := rfl

theorem reads_on_both_entries (x : Reply.Value) :
    point Reply x ≫ Paper.TypeCategory.ofRegion accepted_typed =
      (Row.call Recognition.Example.Op.read Row.leaf).render (point Reply) := by
  rw [ofRegion_eq_render packets rank accepted_typed accepts]
  cases x <;> rfl

end Example

namespace RequestExample

theorem accepted_typed : ValueBranches [ReplyShape.unit.ty] accepted [ReplyShape.unit.ty] :=
  RankedReplyRecognition.request_accepted_typed

theorem backEdge_typed : ValueBranches [ReplyShape.unit.ty] backEdge [ReplyShape.unit.ty] :=
  RankedReplyRecognition.request_backEdge_typed

theorem captured_typed : ValueBranches [ReplyShape.unit.ty] captured [ReplyShape.unit.ty] :=
  RankedReplyRecognition.request_captured_typed

theorem accepts : recognize packets rank .unit .unit accepted = some expected := rfl

theorem rejects_backEdge : recognize packets rank .unit .unit backEdge = none := rfl

theorem rejects_capture : recognize packets rank .unit .unit captured = none := rfl

/-- Each reply to the first request executes the same downstream request. -/
theorem native_readback :
    Paper.TypeCategory.ofRegion accepted_typed = expectedRow.render (point .unit) := by
  simpa only [RankedReplyRecognition.request_readback] using
    (Category.id_comp (Paper.TypeCategory.ofRegion accepted_typed)).symm.trans
      (ofRegion_eq_render packets rank accepted_typed accepts PUnit.unit)

theorem flat_typed : ValueBranches [ReplyShape.unit.ty] flat [ReplyShape.unit.ty] :=
  RankedReplyRecognition.request_flat_typed

theorem flat_rejects_default : recognize flatPackets flatRank .unit .unit flat = none := rfl

/-- The same checker computes the representative for a request in a local
block when supplied the two-label entry-let law. -/
theorem flat_accepts (law : CfgEta.EntryLet (Paper.Eqv (τ := Silmaril.Ty Atom) (Φ := Op)) 2) :
    recognize flatPackets flatRank .unit .unit flat (.ofEntryLet law) = some expected := rfl

theorem flat_native_readback (law : CfgEta.EntryLet (Paper.Eqv (τ := Silmaril.Ty Atom) (Φ := Op)) 2) :
    Paper.TypeCategory.ofRegion flat_typed = expectedRow.render (point .unit) :=
  (ofRegion_eq_native flatPackets flatRank flat_typed (flat_accepts law)).trans
    ((ofRegion_eq_native packets rank accepted_typed accepts).symm.trans native_readback)

/-- For this written table the global premise reduces to one exact local
entry-let instance. The entry jump and the reply continuation are already
eliminated by standard Paper equations. -/
theorem flat_move_iff :
    Paper.Eqv [ReplyShape.unit.ty] flatEntered flatMoved [ReplyShape.unit.ty] ↔
    Paper.Eqv [ReplyShape.unit.ty] flat expected.region [ReplyShape.unit.ty] :=
  RankedReplyRecognition.request_flat_move_iff

end RequestExample

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition.Ranked
