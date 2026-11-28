module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.AcyclicReplyRecognition

/-! # Native Paper certificates for the executable recognizer -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open CategoryTheory
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {Φ : Type} [Profile Φ] [DecidableEq Φ]

omit [Profile Φ] in
/-- A successful syntax comparison certifies literal equality of the compared bodies. -/
theorem sameBody_eq {a b : Region Φ} (h : sameBody a b = true) : a = b :=
  AcyclicReplyRecognition.sameBody_eq h

omit [DecidableEq Φ] in
/-- The written region for a request followed by control on its reply. -/
theorem call_region (op : Φ) {t : ReplyShape} (p : Control Φ (Profile.reply op) t) :
    (Control.let₁ (.call op) p).region =
      .let₁ (.op op (.var 0)) (p.region.renameVars (Silmaril.DeBruijn.lift Nat.succ)) :=
  AcyclicReplyRecognition.call_region op p

/-- Recognition of a bare case table also works in an exactly typed
surrounding context. The renaming specifies the live sum payload. -/
theorem table_eqv {Γ : VCtx (Ty Atom)} {s t : ReplyShape} {ρ : Nat → Nat}
    (w : SSA.Ren [s.ty] Γ ρ) {r : Region Φ} {p : Control Φ s t}
    (accepted : recognizeTable s t ρ r = some p) :
    Paper.Eqv Γ r (p.region.renameVars ρ) [t.ty] :=
  AcyclicReplyRecognition.table_sound w accepted

/-- The accepted raw row equals its re-emitted control at the exact
singleton input and output boundary in standard Paper. -/
theorem eqv {t : ReplyShape} {r : Region Φ} {p : Control Φ .unit t}
    (accepted : recognize t r = some p) :
    Paper.Eqv [ReplyShape.unit.ty] r p.region [t.ty] :=
  AcyclicReplyRecognition.sound accepted

/-- An existing guarded typing witness fixes the original native arrow. -/
theorem ofRegion_eq_native {t : ReplyShape} {r : Region Φ} {p : Control Φ .unit t}
    (hr : ValueBranches [ReplyShape.unit.ty] r [t.ty]) (accepted : recognize t r = some p) :
    Paper.TypeCategory.ofRegion hr = p.native :=
  ((Paper.TypeCategory.ofRegion_eq_iff hr p.region_typed).2 (eqv accepted)).trans
    p.native_eq_ofRegion.symm

/-- The accepted row feeds directly into the existing finite reply-tree renderer. -/
theorem ofRegion_eq_render {t : ReplyShape} {r : Region Φ} {p : Control Φ .unit t}
    (hr : ValueBranches [ReplyShape.unit.ty] r [t.ty]) (accepted : recognize t r = some p) :
    Paper.TypeCategory.ofRegion hr = (p.readback PUnit.unit).render (point t) := by
  rw [ofRegion_eq_native hr accepted, p.native_eq_ofRegion, p.ofRegion_eq_readback]
  rfl

/-- Run the recognizer on an existing typed row and return its native
equality certificate. The equality proof is erased by the executable. -/
def recognizeTyped (t : ReplyShape) {r : Region Φ} (hr : ValueBranches [ReplyShape.unit.ty] r [t.ty]) :
    Option {p : Control Φ .unit t // Paper.TypeCategory.ofRegion hr = p.native} :=
  match found : recognize t r with
  | none => none
  | some p => some ⟨p, ofRegion_eq_native hr found⟩

namespace Example

theorem accepted_typed : ValueBranches [ReplyShape.unit.ty] accepted [Reply.ty] :=
  AcyclicReplyRecognition.graph_typed rfl AcyclicReplyRecognition.return_right_typed

theorem backEdge_typed : ValueBranches [ReplyShape.unit.ty] backEdge [Reply.ty] :=
  AcyclicReplyRecognition.graph_typed rfl (.br rfl (.var rfl))

theorem captured_typed : ValueBranches [ReplyShape.unit.ty] captured [Reply.ty] :=
  AcyclicReplyRecognition.graph_typed rfl AcyclicReplyRecognition.return_right_typed

theorem accepts : recognize Reply accepted = some expected := rfl

theorem rejects_backEdge : recognize Reply backEdge = none := rfl

theorem rejects_capture : recognize Reply captured = none := rfl

theorem accepted_native :
    Paper.TypeCategory.ofRegion accepted_typed = (expected.readback PUnit.unit).render (point Reply) :=
  ofRegion_eq_render accepted_typed accepts

end Example

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Acyclic.Recognition
