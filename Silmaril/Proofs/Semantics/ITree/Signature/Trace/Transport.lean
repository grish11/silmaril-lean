module

public import Silmaril.Semantics.ITree.Signature.Trace.Defs
import Silmaril.Proofs.Semantics.ITree.Signature.Trace.Lift

public section

namespace Silmaril.Elgot.ITree.TraceSignature.Proofs

open CategoryTheory

universe u v w

variable {S T U : TraceSignature.{u}} {A : Type v} {X : Type w}

@[simp] theorem reply_forward_backward (f : S ⟶ T) (q : Request S.toSignature.Event) (r : q.1) :
    f.hom.reply q ((f.replyEquiv q).symm r) = r :=
  (f.replyEquiv q).apply_symm_apply r

@[simp] theorem reply_backward_forward (f : S ⟶ T) (q : Request S.toSignature.Event)
    (r : (f.hom.request q).1) : (f.replyEquiv q).symm (f.hom.reply q r) = r :=
  (f.replyEquiv q).symm_apply_apply r

theorem trace_id (p : Trace S.toSignature.Event A) : (𝟙 S : S ⟶ S).trace p = p := by
  induction p with
  | «prefix» | request | result => rfl
  | @exchange R ev r p ih =>
    have hr : ((𝟙 S : S ⟶ S).replyEquiv ⟨R, ev⟩).symm r = r :=
      reply_forward_backward (𝟙 S) ⟨R, ev⟩ r
    change Trace.exchange ev _ _ = _
    rw [hr, ih]

theorem trace_comp (f : S ⟶ T) (g : T ⟶ U) (p : Trace S.toSignature.Event A) :
    (f ≫ g).trace p = g.trace (f.trace p) := by
  induction p with
  | «prefix» | request | result => rfl
  | @exchange R ev r p ih =>
    let q : Request S.toSignature.Event := ⟨R, ev⟩
    have hr : ((f ≫ g).replyEquiv q).symm r =
        (g.replyEquiv (f.hom.request q)).symm ((f.replyEquiv q).symm r) := by
      apply ((f ≫ g).replyEquiv q).injective
      change (f ≫ g).hom.reply q (((f ≫ g).replyEquiv q).symm r) =
        f.hom.reply q (g.hom.reply (f.hom.request q) _)
      simp only [reply_forward_backward]
    change Trace.exchange (g.hom.request (f.hom.request q)).2 _ _ = Trace.exchange _ _ _
    rw [hr, ih]

theorem trace_ofEquiv (e : SignatureEquiv S.toSignature.Event T.toSignature.Event)
    (p : Trace S.toSignature.Event A) : (ofEquiv e).trace p = e.trace (Equiv.refl A) p := by
  induction p with
  | «prefix» | request | result => rfl
  | @exchange R ev r p ih =>
    let q : Request S.toSignature.Event := ⟨R, ev⟩
    have hr : (((ofEquiv e : S ⟶ T).replyEquiv q).symm r) = e.reply q r := by
      apply (e.reply q).symm.injective
      exact (reply_forward_backward (ofEquiv e) q r).trans ((e.reply q).symm_apply_apply r).symm
    change Trace.exchange (e.request q).2 _ _ = Trace.exchange (e.request q).2 _ _
    rw [hr, ih]

theorem traceLift_iff (f : S ⟶ T) (p : Trace S.toSignature.Event A) (q : Trace T.toSignature.Event A) :
    f.hom.TraceLift p q ↔ f.trace p = q := by
  constructor
  · intro h
    induction h with
    | «prefix» | result | request => rfl
    | @exchange R ev reply p q _ ih =>
      change Trace.exchange (f.hom.request ⟨R, ev⟩).2
        ((f.replyEquiv ⟨R, ev⟩).symm (f.hom.reply ⟨R, ev⟩ reply)) (f.trace p) = _
      rw [reply_backward_forward, ih]
  · rintro rfl
    induction p with
    | «prefix» => exact .prefix
    | result a => exact .result a
    | request e => exact .request e
    | @exchange R ev reply p ih =>
      have lift := Signature.Hom.TraceLift.exchange ev ((f.replyEquiv ⟨R, ev⟩).symm reply) ih
      rw [reply_forward_backward f ⟨R, ev⟩ reply] at lift
      exact lift

theorem trace_injective (f : S ⟶ T) : Function.Injective (f.trace (A := A)) := by
  intro p q equal
  exact Signature.Proofs.traceLift_unique f.hom f.request_injective
    ((traceLift_iff f p (f.trace p)).mpr rfl) ((traceLift_iff f q (f.trace q)).mpr rfl) equal

theorem handledTrace_image (f : S ⟶ T) (step : Handler X T.toSignature.Event)
    (x : X) (t : Tree S.toSignature.Event A) (p : Trace T.toSignature.Event A) :
    HandledTrace step x (f.hom.tree id t) p ↔
      ∃ source, HandledTrace (f.hom.restrict step) x t source ∧ f.trace source = p := by
  constructor
  · intro seen
    obtain ⟨source, lift, handled⟩ := Signature.Proofs.handledTrace_project f.hom step x t p seen
    exact ⟨source, handled, (traceLift_iff f _ _).mp lift⟩
  · rintro ⟨source, handled, equal⟩
    obtain ⟨target, lift, seen⟩ := Signature.Proofs.handledTrace_lift f.hom step x t source handled
    exact ((traceLift_iff f _ _).mp lift).symm.trans equal ▸ seen

theorem hasTrace_image (f : S ⟶ T) (t : Tree S.toSignature.Event A) (p : Trace T.toSignature.Event A) :
    HasTrace (f.hom.tree id t) p ↔ ∃ pre, HasTrace t pre ∧ f.trace pre = p := by
  simpa only [traceLift_iff f] using Signature.Proofs.hasTrace_lift_iff f.hom t p

end Silmaril.Elgot.ITree.TraceSignature.Proofs
