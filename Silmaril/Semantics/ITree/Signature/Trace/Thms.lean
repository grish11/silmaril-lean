module

public import Silmaril.Semantics.ITree.Signature.Trace.Defs
import Silmaril.Proofs.Semantics.ITree.Signature.Trace.Transport

public section

namespace Silmaril.Elgot.ITree.TraceSignature

open CategoryTheory

universe u v w

variable {S T U : TraceSignature.{u}} {A : Type v} {X : Type w}

@[simp] theorem Hom.reply_forward_backward (f : S ⟶ T) (q : Request S.toSignature.Event) (r : q.1) :
    f.hom.reply q ((f.replyEquiv q).symm r) = r :=
  Proofs.reply_forward_backward f q r

@[simp] theorem Hom.trace_id (p : Trace S.toSignature.Event A) : (𝟙 S : S ⟶ S).trace p = p :=
  Proofs.trace_id p

theorem Hom.trace_comp (f : S ⟶ T) (g : T ⟶ U) (p : Trace S.toSignature.Event A) :
    (f ≫ g).trace p = g.trace (f.trace p) :=
  Proofs.trace_comp f g p

theorem trace_ofEquiv (e : SignatureEquiv S.toSignature.Event T.toSignature.Event)
    (p : Trace S.toSignature.Event A) : (ofEquiv e).trace p = e.trace (Equiv.refl A) p :=
  Proofs.trace_ofEquiv e p

theorem Hom.trace_injective (f : S ⟶ T) : Function.Injective (f.trace (A := A)) :=
  Proofs.trace_injective f

/-- The target's finite observations from `x` are exactly the images of the
source observations from `x` under the reduct handler. This includes pending
requests and prefixes, and holds for every target observation. -/
theorem Hom.handledTrace_image (f : S ⟶ T) (step : Handler X T.toSignature.Event)
    (x : X) (t : Tree S.toSignature.Event A) (p : Trace T.toSignature.Event A) :
    HandledTrace step x (f.hom.tree id t) p ↔
      ∃ source, HandledTrace (f.hom.restrict step) x t source ∧ f.trace source = p :=
  Proofs.handledTrace_image f step x t p

end Silmaril.Elgot.ITree.TraceSignature
