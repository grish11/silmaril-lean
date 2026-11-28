module

public import Silmaril.Semantics.ITree.Signature.Trace.Defs
import Silmaril.Proofs.Semantics.ITree.Signature.Trace.Transport
import Silmaril.Proofs.Semantics.ITree.Signature.Trace.Order
import Silmaril.Proofs.Semantics.ITree.Signature.Trace.Lift

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

theorem Hom.traceLift_iff (f : S ⟶ T) (p : Trace S.toSignature.Event A) (q : Trace T.toSignature.Event A) :
    f.hom.TraceLift p q ↔ f.trace p = q :=
  Proofs.traceLift_iff f p q

/-- The target's finite observations from `x` are exactly the images of the
source observations from `x` under the reduct handler. This includes pending
requests and prefixes, and holds for every target observation. -/
theorem Hom.handledTrace_image (f : S ⟶ T) (step : Handler X T.toSignature.Event)
    (x : X) (t : Tree S.toSignature.Event A) (p : Trace T.toSignature.Event A) :
    HandledTrace step x (f.hom.tree id t) p ↔
      ∃ source, HandledTrace (f.hom.restrict step) x t source ∧ f.trace source = p :=
  Proofs.handledTrace_image f step x t p

/-- Even when the target has additional keys, its observations of the
translated tree are exactly the image of the original observations. -/
theorem Hom.hasTrace_image (f : S ⟶ T) (t : Tree S.toSignature.Event A) (p : Trace T.toSignature.Event A) :
    HasTrace (f.hom.tree id t) p ↔ ∃ pre, HasTrace t pre ∧ f.trace pre = p :=
  Proofs.hasTrace_image f t p

theorem Hom.traceLE_iff (f : S ⟶ T) {l r : Tree S.toSignature.Event A} :
    TraceLE (f.hom.tree id l) (f.hom.tree id r) ↔ TraceLE l r :=
  ⟨Signature.Proofs.traceLE_reflect f.hom f.request_injective (fun q => (f.reply_bijective q).2),
    Signature.Proofs.traceLE_map f.hom⟩

end Silmaril.Elgot.ITree.TraceSignature

namespace Silmaril.Elgot.ITree.Signature

open CategoryTheory

universe u v w

variable {S T U : Signature.{u}} {A : Type v} {X : Type w}

@[simp] theorem Hom.traceLift_id (p q : Trace S.Event A) : (𝟙 S : S ⟶ S).TraceLift p q ↔ p = q :=
  Proofs.traceLift_id p q

/-- An exact lift along a composite factors through an intermediate trace. -/
theorem Hom.traceLift_comp (f : S ⟶ T) (g : T ⟶ U) (p : Trace S.Event A) (r : Trace U.Event A) :
    (f ≫ g).TraceLift p r ↔ ∃ q, f.TraceLift p q ∧ g.TraceLift q r :=
  Proofs.traceLift_comp f g p r

/-- Injective request keys determine the source trace of each lift. -/
theorem Hom.traceLift_unique (f : S ⟶ T) (keys : Function.Injective f.request)
    {p q : Trace S.Event A} {r : Trace T.Event A} (left : f.TraceLift p r) (right : f.TraceLift q r) : p = q :=
  Proofs.traceLift_unique f keys left right rfl

theorem Hom.handledTrace_lift (f : S ⟶ T) (step : Handler X T.Event)
    (x : X) (t : Tree S.Event A) (p : Trace S.Event A)
    (handled : HandledTrace (f.restrict step) x t p) :
    ∃ q, f.TraceLift p q ∧ HandledTrace step x (f.tree id t) q :=
  Proofs.handledTrace_lift f step x t p handled

theorem Hom.handledTrace_project (f : S ⟶ T) (step : Handler X T.Event)
    (x : X) (t : Tree S.Event A) (p : Trace T.Event A)
    (handled : HandledTrace step x (f.tree id t) p) :
    ∃ q, f.TraceLift q p ∧ HandledTrace (f.restrict step) x t q :=
  Proofs.handledTrace_project f step x t p handled

/-- Actual observations of a mapped tree are exactly all lifts of its
source observations, including when some source replies have no lift. -/
theorem Hom.hasTrace_lift_iff (f : S ⟶ T) (t : Tree S.Event A) (q : Trace T.Event A) :
    HasTrace (f.tree id t) q ↔ ∃ p, HasTrace t p ∧ f.TraceLift p q :=
  Proofs.hasTrace_lift_iff f t q

/-- Reindexing preserves directed trace inclusion for any signature morphism. -/
theorem Hom.traceLE_map (f : S ⟶ T) {l r : Tree S.Event A} (included : TraceLE l r) :
    TraceLE (f.tree id l) (f.tree id r) :=
  Proofs.traceLE_map f included

/-- Reflection needs every source reply to have a target representative.
Several target replies may represent the same source reply. -/
theorem Hom.traceLE_iff_of_surjective (f : S ⟶ T) (keys : Function.Injective f.request)
    (replies : ∀ q, Function.Surjective (f.reply q)) {l r : Tree S.Event A} :
    TraceLE (f.tree id l) (f.tree id r) ↔ TraceLE l r :=
  ⟨Proofs.traceLE_reflect f keys replies, f.traceLE_map⟩

end Silmaril.Elgot.ITree.Signature
