module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.State.Defs

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open Category.FiniteIteration
open CFG.Dependent (Packet)
open TwoRequest (Tag)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty]

/-- Observation laws needed by the product proof at a fixed typed caller.
The computation of heads and the implementation of feedback can vary. -/
structure HeadObserver (S : RequestSignature Φ) (R : List Syntax.Ty) where
  head : Packet R → Head S R
  returnValue : Packet R → Tag → Value Unit
  observe : {σ : Type v} → Syntax.StatePrimitives Φ σ → Packet R → σ → Behaviour 2 Unit σ
  step : ∀ {σ : Type v} (prim : Syntax.StatePrimitives Φ σ) (p : Packet R) (s : σ),
    observe prim p s =
      match (head p).execute prim s with
      | .exit i selected t => if selected then ⊤ else WithTop.some {Outcome.ret i (returnValue p i) t}
      | .repeat q t => observe prim q t
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge}
  infinite : ∀ {σ : Type v} (prim : Syntax.StatePrimitives Φ σ)
    (p : Nat → Packet R) (s : Nat → σ),
    (∀ n, (head (p n)).execute prim (s n) = .repeat (p (n + 1)) (s (n + 1))) →
    observe prim (p 0) (s 0) = WithTop.some {Outcome.diverge}
  mapState : ∀ {σ τ : Type v} (e : σ ↪ τ) (prim : Syntax.StatePrimitives Φ σ)
    (other : Syntax.StatePrimitives Φ τ),
    (∀ f a s, other f a (e s) = (prim f a s).mapState e) →
    ∀ p s, observe other p (e s) = Behaviour.mapState e (observe prim p s)

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
