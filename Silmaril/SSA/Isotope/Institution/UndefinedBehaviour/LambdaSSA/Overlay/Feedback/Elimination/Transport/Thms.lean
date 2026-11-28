module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Transport.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Transport

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback.Graph

/-- Exact replay retains finite outcomes, reachable top, and genuine
infinite paths while allowing different internal point representations. -/
theorem Transport.close_eq {P Q O U : Type*} {g : Graph P O} {h : Graph Q U}
    {point : P → Q} {output : O → U} (rel : Transport g h point output) (p : P) :
    h.close (point p) = (g.close p).map (Set.image output) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Elimination.Transport.close_eq rel p

open Silmaril.Isotope (Value)

universe u v w x y

/-- Singleton native steps and terminals implement a deterministic graph
under the supplied point and terminal encodings. -/
theorem transitions_run {κ : Type u} {R L : List (Silmaril.Ty κ)} {α : Type v} {σ : Type w}
    {P : Type x} {O : Type y} (next : P → P ⊕ O) (diverge : O)
    (invoke : P → Fin R.length × Value α × σ) (output : O → Outcome L.length α σ)
    (f : Run R L α σ) (div : output diverge = .diverge)
    (localRow : ∀ p, f (.block (invoke p).1 (invoke p).2.1 (invoke p).2.2) =
      match next p with
      | .inl q => WithTop.some {Outcome.ret (internal R L (invoke q).1) (invoke q).2.1 (invoke q).2.2}
      | .inr o => WithTop.some {external R L (output o)}) :
    Transport (transitions next diverge) (ofRun f)
      (fun p => .block (invoke p).1 (invoke p).2.1 (invoke p).2.2) output :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Elimination.Transport.transitions_run
    next diverge invoke output f div localRow

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback.Graph
