module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Defs

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback.Graph

/-- An execution representation preserves and lifts steps and terminal
outcomes at every represented point. The point map need not be injective. -/
structure Transport {P Q O U : Type*} (g : Graph P O) (h : Graph Q U)
    (point : P → Q) (output : O → U) : Prop where
  step : ∀ p q, h.step (point p) q ↔ ∃ p', g.step p p' ∧ point p' = q
  ub : ∀ p, h.ub (point p) ↔ g.ub p
  finish : ∀ p u, h.finish (point p) u ↔ ∃ o, g.finish p o ∧ output o = u
  divergence : output g.divergence = h.divergence

/-- A deterministic local observation advances to a new point or stops
with an ordinary outcome. Fresh UB can be supplied by a subsequent observer. -/
def transitions {P O : Type*} (next : P → P ⊕ O) (diverge : O) : Graph P O where
  step p q := next p = .inl q
  ub _ := False
  finish p o := next p = .inr o
  divergence := diverge

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback.Graph
