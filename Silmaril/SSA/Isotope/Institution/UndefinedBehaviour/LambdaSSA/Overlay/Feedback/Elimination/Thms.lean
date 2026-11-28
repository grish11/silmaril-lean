module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Finite
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Elimination.Infinite

/-! # Model-level two-level elimination for overlay feedback -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback

open Institution.Observational

universe u v w x

/-- An infinite sequence of positive segments gives an infinite path of
actual steps. The proof chooses successors within the segments. -/
theorem transitive_segments_path {P : Type u} {step : P → P → Prop} (boundary : Nat → P)
    (segments : ∀ n, Relation.TransGen step (boundary n) (boundary (n + 1))) :
    ∃ path : Nat → P, path 0 = boundary 0 ∧ ∀ n, step (path n) (path (n + 1)) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Elimination.path_of_segments boundary segments

namespace Graph

variable {P : Type u} {O : Type v} {g : Graph P O} {inside : P → Prop} {p q : P}

/-- Fresh top is exactly reachable UB. -/
theorem close_top_iff : g.close p = ⊤ ↔ g.ReachesUB p :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Elimination.close_top_iff

theorem ordinary_close_iff {o : O} : g.Ordinary p o ↔ ¬ g.ReachesUB p ∧ o ∈ g.outcomes p :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Elimination.ordinary_close_iff

/-- An outer transition has a finite inner prefix and a final ordinary edge
to an outer point. Reachable inner UB suppresses the transition. -/
theorem outer_step_iff :
    (g.outer inside).step p q ↔
      ¬ (g.inner inside).ReachesUB p ∧
        ∃ b, (g.inner inside).Reaches p b ∧ g.step b q ∧ ¬ inside q :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Elimination.outer_step_iff

/-- Every outer transition consumes at least one original step. -/
theorem outer_step_progress (h : (g.outer inside).step p q) :
    Relation.TransGen g.step p q :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Elimination.outer_step_progress h

theorem reachesUB_outer_iff : (g.outer inside).ReachesUB p ↔ g.ReachesUB p :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Elimination.reachesUB_outer_iff

/-- Finite ordinary terminal observations retain their outcomes below UB. -/
theorem finite_segmented_iff {o : O} (safe : ¬ g.ReachesUB p) :
    g.Finite p o ↔ ∃ b, (g.outer inside).Reaches p b ∧ (g.inner inside).Finite b (.inr o) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Elimination.finite_segmented_iff safe

/-- Below reachable UB, an infinite flat path either eventually stays in the
inner group or visits outer points infinitely often. Both alternatives
reflect genuine flat divergence. The reflection of an infinite sequence of
outer segments uses classical choice of a successor at each original step. -/
theorem infinite_outer_iff (safe : ¬ g.ReachesUB p) :
    g.Infinite p ↔
      (∃ q, (g.outer inside).Reaches p q ∧ (g.inner inside).Infinite q) ∨
        (g.outer inside).Infinite p :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Elimination.infinite_outer_iff safe

/-- Closing inner transfers with the boundary exposed, followed by closing the
outer graph, gives exactly the one-shot closure. -/
theorem close_outer : (g.outer inside).close p = g.close p :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Feedback.Elimination.close_outer

end Graph

variable {τ : Type v} {R I O L : List τ} {α : Type w} {σ : Type x}

@[simp] theorem close_ofRun (f : Run R L α σ) (p : Point R.length α σ) :
    (Graph.ofRun f).close p = close f p :=
  rfl

/-- Two-level elimination applies to the existing overlay model at any
partition of block invocations. The inner closure exposes the entire
outer invocation, including its payload and machine state. -/
theorem close_partition (f : Run R L α σ) (inside : Point R.length α σ → Prop)
    (p : Point R.length α σ) : ((Graph.ofRun f).outer inside).close p = close f p :=
  Graph.close_outer

/-- In particular, a typed split of the hidden label interface into `I ++ O`
can be closed in two stages, keeping `O` visible when closing `I`. -/
theorem close_two_levels (f : Run (I ++ O) L α σ) (p : Point (I ++ O).length α σ) :
    ((Graph.ofRun f).outer (insidePrefix I O)).close p = close f p :=
  close_partition f (insidePrefix I O) p

/-- The staged graph closure computes the denotation of the existing typed
feedback constructor, in every observational model. -/
theorem denote_feedback_two_levels {Φ : Type u} [TypeFormers τ] [HasTy Φ τ] {Γ : List τ}
    (entry : Region Φ Γ ((I ++ O) ++ L))
    (blocks : (i : Fin (I ++ O).length) → Region Φ ((I ++ O).get i :: Γ) ((I ++ O) ++ L))
    (M : Model.{u,w,x} Φ Γ.length) (s : M.σ) :
    ((Graph.ofRun (feedbackRun entry blocks M)).outer (insidePrefix I O)).close (.entry s) =
      denote (.feedback entry blocks) M s :=
  close_two_levels (feedbackRun entry blocks M) (.entry s)

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Feedback
