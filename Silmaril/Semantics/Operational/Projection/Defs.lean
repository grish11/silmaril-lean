module

public import Cslib.Foundations.Semantics.LTS.Execution

/-! # Operational projection and readback

A projection preserves actions and successors. Its readback condition starts
from the specific presentation already chosen for the semantic source. This
lets a run use the result of one readback as the input to the next.
-/

@[expose] public section

namespace Silmaril.Semantics.Operational

/-- One-step soundness and readback across state and action projections.
States can include layout invariants in their type. The projected action
need not determine its finite presentation. -/
structure Projection {F S A B : Type*}
    (presented : Cslib.LTS F A) (semantic : Cslib.LTS S B)
    (projectState : F → S) (projectAction : A → B) : Prop where
  sound : ∀ ⦃source action target⦄, presented.Tr source action target →
    semantic.Tr (projectState source) (projectAction action) (projectState target)
  readback : ∀ ⦃source action target⦄, semantic.Tr (projectState source) action target →
    ∃ label next, presented.Tr source label next ∧
      projectAction label = action ∧ projectState next = target

end Silmaril.Semantics.Operational
