module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.ExactSum.Defs

/-! # Repeating exact-sum observations at their final states -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category

open CategoryTheory

universe v w x

variable {α : Type w} {σ : Type x} {κ : Type v} {atomType : α → κ → Prop} {A B : Ty κ}

/-- Read the internal label as the repeat tag and the external label as the
return tag. State, faults and divergence are unchanged. -/
def tagIterationOutcome : Outcome 2 α σ → Outcome 1 α σ
  | .ret i a s => .ret 0 (if i = 0 then .inr a else .inl a) s
  | .fault s => .fault s
  | .diverge => .diverge

/-- The entry transfers to the step with the original payload and state.
Each repeat transfers to the step with the payload and final state of that
particular observation. The graph also retains step faults, divergence,
and top. -/
noncomputable def iterationGraph
    (f : single A ⟶ (single (.coprod B A) : Interface α σ atomType))
    (a : singlePayload (atomType := atomType) A) : Feedback.Run [A] [B] α σ :=
  Feedback.run (fun s => WithTop.some {Outcome.ret (0 : Fin 2) a.val s})
    (fun _ b s => (f.total 0 b s).map (Set.preimage tagIterationOutcome))

/-- An ordinary right tag transfers the exact typed payload and the final
machine state to the next step. Fresh UB supplies no repeat edge. -/
def Repeat (f : single A ⟶ (single (.coprod B A) : Interface α σ atomType))
    (p q : singlePayload (atomType := atomType) A × σ) : Prop :=
  (f.run 0 p.1 p.2).Ordinary (.ret 0 (.inr q.1.val) q.2)

/-- Collect finite results, reachable step divergence, and infinite
repetition, with the overlay's existing priority for reachable top. -/
noncomputable def iterateObservations
    (f : single A ⟶ (single (.coprod B A) : Interface α σ atomType))
    (a : singlePayload (atomType := atomType) A) (s : σ) : Behaviour 1 α σ :=
  Feedback.close (iterationGraph f a) (.entry s)

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
