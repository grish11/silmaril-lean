module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.SingleRequest.Thms

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.SingleRequest

open Category.FiniteIteration

private def forward : Endpoint := ⟨0, true, false⟩
private def literal : Endpoint := ⟨0, false, false⟩
private def otherExit : Endpoint := ⟨1, false, false⟩
private def reachedUB : Endpoint := ⟨0, true, true⟩

private abbrev testModel := Syntax.model (unitInterpreter (1 : Fin 2)) Syntax.emptyBindings

example : Shape.denote forward.region testModel 0 =
    WithTop.some {Outcome.ret (0 : Fin 2) Value.unit (1 : Fin 2)} := by
  exact finite_observe forward _ _

example : Shape.denote reachedUB.region testModel 0 = ⊤ := by
  exact finite_observe reachedUB _ _

example : Shape.denote forward.region testModel 0 ≤ Shape.denote reachedUB.region testModel 0 :=
  (finite_test_iff _ _).mpr (.inl rfl)

example : ¬ Shape.denote reachedUB.region testModel 0 ≤ Shape.denote forward.region testModel 0 := by
  intro le
  simpa [ReplyRefines, reachedUB, forward] using (finite_test_iff _ _).mp le

example : ¬ Shape.denote literal.region testModel 0 ≤ Shape.denote otherExit.region testModel 0 := by
  intro le
  have order := (finite_test_iff _ _).mp le
  change false = true ∨ (false = false ∧ (0 : Fin 2) = 1) at order
  simp at order

private def failedRequest : Syntax.Primitives Instr 2 :=
  fun _ _ s => if s = 0 then .fault 1 else .diverge

private abbrev failedModel := Syntax.model failedRequest Syntax.emptyBindings

example : Shape.denote reachedUB.region failedModel 0 =
    WithTop.some {Outcome.fault (1 : Fin 2)} := by
  exact finite_observe reachedUB _ _

example : Shape.denote reachedUB.region failedModel (1 : Fin 2) =
    WithTop.some {Outcome.diverge} := by
  exact finite_observe reachedUB _ _

/-- The endpoints both carry a literal UB exit, but their actual exit is ordinary. -/
example {M : Shape.Model Instr []} (s : M.raw.σ) :
    Shape.denote forward.region M s = Shape.denote literal.region M s :=
  le_antisymm (shaped_sound forward literal (.inr ⟨rfl, rfl⟩) M s)
    (shaped_sound literal forward (.inr ⟨rfl, rfl⟩) M s)

example : ¬ Refines.{0,0,0,0} forward.region literal.region := by
  intro le
  simpa [RawReplyRefines, forward, literal] using (raw_refines_iff _ _).mp le

/-- info: 'Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.SingleRequest.shaped_refines_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shaped_refines_iff

/-- info: 'Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.SingleRequest.raw_refines_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms raw_refines_iff

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.SingleRequest
