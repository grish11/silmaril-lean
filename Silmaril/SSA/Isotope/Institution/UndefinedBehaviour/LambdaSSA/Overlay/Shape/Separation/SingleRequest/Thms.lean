module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.SingleRequest.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.SingleRequest.Soundness

/-! # Finite separation for acyclic one-request LambdaSSA overlays -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.SingleRequest

open Category.FiniteIteration

universe v w

/-- The installed evaluator runs the common native request and invokes the
response normal form at each reached reply and its final state. -/
theorem denote_endpoint (p : Endpoint) (M : Institution.Observational.Model.{0,v,w} Instr 0) (s : M.σ) :
    Overlay.denote p.region M s =
      (Overlay.denote (.native request) M s).bind (fun _ a t => p.afterReply a t) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.SingleRequest.denote_endpoint p M s

/-- The shaped normal-form order is sound for nondeterministic shaped models,
including their ordinary faults and primitive may-divergence. -/
theorem shaped_sound (p q : Endpoint) (le : ReplyRefines p q)
    (M : Shape.Model.{0,0,v,w} Instr []) (s : M.raw.σ) :
    Shape.denote p.region M s ≤ Shape.denote q.region M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.SingleRequest.shaped_sound p q le M s

theorem finite_observe {states : Nat} (p : Endpoint) (prim : Syntax.Primitives Instr states)
    (s : Fin states) :
    Shape.denote p.region (Syntax.model prim Syntax.emptyBindings) s =
      match prim .request ⟨.unit, .unit⟩ s with
      | .ret a t => p.afterReply a.val t
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge} :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.SingleRequest.finite_observe p prim s

/-- The same finite shaped interpreter separates every failed normal-form
comparison, with the request changing the state from zero to one. -/
theorem finite_test_iff (p q : Endpoint) :
    let M := Syntax.model (unitInterpreter (1 : Fin 2)) Syntax.emptyBindings
    Shape.denote p.region M 0 ≤ Shape.denote q.region M 0 ↔ ReplyRefines p q :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.SingleRequest.finite_test_iff p q

/-- Model validity for the shaped semantics at the test model's universes. -/
theorem shaped_refines_iff (p q : Endpoint) :
    (∀ (M : Shape.Model.{0,0,0,0} Instr []) (s : M.raw.σ),
      Shape.denote p.region M s ≤ Shape.denote q.region M s) ↔ ReplyRefines p q :=
  ⟨fun all => (finite_test_iff p q).mp (all _ _), shaped_sound p q⟩

/-- Keeping the raw reply projection in the normal form ensures soundness
even when a successful reply violates the opcode's declared type. -/
theorem raw_sound (p q : Endpoint) (le : RawReplyRefines p q) :
    Refines.{0,0,v,w} p.region q.region :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.SingleRequest.raw_sound p q le

theorem raw_test_iff (p q : Endpoint) :
    Overlay.denote p.region rawProbe 0 ≤ Overlay.denote q.region rawProbe 0 ↔ RawReplyRefines p q :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.SingleRequest.raw_test_iff p q

/-- The installed unrestricted order sees the difference between forwarding
and discarding an unshaped reply. -/
theorem raw_refines_iff (p q : Endpoint) :
    Refines.{0,0,0,0} p.region q.region ↔ RawReplyRefines p q :=
  ⟨fun all => (raw_test_iff p q).mp (all rawProbe (0 : Fin 2)), raw_sound p q⟩

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.SingleRequest
