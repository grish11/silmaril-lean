module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Soundness
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Separation

/-! # Finite distinguishing models for Boolean-dependent requests -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest

open Category.FiniteIteration

universe v w

/-- The exact typed native request branches on the successful reply's tag.
The branch receives the reply state. Faults and primitive may-divergence
are the ordinary observations of the request itself. -/
theorem request_denote {Γ : List (Silmaril.Ty Empty)} (M : Shape.Model.{0,0,v,w} Instr Γ)
    (f : Instr) (s : M.raw.σ) :
    Shape.denote (.native (request f Γ)) M s =
      WithTop.some {o | match o with
        | .ret i a t => a = .unit ∧ M.raw.instr f .unit s (bitValue i) t
        | .fault t => M.raw.faults f .unit s t
        | .diverge => M.raw.prim f .unit s} :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest.request_denote M f s

/-- Literal returns and UB have the same observation in every ambient context. -/
theorem exit_denote {Γ : List (Silmaril.Ty Empty)} (e : Exit)
    (M : Institution.Observational.Model.{0,v,w} Instr Γ.length) (s : M.σ) :
    Overlay.denote (e.region (Γ := Γ)) M s = e.behaviour s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest.exit_denote e M s

theorem exit_order {α : Type v} {σ : Type w} (p q : Exit) (s : σ) :
    (p.behaviour s : Behaviour Exits.length α σ) ≤ q.behaviour s ↔ p.Refines q :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest.exit_order p q s

/-- Bind an actual native request to typed continuations in a deterministic
handler. The selected continuation receives unit at the reply's final state. -/
theorem request_bind_finite {Γ : List (Silmaril.Ty Empty)} {n : Nat} (h : Handler n)
    (env : Syntax.Bindings Γ) (f : Instr) (s : Fin n)
    (k : (i : Tag) → Overlay.Region Instr (Exits.get i :: Γ) Exits) :
    Shape.denote (.lsubst (.native (request f Γ)) k) (Syntax.model h.primitives env) s =
      match h f s with
      | .reply i t => Shape.denote (k i)
          (Syntax.model h.primitives (env.push ⟨.unit, exit_type i ▸ .unit⟩)) t
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge} :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest.request_bind_finite h env f s k

/-- Fresh top occurs exactly when two successful replies reach a selected UB
continuation. Competing ordinary observations cannot prevent a reached UB. -/
theorem endpoint_top (p : Endpoint) (M : Shape.Model.{0,0,v,w} Instr []) (s : M.raw.σ) :
    Shape.denote p.region M s = ⊤ ↔
      ∃ i t j u, M.raw.instr p.first .unit s (bitValue i) t ∧
        M.raw.instr (p.next i).key .unit t (bitValue j) u ∧ (p.next i).exit j = .ub :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest.endpoint_top p M s

/-- Normal-form refinement is sound for arbitrary shaped relations, including
nondeterministic successful replies and coexisting faults or divergence. -/
theorem shaped_sound (p q : Endpoint) (h : NormalRefines p q) (M : Shape.Model.{0,0,v,w} Instr [])
    (s : M.raw.σ) : Shape.denote p.region M s ≤ Shape.denote q.region M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest.shaped_sound p q h M s

/-- A deterministic handler computes the complete lifted observation of the
actual overlay, including the final state on ordinary returns and faults. -/
theorem finite_observe {n : Nat} (p : Endpoint) (h : Handler n) (s : Fin n) :
    Shape.denote p.region h.model s = resultBehaviour (p.execute h s) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest.finite_observe p h s

theorem result_order {n : Nat} (p q : Result 2 n) :
    resultBehaviour p ≤ resultBehaviour q ↔ p.refines q :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest.result_order p q

/-- Three states suffice. Disagreeing keys are distinguished with fault
versus divergence. With matching keys, the handler selects both Boolean
replies and keeps every competing reply out of the run. -/
theorem prefix_refines_iff (p q : Endpoint) :
    (∀ first next root step,
      let h := prefixHandler first next root step
      Shape.denote p.region h.model 0 ≤ Shape.denote q.region h.model 0) ↔ NormalRefines p q :=
  ⟨Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest.normal_of_prefixes,
    fun order _ _ _ _ => shaped_sound p q order _ _⟩

/-- Tests over deterministic finite prefixes characterize validity over all
shaped models at the witnesses' universes. The soundness direction also
holds at arbitrary value and state universes. -/
theorem shaped_refines_iff (p q : Endpoint) :
    (∀ (M : Shape.Model.{0,0,0,0} Instr []) (s : M.raw.σ),
      Shape.denote p.region M s ≤ Shape.denote q.region M s) ↔ NormalRefines p q :=
  ⟨fun all => (prefix_refines_iff p q).mp (fun _ _ _ _ => all _ _), shaped_sound p q⟩

/-- Every failed normal-form comparison has a deterministic finite witness. -/
theorem exists_prefix_countermodel {p q : Endpoint} (fails : ¬ NormalRefines p q) :
    ∃ first next root step,
      let h := prefixHandler first next root step
      ¬ Shape.denote p.region h.model 0 ≤ Shape.denote q.region h.model 0 := by
  by_contra missing
  exact fails ((prefix_refines_iff p q).mp fun f g a b =>
    Classical.byContradiction fun bad => missing ⟨f, g, a, b, bad⟩)

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest
