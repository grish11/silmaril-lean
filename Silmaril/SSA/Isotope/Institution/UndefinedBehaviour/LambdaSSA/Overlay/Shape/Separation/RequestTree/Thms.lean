module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.RequestTree.Defs
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.RequestTree.Soundness
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.RequestTree.Separation

/-! # Depth-bounded separation of finite request trees -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.RequestTree

open TwoRequest (Instr Handler resultBehaviour)
open Category.FiniteIteration.Syntax (Bindings model)

universe v w

/-- The structural order is sound under the installed observation order.
Identical requests bind the same observations in both operands. This
argument also works for the unrestricted observational relations. -/
theorem sound (p q : Tree) (h : p.Refines q) {Γ : List (Silmaril.Ty Empty)}
    (M : Institution.Observational.Model.{0,v,w} Instr Γ.length) (s : M.σ) :
    Overlay.denote (p.region (Γ := Γ)) M s ≤ Overlay.denote (q.region (Γ := Γ)) M s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.RequestTree.sound p q h M s

theorem shaped_sound (p q : Tree) (h : p.Refines q) {Γ : List (Silmaril.Ty Empty)}
    (M : Shape.Model.{0,0,v,w} Instr Γ) (s : M.raw.σ) :
    Shape.denote p.region M s ≤ Shape.denote q.region M s :=
  sound p q h M.raw s

/-- Structural execution computes the full observation of the typed overlay
for a deterministic handler, including the final state of a fault. -/
theorem finite_observe {Γ : List (Silmaril.Ty Empty)} {n : Nat} (p : Tree) (h : Handler n)
    (env : Bindings Γ) (s : Fin n) :
    Shape.denote p.region (model h.primitives env) s = resultBehaviour (p.execute h s) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.RequestTree.finite_observe p h env s

/-- Every failed comparison has a deterministic shaped countermodel with
one machine state for each reply on the common prefix and one final state.
The common prefix is bounded by both tree depths. -/
theorem exists_prefix_countermodel {p q : Tree} (fails : ¬ p.Refines q) :
    ∃ (n : Nat) (probe : Prefix n), n ≤ min p.depth q.depth ∧
      ¬ Shape.denote p.region probe.handler.model 0 ≤ Shape.denote q.region probe.handler.model 0 :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.RequestTree.exists_prefix_countermodel fails

theorem shaped_refines_iff (p q : Tree) :
    (∀ (M : Shape.Model.{0,0,0,0} Instr []) (s : M.raw.σ),
      Shape.denote p.region M s ≤ Shape.denote q.region M s) ↔ p.Refines q := by
  refine ⟨fun all => Classical.byContradiction fun bad => ?_, fun order M s => shaped_sound p q order M s⟩
  obtain ⟨n, probe, _, h⟩ := exists_prefix_countermodel bad
  exact h (all probe.handler.model 0)

/-- The same shaped witnesses also refute the unrestricted observational
judgment. Both equivalences are stated at the witnesses' universes. -/
theorem raw_refines_iff (p q : Tree) :
    Overlay.Refines.{0,0,0,0} (p.region (Γ := [])) (q.region (Γ := [])) ↔ p.Refines q :=
  ⟨fun all => (shaped_refines_iff p q).mp (fun M s => all M.raw s), fun h M s => sound p q h M s⟩

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.RequestTree
