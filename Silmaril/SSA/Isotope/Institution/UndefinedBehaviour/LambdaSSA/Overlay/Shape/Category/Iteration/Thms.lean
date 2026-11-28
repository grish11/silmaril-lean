module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Thms
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Monotonicity
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Typed

/-! # Refinement of repeated exact-sum observations -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category

open CategoryTheory

universe u v w x

variable {α : Type w} {σ : Type x} {κ : Type v} {atomType : α → κ → Prop} {A B : Ty κ}

/-- Pointwise refinement of the typed step suffices for ordered iteration.
Successors include the exact reply payload and final machine state. -/
theorem iterateObservations_mono
    {f g : single A ⟶ (single (.coprod B A) : Interface α σ atomType)}
    (le : ∀ (a : singlePayload (atomType := atomType) A) (s : σ), f.run (0 : Fin 1) a s ≤ g.run (0 : Fin 1) a s)
    (a : singlePayload (atomType := atomType) A) (s : σ) :
    iterateObservations f a s ≤ iterateObservations g a s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.Iteration.iterateObservations_mono le a s

/-- Close an exact-sum step in the shaped observation category. Ordinary
returns carry a typed payload of the left summand. -/
noncomputable def iterateSum
    (f : single A ⟶ (single (.coprod B A) : Interface α σ atomType)) :
    (single A : Interface α σ atomType) ⟶ single B where
  run _ a s := iterateObservations f (payloadAtZero a) s
  returnsTyped _ a s := by
    exact Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.Iteration.iterateObservations_typed f (payloadAtZero a) s

/-- The typed iterator is monotone under pointwise refinement of complete
step behaviours. -/
theorem iterateSum_mono
    {f g : single A ⟶ (single (.coprod B A) : Interface α σ atomType)}
    (le : ∀ (a : singlePayload (atomType := atomType) A) (s : σ), f.run 0 a s ≤ g.run 0 a s)
    (a : singlePayload (atomType := atomType) A) (s : σ) :
    (iterateSum f).run 0 a s ≤ (iterateSum g).run 0 a s :=
  iterateObservations_mono le a s

/-- Fresh UB occurs exactly when finitely many ordinary typed repeats reach
a step that exposes it. The path includes the zero-repeat case. -/
theorem iterateSum_eq_top_iff
    (f : single A ⟶ (single (.coprod B A) : Interface α σ atomType))
    (a : singlePayload (atomType := atomType) A) (s : σ) :
    (iterateSum f).run 0 a s = ⊤ ↔
      ∃ p, Relation.ReflTransGen (Repeat f) (a, s) p ∧ f.run 0 p.1 p.2 = ⊤ :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.Iteration.iterateObservations_top_iff f a s

/-- At a typed block, retagging preserves exactly the ordinary outcomes of
the step, including the state on each return or fault. -/
theorem iterationGraph_block_ordinary
    (f : single A ⟶ (single (.coprod B A) : Interface α σ atomType))
    (a b : singlePayload (atomType := atomType) A) (s : σ) (o : Outcome 2 α σ) :
    (iterationGraph f a (.block 0 b.val s)).Ordinary o ↔
      (f.run 0 b s).Ordinary (tagIterationOutcome o) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.Iteration.block_ordinary f a (b, s) o

/-- A start with an ordinary step and no repeat observes exactly that
step's terminal observations, with the left tag removed. -/
theorem iterateSum_no_repeat
    (f : single A ⟶ (single (.coprod B A) : Interface α σ atomType))
    (a : singlePayload (atomType := atomType) A) (s : σ)
    (noRepeat : ∀ p, ¬ Repeat f (a, s) p)
    {os : Set (Outcome 1 α σ)} (run : f.run 0 a s = ↑os) :
    (iterateSum f).run 0 a s =
      WithTop.some (Set.preimage (tagIterationOutcome ∘ Feedback.external [A] [B]) os) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.Iteration.iterateObservations_no_repeat f a s noRepeat os run

section OverlayStep

variable {Φ : Type u} [HasTy Φ (Ty κ)] {Γ : List (Ty κ)} (M : Shape.Model.{u,v,w,x} Φ Γ)

/-- Interpret any typed overlay region as a singleton arrow. Its one value
binder supplies the incoming payload ahead of the fixed captures. -/
noncomputable def interpretSingleton (r : Region Φ (A :: Γ) [B]) :
    single A ⟶ (single B : Interface M.raw.α M.raw.σ M.atomType) where
  run _ a s := Shape.denote r (M.extend (payloadAtZero a).property) s
  returnsTyped _ a s := Shape.returns_typed r (M.extend (payloadAtZero a).property) s

/-- Exact-sum iteration of an explicit overlay step, as a shaped arrow. -/
noncomputable def iterateOverlay (r : Region Φ (A :: Γ) [.coprod B A]) :
    single A ⟶ (single B : Interface M.raw.α M.raw.σ M.atomType) :=
  iterateSum (interpretSingleton M r)

/-- At an initial state the explicit-overlay iterator is greatest exactly
when an ordinary typed repeat path reaches a greatest step behaviour. -/
theorem iterateOverlay_eq_top_iff (r : Region Φ (A :: Γ) [.coprod B A])
    (a : singlePayload (atomType := M.atomType) A) (s : M.raw.σ) :
    (iterateOverlay M r).run 0 a s = ⊤ ↔
      ∃ p, Relation.ReflTransGen (Repeat (interpretSingleton M r)) (a, s) p ∧
        Shape.denote r (M.extend p.1.property) p.2 = ⊤ :=
  iterateSum_eq_top_iff (interpretSingleton M r) a s

/-- The existing overlay refinement supplies the pointwise comparison at
each typed invocation of the loop. -/
theorem iterateOverlay_mono {r t : Region Φ (A :: Γ) [.coprod B A]} (le : Refines.{u,v,w,x} r t)
    (a : singlePayload (atomType := M.atomType) A) (s : M.raw.σ) :
    (iterateOverlay M r).run 0 a s ≤ (iterateOverlay M t).run 0 a s :=
  iterateSum_mono (f := interpretSingleton M r) (g := interpretSingleton M t)
    (fun b t => le (M.extend b.property).raw t) a s

end OverlayStep

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
