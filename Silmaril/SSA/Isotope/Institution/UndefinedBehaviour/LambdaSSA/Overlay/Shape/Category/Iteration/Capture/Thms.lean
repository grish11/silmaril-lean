module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Product.Thms

/-! # Exact-sum iteration at a packed capture and seed -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category

open CategoryTheory

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {X A B : Ty κ}
variable (M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ)))

local notation "Payload" => singlePayload (atomType := M.atomType)

/-- An input product contains a fixed capture pack on the left and the
initial loop payload on the right. The iterator closes the step over that
capture and each repeat supplies only a new payload and machine state. -/
noncomputable def iterateCaptured (r : Region Φ [A, X] [.coprod B A]) :
    single (.product X A) ⟶ (single B : Interface M.raw.α M.raw.σ M.atomType) where
  run _ p s :=
    let (capture, seed) := splitPair (payloadAtZero p)
    (iterateOverlay (M.extend capture.property) r).run 0 seed s
  returnsTyped _ p s := by
    obtain ⟨capture, seed⟩ := splitPair (payloadAtZero p)
    exact (iterateOverlay (M.extend capture.property) r).returnsTyped 0 seed s

@[simp] theorem iterateCaptured_run (r : Region Φ [A, X] [.coprod B A])
    (c : Payload X) (a : Payload A) (s : M.raw.σ) :
    (iterateCaptured M r).run 0 (pairPayload c a) s =
      (iterateOverlay (M.extend c.property) r).run 0 a s :=
  rfl

/-- Each start uses a single capture environment in both the repeat relation
and the final UB test. -/
theorem iterateCaptured_eq_top_iff (r : Region Φ [A, X] [.coprod B A])
    (c : Payload X) (a : Payload A) (s : M.raw.σ) :
    (iterateCaptured M r).run 0 (pairPayload c a) s = ⊤ ↔
      ∃ p, Relation.ReflTransGen (Repeat (interpretSingleton (M.extend c.property) r)) (a, s) p ∧
        Shape.denote r ((M.extend c.property).extend p.1.property) p.2 = ⊤ :=
  iterateOverlay_eq_top_iff (M.extend c.property) r a s

/-- Refining the step preserves the order of the packed arrows pointwise. -/
theorem iterateCaptured_mono {r t : Region Φ [A, X] [.coprod B A]} (le : Refines.{u,v,w,x} r t)
    (p : Payload (.product X A)) (s : M.raw.σ) :
    (iterateCaptured M r).run 0 p s ≤ (iterateCaptured M t).run 0 p s :=
  iterateOverlay_mono (M.extend (splitPair p).1.property) le (splitPair p).2 s

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
