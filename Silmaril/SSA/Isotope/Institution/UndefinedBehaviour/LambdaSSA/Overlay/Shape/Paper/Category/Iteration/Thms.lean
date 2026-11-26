module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.ExactSum.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Defs
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Paper.Category.Iteration.Preservation

/-! # Bind-first exact-sum iteration in the shaped stateful target -/

public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper

open CategoryTheory
open LambdaSSA.Region.Paper.TypeCategory (ofType iterateSum)
open Shape.Category (singlePayload iterationGraph iterateObservations sumDesc)

universe u v w x

variable {Φ : Type u} {κ : Type v} [HasTy Φ (Ty κ)] {A B : Ty κ}
variable (M : Shape.Model.{u,v,w,x} Φ ([] : List (Ty κ)))
variable (f : ofType (Φ := Φ) A ⟶ ofType (.coprod B A))
variable (a : singlePayload (atomType := M.atomType) A) (s : M.raw.σ)

/-- The installed exact-sum iterator agrees with repeated observations of the
step at the preceding reply's payload and final machine state. The equality
includes faults, step divergence and infinite replay of repeats. -/
theorem singleton_map_iterateSum :
    ((singletonInterpretation M).map (iterateSum f)).run (0 : Fin 1) a s =
      iterateObservations ((singletonInterpretation M).map f) a s :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Iteration.map_iterateSum M f a s

/-- The typed observation iterator extends the installed guarded iterator. -/
theorem singleton_map_iterateSum_eq_shaped :
    (singletonInterpretation M).map (iterateSum f) =
      Shape.Category.iterateSum ((singletonInterpretation M).map f) := by
  apply Shape.Category.arrow_ext
  intro i b t
  obtain rfl := Fin.eq_zero i
  exact singleton_map_iterateSum M f b t

/-- On a native step representative the explicit-overlay interface agrees
with the installed guarded iterator, including faults and divergence. -/
theorem singleton_map_iterateSum_eq_overlay {r : LambdaSSA.Region Φ}
    (hr : r.ValueBranches [A] [.coprod B A]) :
    (singletonInterpretation M).map (iterateSum (LambdaSSA.Region.Paper.TypeCategory.ofRegion hr)) =
      Shape.Category.iterateOverlay M (.native ⟨r, hr.hasType⟩) :=
  singleton_map_iterateSum_eq_shaped M (LambdaSSA.Region.Paper.TypeCategory.ofRegion hr)

/-- The installed iterator is monotone in the shaped observation order.
Larger behaviour includes additional ordinary outcomes or fresh top. -/
theorem singleton_map_iterateSum_mono {g : ofType (Φ := Φ) A ⟶ ofType (.coprod B A)}
    (le : ∀ (b : singlePayload (atomType := M.atomType) A) (t : M.raw.σ),
      ((singletonInterpretation M).map f).run (0 : Fin 1) b t ≤
        ((singletonInterpretation M).map g).run (0 : Fin 1) b t) :
    ((singletonInterpretation M).map (iterateSum f)).run (0 : Fin 1) a s ≤
      ((singletonInterpretation M).map (iterateSum g)).run (0 : Fin 1) a s := by
  exact (singleton_map_iterateSum M f a s).trans_le
    ((Shape.Category.iterateObservations_mono le a s).trans_eq (singleton_map_iterateSum M g a s).symm)

/-- An existing overlay refinement of native representatives implies ordered
iteration in every shaped model of the same universe. -/
theorem singleton_map_iterateSum_mono_of_refines {r t : LambdaSSA.Region Φ}
    (hr : r.ValueBranches [A] [.coprod B A]) (ht : t.ValueBranches [A] [.coprod B A])
    (le : Refines.{u,v,w,x} (.native ⟨r, hr.hasType⟩) (.native ⟨t, ht.hasType⟩)) :
    ((singletonInterpretation M).map (iterateSum (LambdaSSA.Region.Paper.TypeCategory.ofRegion hr))).run
        (0 : Fin 1) a s ≤
      ((singletonInterpretation M).map (iterateSum (LambdaSSA.Region.Paper.TypeCategory.ofRegion ht))).run
        (0 : Fin 1) a s :=
  singleton_map_iterateSum_mono M _ a s fun b t => le (M.extend b.property).raw t

/-- Unfold the interpreted iterator into one step followed by the selected
arm. The right arm starts the remainder at that step's final state. -/
theorem singleton_map_iterateSum_unfold :
    (singletonInterpretation M).map (iterateSum f) =
      (singletonInterpretation M).map f ≫ sumDesc (𝟙 _) ((singletonInterpretation M).map (iterateSum f)) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Iteration.map_iterateSum_unfold M f

/-- The native guarded step and iterator always produce ordinary behaviour. -/
theorem singleton_map_ne_top {D E : Ty κ} (g : ofType (Φ := Φ) D ⟶ ofType E)
    (b : singlePayload (atomType := M.atomType) D) (t : M.raw.σ) :
    ((singletonInterpretation M).map g).run (0 : Fin 1) b t ≠ ⊤ :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Iteration.map_ne_top M g b t

/-- With native generated steps every finite external outcome is observed.
The additional divergence observation is exactly infinite ordinary replay. -/
theorem singleton_iterateSum_ordinary_iff (o : Outcome 1 M.raw.α M.raw.σ) :
    (((singletonInterpretation M).map (iterateSum f)).run (0 : Fin 1) a s).Ordinary o ↔
      Feedback.Finite (iterationGraph ((singletonInterpretation M).map f) a) (.entry s) o ∨
      o = .diverge ∧ Feedback.Infinite (iterationGraph ((singletonInterpretation M).map f) a) (.entry s) :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Paper.Category.Iteration.iterateSum_ordinary_iff M f a s o

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Paper
