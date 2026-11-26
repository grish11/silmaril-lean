module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Defs
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
