module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Acyclic.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.AcyclicStepUniformity

/-! # Uniformity from an acyclic source decomposition -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open CategoryTheory CategoryTheory.Limits
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed

/-- The fixed-point equation for an acyclic step determines its result. -/
theorem AcyclicStep.fixedPoint_unique {A B : Q} {f : A ⟶ B ⨿ A} (bound : AcyclicStep Seed B f)
    (u v : A ⟶ B)
    (hu : u = f ≫ coprod.desc (𝟙 B) u) (hv : v = f ≫ coprod.desc (𝟙 B) v) : u = v :=
  AcyclicStepUniformity.fixedPoint_unique Seed bound u v hu hv

/-- A square in the actual quotient is uniform when the source step admits an
acyclic decomposition into finitely many strata. The state map and target step are arbitrary. -/
theorem uniformity_of_acyclic {A B D : Q} (h : A ⟶ D)
    {f : A ⟶ B ⨿ A} (bound : AcyclicStep Seed B f) (g : D ⟶ B ⨿ D)
    (comm : f ≫ coprod.map (𝟙 B) h = h ≫ g) :
    iterateChosen Seed f = h ≫ iterateChosen Seed g :=
  AcyclicStepUniformity.uniformity_of_acyclic Seed h bound g comm

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
