module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Freyd.Iteration.Thms

/-! # Typing coherence for the chosen structural interpreter -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical

universe u v
variable {κ : Type u} {Φ : Type v} [HasTy Φ (Ty κ)]
  (Seed : VCtx (Ty κ) → Region Φ → Region Φ → LCtx (Ty κ) → Prop)
  [Fact (IncludesUnitEta Seed)]

local notation "inc" => inclusion Seed

attribute [local instance] valueCartesian valueBraided computationPremonoidal computationSymmetric
  computationDistributive valueDistributive hasFiniteCoproducts guardedIteration guardedElgot

/-- Install the graph's strong Elgot Freyd interface on the existing chosen
operations. The uniformity field belongs to the structural model. -/
@[expose, instance_reducible] noncomputable def strongElgotOfStructuralUniformity
    (uniform : StructuralUniformity Seed) : StrongElgotFreydCategory inc where
  toElgotFreydCategory := {
    toDistributiveFreydCategory := distributiveFreyd Seed
    uniformity := uniform }
  iterate_whiskerLeft Z f := iterate_whiskerLeft Seed Z f

/-- The graph's structural interpreter retains the central chosen unit. -/
theorem strongElgotCentralUnit (uniform : StructuralUniformity Seed) :
    letI := strongElgotOfStructuralUniformity Seed uniform
    FreydCategory.CentralUnit inc := by
  change @FreydCategory.CentralUnit _ _ _ _ _ _ _ _ inc (distributiveFreyd Seed).toFreydCategory
  rw [distributiveFreyd_toFreydCategory]
  exact centralUnit Seed

/-- The actual chosen structural interpretation is independent of graph
witnesses on determined exact regions. This uses the installed syntax type
model, projected instruction returns, and chosen guarded feedback. -/
theorem chosen_denoteRegion_eq (uniform : StructuralUniformity Seed)
    {Γ : VCtx (Ty κ)} {r : Region Φ} {L : LCtx (Ty κ)}
    (rigid : DeterminedRegion Γ r L) (t : Region.HasType Γ r L) :
    letI := strongElgotOfStructuralUniformity Seed uniform
    letI := instructions Seed
    ∀ {f}, RegionDenotes inc (typeModel Seed) t f →
      f = denoteRegion inc (typeModel Seed) t := by
  let strong := strongElgotOfStructuralUniformity Seed uniform
  let instr := instructions Seed
  intro f d
  exact rigid.eq_denoteRegion inc (typeModel Seed) d

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.StructuralValues
