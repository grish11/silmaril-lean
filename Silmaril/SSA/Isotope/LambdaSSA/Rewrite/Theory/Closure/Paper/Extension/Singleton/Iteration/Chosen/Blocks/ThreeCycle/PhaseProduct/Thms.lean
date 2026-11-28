module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.PhaseProduct.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Products.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturns.Values.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PhaseProductThreeCycle
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PhaseProductUniformity
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycleRecurrence

/-! # The phase-product square and tripling through one recursive packet -/

public section

universe u v w

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.PhaseProduct

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "P" => TypeCategory (τ := τ) Φ

/-- The two guarded distributors turn phase projection into the copair of
three native Unit-factor projections. -/
theorem split_payload (A : τ) :
    (split (Φ := Φ) A).hom ≫ payload A =
      coprod.desc (rightUnitProjection A) (coprod.desc (rightUnitProjection A) (rightUnitProjection A)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PhaseProductThreeCycle.split_payload A

/-- The literal payload projection commutes with a cyclic, product-state
version of an arbitrary standard Paper round. The result type is unchanged. -/
theorem native_square {A : τ} {B : P} (f : ofType A ⟶ B ⨿ ofType A) :
    step f ≫ coprod.map (𝟙 B) (payload A) = payload A ≫ f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PhaseProductThreeCycle.native_square f

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.PhaseProduct

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "I" => iterateChosen Seed

/-- The payload projection is central and preserves copy and discard
in the contextual quotient. -/
theorem phase_payload_mem (A : τ) :
    StructuralValues.HomProperty Seed
      ((projection Seed).map (Paper.TypeCategory.PhaseProduct.payload (Φ := Φ) A)) :=
  StructuralValues.fst_mem Seed A (Paper.TypeCategory.PhaseProduct.Phase (τ := τ))

/-- A quotient containing the projection-return equations also has an exact
pure-return witness for the payload map. -/
theorem phase_payload_return {ε : Type w} [HasEff Φ ε] (pe : ε)
    (includeProjection : ∀ {Γ L r s}, Paper.WithProjectionReturns.Step Γ r s L → Seed Γ r s L)
    (A : τ) :
    ProjectedCopyingReturn Seed pe
      ((projection Seed).map (Paper.TypeCategory.PhaseProduct.payload (Φ := Φ) A)) :=
  Paper.WithProjectionReturns.fst_mem pe Seed includeProjection A Paper.TypeCategory.PhaseProduct.Phase

/-- Projection preserves the actual native phase-product square. -/
theorem phase_projected_square {A : τ} {B : Paper.TypeCategory (τ := τ) Φ}
    (f : Paper.TypeCategory.ofType A ⟶ B ⨿ Paper.TypeCategory.ofType A) :
    let h := (projection Seed).map (Paper.TypeCategory.PhaseProduct.payload (Φ := Φ) A)
    projectStep Seed (Paper.TypeCategory.PhaseProduct.step f) ≫
      coprod.map (𝟙 ((projection Seed).obj B)) h = h ≫ projectStep Seed f :=
  (projectSquare_iff Seed _ _ _).mpr
    (congrArg (projection Seed).map (Paper.TypeCategory.PhaseProduct.native_square f))

/-- With Unit η, uniformity for the written phase-product square is exactly
tripling at the projected round. This comparison uses only an invertible
change of state for the three packet copies. -/
theorem phase_uniformity_iff_triple
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L)
    {A : τ} {B : Paper.TypeCategory (τ := τ) Φ}
    (f : Paper.TypeCategory.ofType A ⟶ B ⨿ Paper.TypeCategory.ofType A) :
    let h := (projection Seed).map (Paper.TypeCategory.PhaseProduct.payload (Φ := Φ) A)
    I (projectStep Seed (Paper.TypeCategory.PhaseProduct.step f)) = h ≫ I (projectStep Seed f) ↔
      I (triple (projectStep Seed f)) = I (projectStep Seed f) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PhaseProductUniformity.phase_uniformity_iff_triple
    Seed includeUnit f

/-- If recursive outputs travel through another state type, tripling there
suffices. The restoring arrow can be an arbitrary computation. -/
theorem triple_step_through {A D B : Q} (first : A ⟶ B ⨿ D) (restore : D ⟶ A)
    (small : I (triple (restore ≫ first)) = I (restore ≫ first)) :
    let g := first ≫ coprod.map (𝟙 B) restore
    I (triple g) = I g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycleRecurrence.triple_step_through
    Seed first restore small

/-- Arbitrary payload steps with recursion through one Unit packet admit tripling.
The initial step can inspect the payload, execute effects and exit. -/
theorem triple_step_through_unit
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L)
    {A B : Q} (first : A ⟶ B ⨿ ofType Seed (Silmaril.unit : τ))
    (restore : ofType Seed (Silmaril.unit : τ) ⟶ A) :
    let g := first ≫ coprod.map (𝟙 B) restore
    I (triple g) = I g :=
  triple_step_through Seed first restore (triple_step_unit Seed includeUnit (restore ≫ first))

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle
