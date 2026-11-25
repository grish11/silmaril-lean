module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Coproducts.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.Category.Freyd.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Syntactic.AbortSequence.CategoryDistributivity

/-! # Distributivity and coproduct preservation in the LetIter computation quotient -/

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Thesis.LambdaIter.Syn (SynCat)

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]
variable (pe : ε)

local notation "S" => signature (τ := τ) (Φ := Φ) pe
local notation "Q" => RepairedSynCat (τ := τ) (Φ := Φ) pe
local notation "P" => repairedProjection (τ := τ) (Φ := Φ) pe
local notation "Jq" => repairedValues (τ := τ) (Φ := Φ) pe
local notation "cmp" => repairedProjectionCoprodIso pe

/-- The exact-to-repaired projection preserves the initial computation object. -/
instance repairedProjection_preservesInitial :
    PreservesColimit (Functor.empty.{0} (SynCat S)) (P) :=
  preservesColimit_of_preserves_colimit_cocone (initialIsInitial (C := SynCat S))
    ((isColimitMapCoconeEmptyCoconeEquiv (P) _).symm (repairedProjection_initial pe))

instance repairedProjection_preservesBinaryCoproduct (X Y : SynCat S) :
    PreservesColimit (pair X Y) (P) :=
  preservesColimit_of_preserves_colimit_cocone (coprodIsCoprod X Y)
    ((isColimitMapCoconeBinaryCofanEquiv (P) _ _).symm (repairedProjection_coprodIsColimit pe X Y))

instance repairedProjection_preservesBinaryCoproducts :
    PreservesColimitsOfShape (Discrete WalkingPair) (P) where
  preservesColimit {K} := preservesColimit_of_iso_diagram (P) (diagramIsoPair K).symm

/-- The exact-to-repaired projection preserves finite coproducts. -/
instance repairedProjection_preservesFiniteCoproducts : PreservesFiniteCoproducts (P) where
  preserves n :=
    let := preservesColimitsOfShape_pempty_of_preservesInitial (P)
    PreservesFiniteCoproducts.of_preserves_binary_and_initial (P) (Fin n)

/-- The projected value inclusion preserves finite coproducts. -/
theorem repairedValues_preservesFiniteCoproducts : PreservesFiniteCoproducts (Jq) :=
  inferInstance

/-- The left distributor commutes with projection after comparing coproducts. -/
theorem repairedProjection_leftDistributor (X Y Z : SynCat S) :
    (cmp (X ⊗ Y) (X ⊗ Z)).hom ≫ DistributiveTensor.leftHom ((P).obj X) ((P).obj Y) ((P).obj Z) =
      (P).map (DistributiveTensor.leftHom X Y Z) ≫ (P).obj X ◁ (cmp Y Z).hom :=
  RepairedDistributiveProofs.repairedProjection_leftDistributor pe X Y Z

/-- The canonical left distributor of the computation quotient is invertible. -/
instance repairedDistributiveTensor : DistributiveTensor Q where
  left_isIso := by exact RepairedDistributiveProofs.repairedLeftDistributor_isIso pe

/-- The value inclusion and computation tensor give a distributive Freyd category. -/
noncomputable instance repairedDistributiveFreyd : DistributiveFreydCategory (Jq) where
  preservesFiniteCoproducts := repairedValues_preservesFiniteCoproducts pe

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic
