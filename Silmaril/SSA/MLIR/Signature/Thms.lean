module

public import Silmaril.SSA.MLIR.Signature.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
import Silmaril.Proofs.SSA.MLIR.Signature.Laws

public section

namespace Silmaril.MLIR.Institution.Signature

open CategoryTheory CategoryTheory.Limits

/-- Renamings between included signatures correspond exactly to regionless renamings. -/
def withRegionsFullyFaithful : withRegions.FullyFaithful :=
  Proofs.MLIR.Signature.withRegionsFullyFaithful

instance : withRegions.Full := withRegionsFullyFaithful.full

instance : withRegions.Faithful := withRegionsFullyFaithful.faithful

variable {withRegions : Bool} {S T U : Signature withRegions}

/-- Renamings agree when their sort maps and all their symbol images agree. -/
theorem hom_ext {f g : S ⟶ T} (sort_eq : f.sort = g.sort)
    (symbol_eq : ∀ {a : OpArity withRegions} {p : Profile a S.Ty} (o : S.Op p),
      HEq (f.symbol o) (g.symbol o)) : f = g :=
  Proofs.MLIR.Signature.hom_ext sort_eq symbol_eq

namespace disjointSum

@[simp] theorem inl_desc (f : S ⟶ U) (g : T ⟶ U) : inl S T ≫ desc f g = f := rfl

@[simp] theorem inr_desc (f : S ⟶ U) (g : T ⟶ U) : inr S T ≫ desc f g = g := rfl

/-- The mediator is uniquely determined by its restrictions to the two dialects. -/
theorem desc_unique (f : S ⟶ U) (g : T ⟶ U) (h : disjointSum S T ⟶ U)
    (hl : inl S T ≫ h = f) (hr : inr S T ≫ h = g) : h = desc f g :=
  Proofs.MLIR.Signature.disjointSum_uniq f g h hl hr

/-- The disjoint sum is a binary coproduct of signatures and renamings. -/
def isColimit (S T : Signature withRegions) : IsColimit (cofan S T) :=
  Proofs.MLIR.Signature.disjointSumIsColimit S T

end disjointSum

instance (S T : Signature withRegions) : HasBinaryCoproduct S T :=
  ⟨⟨disjointSum.cofan S T, disjointSum.isColimit S T⟩⟩

instance : HasBinaryCoproducts (Signature withRegions) :=
  hasBinaryCoproducts_of_hasColimit_pair _

end Silmaril.MLIR.Institution.Signature
