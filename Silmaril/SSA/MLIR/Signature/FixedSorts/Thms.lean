module

public import Silmaril.SSA.MLIR.Signature.FixedSorts.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
import Silmaril.Proofs.SSA.MLIR.Signature.FixedSorts

public section

namespace Silmaril.MLIR.Institution.Signature.FixedSorts

open CategoryTheory CategoryTheory.Limits

variable {withRegions : Bool} {Ty : Type} {S T U : FixedSorts withRegions Ty}

namespace sum

@[simp] theorem inl_desc (f : S ⟶ U) (g : T ⟶ U) : inl S T ≫ desc f g = f := rfl

@[simp] theorem inr_desc (f : S ⟶ U) (g : T ⟶ U) : inr S T ≫ desc f g = g := rfl

theorem desc_unique (f : S ⟶ U) (g : T ⟶ U) (h : sum S T ⟶ U)
    (hl : inl S T ≫ h = f) (hr : inr S T ≫ h = g) : h = desc f g :=
  Proofs.MLIR.Signature.FixedSorts.desc_unique f g h hl hr

/-- The pointwise symbol sum is a binary coproduct when arrows fix the common sorts. -/
def isColimit (S T : FixedSorts withRegions Ty) : IsColimit (cofan S T) :=
  BinaryCofan.IsColimit.mk _ desc (fun {_} => inl_desc) (fun {_} => inr_desc)
    (fun {_} => desc_unique)

end sum

instance (S T : FixedSorts withRegions Ty) : HasBinaryCoproduct S T :=
  ⟨⟨sum.cofan S T, sum.isColimit S T⟩⟩

instance : HasBinaryCoproducts (FixedSorts withRegions Ty) :=
  hasBinaryCoproducts_of_hasColimit_pair _

end Silmaril.MLIR.Institution.Signature.FixedSorts
