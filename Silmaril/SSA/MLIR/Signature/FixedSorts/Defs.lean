module

public import Silmaril.SSA.MLIR.Signature.Defs

/-! Dialects on a common sort type, with symbol renamings that fix each sort. -/

@[expose] public section

namespace Silmaril.MLIR.Institution.Signature

open CategoryTheory CategoryTheory.Limits

/-- A typed signature on a specified set of sorts. -/
structure FixedSorts (withRegions : Bool) (Ty : Type) where
  Op : {a : OpArity withRegions} → Profile a Ty → Type

namespace FixedSorts

variable {withRegions : Bool} {Ty : Type}

/-- With sorts fixed, a renaming acts at each profile. -/
@[ext] structure Hom (S T : FixedSorts withRegions Ty) where
  symbol : ∀ {a : OpArity withRegions} {p : Profile a Ty}, S.Op p → T.Op p

instance : Category (FixedSorts withRegions Ty) where
  Hom := Hom
  id _ := ⟨id⟩
  comp f g := ⟨fun o => g.symbol (f.symbol o)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- Read a fixed-sort signature and its renamings in the general signature category. -/
def toSignature : FixedSorts withRegions Ty ⥤ Signature withRegions where
  obj S := ⟨Ty, S.Op⟩
  map f := ⟨id, f.symbol⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Combine symbol families profile by profile over the same sorts. -/
def sum (S T : FixedSorts withRegions Ty) : FixedSorts withRegions Ty :=
  ⟨fun p => S.Op p ⊕ T.Op p⟩

namespace sum

variable {S T U : FixedSorts withRegions Ty}

def inl (S T : FixedSorts withRegions Ty) : S ⟶ sum S T := ⟨Sum.inl⟩

def inr (S T : FixedSorts withRegions Ty) : T ⟶ sum S T := ⟨Sum.inr⟩

def desc (f : S ⟶ U) (g : T ⟶ U) : sum S T ⟶ U :=
  ⟨fun o => o.elim f.symbol g.symbol⟩

def cofan (S T : FixedSorts withRegions Ty) : BinaryCofan S T := BinaryCofan.mk (inl S T) (inr S T)

end sum

end FixedSorts

end Silmaril.MLIR.Institution.Signature
