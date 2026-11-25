module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryFan
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! Typed dialect signatures and profile-preserving renamings. The declarations keep the
`Silmaril.MLIR.Institution` namespace used by the pure equational institutions. -/

@[expose] public section

namespace Silmaril.MLIR.Institution

open CategoryTheory CategoryTheory.Limits

/-- The number of block arguments and yielded values of an isolated region. -/
structure RegionArity where
  params : Nat
  yields : Nat

/-- An ordered family of region slots, each with its own parameter and yield counts. -/
structure RegionSlots where
  count : Nat
  slot : Fin count → RegionArity

/-- Slot counts are independent of sorts. A regionless operation has no region slots. -/
structure OpArity (withRegions : Bool) where
  operands : Nat
  results : Nat
  regions : if withRegions then RegionSlots else Unit

/-- The ordered region slots of an operation. -/
abbrev OpArity.regionArities : {withRegions : Bool} → OpArity withRegions → RegionSlots
  | false, _ => ⟨0, Fin.elim0⟩
  | true, a => a.regions

abbrev OpArity.Region {withRegions : Bool} (a : OpArity withRegions) := Fin a.regionArities.count

abbrev OpArity.region {withRegions : Bool} (a : OpArity withRegions) (r : a.Region) : RegionArity :=
  a.regionArities.slot r

/-- Ordered sorts for operands, results, block arguments and yields. -/
structure Profile {withRegions : Bool} (a : OpArity withRegions) (Ty : Type) where
  operand : Fin a.operands → Ty
  result : Fin a.results → Ty
  param : (r : a.Region) → Fin (a.region r).params → Ty
  yield : (r : a.Region) → Fin (a.region r).yields → Ty

def Profile.map {withRegions : Bool} {a : OpArity withRegions} {Ty Ty' : Type}
    (f : Ty → Ty') (p : Profile a Ty) : Profile a Ty' where
  operand i := f (p.operand i)
  result i := f (p.result i)
  param r i := f (p.param r i)
  yield r i := f (p.yield r i)

/-- Regard a regionless operation as an operation with an empty list of region slots. -/
def OpArity.withRegions (a : OpArity false) : OpArity true :=
  ⟨a.operands, a.results, a.regionArities⟩

/-- Retain the operand and result sorts when adding empty region slots. -/
def Profile.withRegions {a : OpArity false} {Ty : Type} (p : Profile a Ty) :
    Profile a.withRegions Ty := ⟨p.operand, p.result, p.param, p.yield⟩

/-- A signature of symbols indexed by their full typed operation profile. -/
structure Signature (withRegions : Bool) where
  Ty : Type
  Op : {a : OpArity withRegions} → Profile a Ty → Type

/-- Maps may identify sorts and symbols. Every operand, result, block parameter and yield
retains its slot and has its sort mapped by `sort`. -/
structure Signature.Hom {withRegions : Bool} (S T : Signature withRegions) where
  sort : S.Ty → T.Ty
  symbol : ∀ {a : OpArity withRegions} {p : Profile a S.Ty}, S.Op p → T.Op (p.map sort)

instance {withRegions : Bool} : Category (Signature withRegions) where
  Hom := Signature.Hom
  id _ := ⟨id, id⟩
  comp f g := ⟨g.sort ∘ f.sort, fun o => g.symbol (f.symbol o)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

namespace Signature

/-- Symbols of a regionless signature, indexed by their profiles with empty region slots. -/
inductive RegionlessOp (S : Signature false) : {a : OpArity true} → Profile a S.Ty → Type
  | lift {a : OpArity false} {p : Profile a S.Ty} (o : S.Op p) : RegionlessOp S p.withRegions

/-- Include a regionless signature without adding sorts or operation symbols. -/
def withRegions : Signature false ⥤ Signature true where
  obj S := ⟨S.Ty, RegionlessOp S⟩
  map f := ⟨f.sort, fun
    | .lift o => .lift (f.symbol o)⟩
  map_id _ := by
    congr
    funext a p o
    cases o
    rfl
  map_comp _ _ := by
    congr
    funext a p o
    cases o
    rfl

variable {withRegions : Bool}

/-- Keep each dialect's symbols at their profiles with tagged sorts. -/
inductive SumOp (S T : Signature withRegions) :
    {a : OpArity withRegions} → Profile a (S.Ty ⊕ T.Ty) → Type
  | inl {a : OpArity withRegions} {p : Profile a S.Ty} (o : S.Op p) : SumOp S T (p.map Sum.inl)
  | inr {a : OpArity withRegions} {p : Profile a T.Ty} (o : T.Op p) : SumOp S T (p.map Sum.inr)

/-- The disjoint sum tags both sorts and symbols by dialect. -/
def disjointSum (S T : Signature withRegions) : Signature withRegions :=
  ⟨S.Ty ⊕ T.Ty, SumOp S T⟩

namespace disjointSum

variable {S T U : Signature withRegions}

/-- Include the left dialect in the disjoint sum. -/
def inl (S T : Signature withRegions) : S ⟶ disjointSum S T := ⟨Sum.inl, SumOp.inl⟩

/-- Include the right dialect in the disjoint sum. -/
def inr (S T : Signature withRegions) : T ⟶ disjointSum S T := ⟨Sum.inr, SumOp.inr⟩

/-- Combine renamings even when their sort maps have overlapping images. -/
def desc (f : S ⟶ U) (g : T ⟶ U) : disjointSum S T ⟶ U where
  sort := Sum.elim f.sort g.sort
  symbol
    | .inl o => f.symbol o
    | .inr o => g.symbol o

/-- The canonical binary cocone in the category of typed signatures and renamings. -/
def cofan (S T : Signature withRegions) : BinaryCofan S T :=
  BinaryCofan.mk (inl S T) (inr S T)

end disjointSum

end Signature

end Silmaril.MLIR.Institution
