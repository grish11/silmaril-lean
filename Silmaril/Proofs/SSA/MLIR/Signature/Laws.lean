module

public import Silmaril.SSA.MLIR.Signature.Defs

public section

namespace Silmaril.Proofs.MLIR.Signature

open CategoryTheory CategoryTheory.Limits Silmaril.MLIR.Institution

variable {withRegions : Bool} {S T U : Signature withRegions}

theorem hom_ext {f g : S ⟶ T} (sort_eq : f.sort = g.sort)
    (symbol_eq : ∀ {a : OpArity withRegions} {p : Profile a S.Ty} (o : S.Op p),
      HEq (f.symbol o) (g.symbol o)) : f = g := by
  cases f
  cases g
  cases sort_eq
  congr
  funext a p o
  exact eq_of_heq (symbol_eq o)

section Inclusion

open Signature (RegionlessOp)

variable {A B : Signature false} {a : OpArity false} {p : Profile a A.Ty}

private def lower : RegionlessOp A p.withRegions → A.Op p := by
  cases a with
  | mk operands results regions =>
    cases regions
    cases p
    intro o
    cases o with
    | lift o => exact o

private theorem lower_lift (o : A.Op p) : lower (RegionlessOp.lift o) = o := by
  cases a
  cases p
  rfl

private theorem lift_lower (o : RegionlessOp A p.withRegions) : RegionlessOp.lift (lower o) = o := by
  cases a
  cases p
  cases o
  rfl

private def lowerRenaming (f : Signature.withRegions.obj A ⟶ Signature.withRegions.obj B) :
    A ⟶ B :=
  ⟨f.sort, fun o => lower (f.symbol (RegionlessOp.lift o))⟩

def withRegionsFullyFaithful : Signature.withRegions.FullyFaithful where
  preimage := lowerRenaming
  map_preimage {_ B} f := by
    refine hom_ext (by rfl) ?_
    intro a p o
    cases o with
    | @lift _ p o =>
      exact heq_of_eq (lift_lower (A := B) (p := p.map f.sort) (f.symbol (RegionlessOp.lift o)))
  preimage_map f := by
    refine hom_ext (by rfl) ?_
    intro a p o
    exact heq_of_eq (lower_lift (f.symbol o))

end Inclusion

private theorem symbol_heq {f g : S ⟶ T} (h : f = g)
    {a : OpArity withRegions} {p : Profile a S.Ty} (o : S.Op p) :
    HEq (f.symbol o) (g.symbol o) := by
  cases h
  rfl

open Signature.disjointSum in
theorem disjointSum_uniq (f : S ⟶ U) (g : T ⟶ U) (h : Signature.disjointSum S T ⟶ U)
    (hl : inl S T ≫ h = f) (hr : inr S T ≫ h = g) : h = desc f g := by
  apply hom_ext
  · funext s
    cases s with
    | inl s => exact congrArg (fun k : S ⟶ U => k.sort s) hl
    | inr s => exact congrArg (fun k : T ⟶ U => k.sort s) hr
  · intro a p o
    cases o with
    | inl o => exact symbol_heq hl o
    | inr o => exact symbol_heq hr o

open Signature.disjointSum in
def disjointSumIsColimit (S T : Signature withRegions) : IsColimit (cofan S T) :=
  BinaryCofan.IsColimit.mk _ desc
    (fun {_} _ _ => rfl) (fun {_} _ _ => rfl)
    (fun {_} f g h hl hr => disjointSum_uniq f g h hl hr)

end Silmaril.Proofs.MLIR.Signature
