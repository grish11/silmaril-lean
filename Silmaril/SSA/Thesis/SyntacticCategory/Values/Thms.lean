module

public import Silmaril.SSA.Thesis.SyntacticCategory.Values.Defs
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Silmaril.Proofs.SSA.Thesis.SyntacticCategory.Values

/-! # Finite products and coproducts of the syntactic λiter value category -/

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory CategoryTheory.Limits
open LocallyNameless

variable {S : Sig.{u}}

/-- The syntactic unit is terminal for arrows with a pure representative. -/
def valueUnitIsTerminal (S : Sig.{u}) :
    IsTerminal (C := ValueCat S) ⟨of (unit : S.Ty)⟩ :=
  IsTerminal.ofUniqueHom (fun _ => ⟨mk HasType.unit, ⟨.unit, .unit, .unit, rfl⟩⟩)
    (fun _ f => WideSubcategory.hom_ext (pureProperty S) (pureToUnit_unique_proof f.property))

instance valuesHasTerminal (S : Sig.{u}) : HasTerminal (ValueCat S) :=
  (valueUnitIsTerminal S).hasTerminal

/-- Empty elimination has a pure representative, giving an initial value object. -/
def valueEmptyIsInitial (S : Sig.{u}) :
    IsInitial (C := ValueCat S) ⟨of (empty : S.Ty)⟩ :=
  IsInitial.ofUniqueHom
    (fun A => ⟨mk (HasType.abort (C := A.obj.ty) HasType.newest),
      ⟨.abort (.bv 0), .abort HasType.newest, .abort .bv, rfl⟩⟩)
    (fun A f => WideSubcategory.hom_ext (pureProperty S) (fromEmpty_unique A.obj f.hom _))

instance valuesHasInitial (S : Sig.{u}) : HasInitial (ValueCat S) :=
  (valueEmptyIsInitial S).hasInitial

/-- The left syntactic injection has a pure representative. -/
theorem isPureMor_injl (A B : SynCat S) : IsPureMor (injl A B) :=
  isPureMor_injl_proof A B

/-- The right syntactic injection has a pure representative. -/
theorem isPureMor_injr (A B : SynCat S) : IsPureMor (injr A B) :=
  isPureMor_injr_proof A B

/-- The two syntax injections have pure representatives. -/
@[expose] def valueCofan (A B : ValueCat S) : BinaryCofan A B :=
  BinaryCofan.mk (P := ⟨cop A.obj B.obj⟩)
    ⟨injl A.obj B.obj, isPureMor_injl _ _⟩
    ⟨injr A.obj B.obj, isPureMor_injr _ _⟩

/-- Copairing two pure representatives gives a pure representative of the copairing. -/
def valueCofanIsColimit (A B : ValueCat S) : IsColimit (valueCofan A B) :=
  BinaryCofan.isColimitMk
    (fun s => ⟨desc s.inl.hom s.inr.hom, isPureMor_desc_proof s.inl.property s.inr.property⟩)
    (fun s => WideSubcategory.hom_ext (pureProperty S) (injl_desc _ _))
    (fun s => WideSubcategory.hom_ext (pureProperty S) (injr_desc _ _))
    (fun s m hl hr => WideSubcategory.hom_ext (pureProperty S) (by
      have left : injl A.obj B.obj ≫ m.hom = s.inl.hom := congrArg (fun f => f.hom) hl
      have right : injr A.obj B.obj ≫ m.hom = s.inr.hom := congrArg (fun f => f.hom) hr
      rw [desc_uniq m.hom, left, right]))

instance valueHasBinaryCoproduct (A B : ValueCat S) : HasBinaryCoproduct A B :=
  ⟨⟨⟨_, valueCofanIsColimit A B⟩⟩⟩

instance valuesHasBinaryCoproducts (S : Sig.{u}) : HasBinaryCoproducts (ValueCat S) :=
  hasBinaryCoproducts_of_hasColimit_pair _

instance valuesHasFiniteCoproducts (S : Sig.{u}) : HasFiniteCoproducts (ValueCat S) :=
  hasFiniteCoproducts_of_has_binary_and_initial

instance valuesPreservesInitial (S : Sig.{u}) :
    PreservesColimit (Functor.empty.{0} (ValueCat S)) (values S) :=
  preservesColimit_of_preserves_colimit_cocone (valueEmptyIsInitial S)
    ((isColimitMapCoconeEmptyCoconeEquiv (values S) _).symm (isInitialEmpty S))

instance valuesPreservesBinaryCoproduct (A B : ValueCat S) :
    PreservesColimit (pair A B) (values S) :=
  preservesColimit_of_preserves_colimit_cocone (valueCofanIsColimit A B)
    ((isColimitMapCoconeBinaryCofanEquiv (values S) _ _).symm (isColimitBinaryCofan A.obj B.obj))

instance valuesPreservesBinaryCoproducts (S : Sig.{u}) :
    PreservesColimitsOfShape (Discrete WalkingPair) (values S) where
  preservesColimit {K} := preservesColimit_of_iso_diagram (values S) (diagramIsoPair K).symm

instance valuesPreservesFiniteCoproducts (S : Sig.{u}) : PreservesFiniteCoproducts (values S) where
  preserves n :=
    let := preservesColimitsOfShape_pempty_of_preservesInitial (values S)
    PreservesFiniteCoproducts.of_preserves_binary_and_initial (values S) (Fin n)

/-- The first projection of a pair reduces when the discarded second term is pure. -/
theorem first_beta {n : Nat} {β : BoundCtx S.Ty n}
    {a b : Tm Empty S.Instr n} {A B : S.Ty}
    (ha : HasType S.Instr Ctx.nil β a A) (hb : HasType S.Instr Ctx.nil β b B)
    (hp : Pure S.pureEff b) :
    Eqv S.pureEff Ctx.nil β (.let₂ (.pair a b) (.bv 1)) a A :=
  first_beta_proof ha hb hp

/-- The second projection of a pair reduces when the discarded first term is pure. -/
theorem second_beta {n : Nat} {β : BoundCtx S.Ty n}
    {a b : Tm Empty S.Instr n} {A B : S.Ty}
    (ha : HasType S.Instr Ctx.nil β a A) (hb : HasType S.Instr Ctx.nil β b B)
    (hp : Pure S.pureEff a) :
    Eqv S.pureEff Ctx.nil β (.let₂ (.pair a b) (.bv 0)) b B :=
  second_beta_proof ha hb hp

/-- Pairing the projections of a pure term recovers that term. -/
theorem pair_projections_eta {n : Nat} {β : BoundCtx S.Ty n}
    {p : Tm Empty S.Instr n} {A B : S.Ty}
    (h : HasType S.Instr Ctx.nil β p (tensor A B)) (hp : Pure S.pureEff p) :
    Eqv S.pureEff Ctx.nil β (.pair (.let₂ p (.bv 1)) (.let₂ p (.bv 0))) p (tensor A B) :=
  pair_projections_eta_proof h hp

/-- First projection has a syntactically pure representative. -/
theorem isPureMor_first (A B : SynCat S) : IsPureMor (first A B) :=
  isPureMor_first_proof A B

/-- Second projection has a syntactically pure representative. -/
theorem isPureMor_second (A B : SynCat S) : IsPureMor (second A B) :=
  isPureMor_second_proof A B

/-- The syntactic projections are value morphisms. -/
@[expose] def valueFan (A B : ValueCat S) : BinaryFan A B :=
  BinaryFan.mk (P := ⟨productObj A.obj B.obj⟩)
    ⟨first A.obj B.obj, isPureMor_first _ _⟩
    ⟨second A.obj B.obj, isPureMor_second _ _⟩

/-- Pairing of pure terms gives the universal arrow into the syntactic product. -/
def valueFanIsLimit (A B : ValueCat S) : IsLimit (valueFan A B) :=
  BinaryFan.isLimitMk
    (fun s => ⟨pairArrows s.fst.hom s.snd.hom, isPureMor_pairArrows_proof s.fst.property s.snd.property⟩)
    (fun s => WideSubcategory.hom_ext (pureProperty S)
      (pairArrows_first_proof s.fst.property s.snd.property))
    (fun s => WideSubcategory.hom_ext (pureProperty S)
      (pairArrows_second_proof s.fst.property s.snd.property))
    (fun s m hl hr => WideSubcategory.hom_ext (pureProperty S) (by
      have left : m.hom ≫ first A.obj B.obj = s.fst.hom := congrArg (fun f => f.hom) hl
      have right : m.hom ≫ second A.obj B.obj = s.snd.hom := congrArg (fun f => f.hom) hr
      exact (pairArrows_uniq_proof m.property).trans (congrArg₂ pairArrows left right)))

/-- The value category has Cartesian tensor given by syntactic pairing. -/
instance valuesCartesianMonoidal (S : Sig.{u}) : CartesianMonoidalCategory (ValueCat S) :=
  CartesianMonoidalCategory.ofChosenFiniteProducts ⟨_, valueUnitIsTerminal S⟩ fun A B =>
    ⟨_, valueFanIsLimit A B⟩

/-- Cartesian pairing in the value category has the indicated syntax representative. -/
theorem valueLift_hom {X A B : ValueCat S} (f : X ⟶ A) (g : X ⟶ B) :
    (CartesianMonoidalCategory.lift f g).hom = pairArrows f.hom g.hom := by rfl

/-- Pairing two pure representatives preserves purity. -/
theorem isPureMor_pairArrows {X A B : SynCat S} {f : X ⟶ A} {g : X ⟶ B}
    (hf : IsPureMor f) (hg : IsPureMor g) : IsPureMor (pairArrows f g) :=
  isPureMor_pairArrows_proof hf hg

end Silmaril.Thesis.LambdaIter.Syn.SynCat
