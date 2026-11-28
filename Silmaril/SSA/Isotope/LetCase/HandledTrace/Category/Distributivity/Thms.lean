module

public import Silmaril.SSA.Isotope.LetCase.HandledTrace.Category.Distributivity.Defs
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Silmaril.Proofs.SSA.Isotope.LetCase.HandledTrace.Category.Distributivity.Runs
import Silmaril.Proofs.SSA.Isotope.LetCase.HandledTrace.Category.Distributivity.Cofan

@[expose] public section

namespace Silmaril.Isotope.LetCase.HandledTrace

open CategoryTheory CategoryTheory.Limits Silmaril.Isotope.Semantics Silmaril.Elgot.ITree

universe u v e s

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {D : τ → Type (e + 1)} [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
  {Events : Type e → Type e} {State : Type s}
  {M : InstructionModel D Φ (Tree Events)} {policy : Handler State Events}

namespace Program

variable {K A B C : τ}

theorem distribLeft_pure (K A B : τ) : (distribLeft (Φ := Φ) K A B).HasPureRun M :=
  DistributivityProofs.left_pure K A B

theorem distribRight_pure (A B K : τ) : (distribRight (Φ := Φ) A B K).HasPureRun M :=
  DistributivityProofs.right_pure A B K

theorem mergeLeft_pure (K A B : τ) : (mergeLeft (Φ := Φ) K A B).HasPureRun M :=
  DistributivityProofs.left_merge_pure K A B

theorem mergeRight_pure (A B K : τ) : (mergeRight (Φ := Φ) A B K).HasPureRun M :=
  DistributivityProofs.right_merge_pure A B K

/-- Distributing and then running the selected whiskered arm gives the
same tree as whiskering native case. -/
theorem run_whiskerLeft_desc (p : Program Φ A C) (q : Program Φ B C) (input : D (product K (coprod A B))) :
    ((p.desc q).whiskerLeft K).run M input =
      ((distribLeft K A B).seq ((p.whiskerLeft K).desc (q.whiskerLeft K))).run M input :=
  DistributivityProofs.run_whiskerLeft_desc p q input

theorem run_whiskerRight_desc (p : Program Φ A C) (q : Program Φ B C) (input : D (product (coprod A B) K)) :
    ((p.desc q).whiskerRight K).run M input =
      ((distribRight A B K).seq ((p.whiskerRight K).desc (q.whiskerRight K))).run M input :=
  DistributivityProofs.run_whiskerRight_desc p q input

end Program

namespace Arrow

/-- The chosen left distributor carries the written merge and split maps. -/
def leftDistributor (K A B : Interface M policy) : (K.tensor A).sum (K.tensor B) ≅ K.tensor (A.sum B) where
  hom := desc ((tensorLeft K).map (inl A B)) ((tensorLeft K).map (inr A B))
  inv := ofProgram (Program.distribLeft K.ty A.ty B.ty)
  hom_inv_id := by exact Quotient.sound (DistributivityProofs.left_merge_split K.ty A.ty B.ty)
  inv_hom_id := by exact Quotient.sound (DistributivityProofs.left_split_merge K.ty A.ty B.ty)

/-- The chosen right distributor carries the written merge and split maps. -/
def rightDistributor (A B K : Interface M policy) : (A.tensor K).sum (B.tensor K) ≅ (A.sum B).tensor K where
  hom := desc ((tensorRight K).map (inl A B)) ((tensorRight K).map (inr A B))
  inv := ofProgram (Program.distribRight A.ty B.ty K.ty)
  hom_inv_id := by exact Quotient.sound (DistributivityProofs.right_merge_split A.ty B.ty K.ty)
  inv_hom_id := by exact Quotient.sound (DistributivityProofs.right_split_merge A.ty B.ty K.ty)

theorem leftDistributor_hom (K A B : Interface M policy) :
    (leftDistributor K A B).hom = ofProgram (Program.mergeLeft K.ty A.ty B.ty) :=
  rfl

theorem rightDistributor_hom (A B K : Interface M policy) :
    (rightDistributor A B K).hom = ofProgram (Program.mergeRight A.ty B.ty K.ty) :=
  rfl

theorem leftDistributor_central (K A B : Interface M policy) :
    PremonoidalCategory.IsCentral (leftDistributor K A B).hom ∧
      PremonoidalCategory.IsCentral (leftDistributor K A B).inv := by
  have h := isCentral_of_pureRun (A := K.tensor (A.sum B)) (B := (K.tensor A).sum (K.tensor B))
    (Program.distribLeft_pure (M := M) K.ty A.ty B.ty)
  exact ⟨h.inv (leftDistributor K A B).symm, h⟩

theorem rightDistributor_central (A B K : Interface M policy) :
    PremonoidalCategory.IsCentral (rightDistributor A B K).hom ∧
      PremonoidalCategory.IsCentral (rightDistributor A B K).inv := by
  have h := isCentral_of_pureRun (A := (A.sum B).tensor K) (B := (A.tensor K).sum (B.tensor K))
    (Program.distribRight_pure (M := M) A.ty B.ty K.ty)
  exact ⟨h.inv (rightDistributor A B K).symm, h⟩

@[simp] theorem inl_leftDistributor (K A B : Interface M policy) :
    inl (K.tensor A) (K.tensor B) ≫ (leftDistributor K A B).hom = (tensorLeft K).map (inl A B) :=
  inl_desc ((tensorLeft K).map (inl A B)) ((tensorLeft K).map (inr A B))

@[simp] theorem inr_leftDistributor (K A B : Interface M policy) :
    inr (K.tensor A) (K.tensor B) ≫ (leftDistributor K A B).hom = (tensorLeft K).map (inr A B) :=
  inr_desc ((tensorLeft K).map (inl A B)) ((tensorLeft K).map (inr A B))

@[simp] theorem inl_rightDistributor (A B K : Interface M policy) :
    inl (A.tensor K) (B.tensor K) ≫ (rightDistributor A B K).hom = (tensorRight K).map (inl A B) :=
  inl_desc ((tensorRight K).map (inl A B)) ((tensorRight K).map (inr A B))

@[simp] theorem inr_rightDistributor (A B K : Interface M policy) :
    inr (A.tensor K) (B.tensor K) ≫ (rightDistributor A B K).hom = (tensorRight K).map (inr A B) :=
  inr_desc ((tensorRight K).map (inl A B)) ((tensorRight K).map (inr A B))

/-- Left whiskering of a copair is copairing of the whiskered arrows
after passing through the written split. -/
theorem whiskerLeft_desc (K : Interface M policy) {A B C : Interface M policy}
    (f : A ⟶ C) (g : B ⟶ C) :
    (tensorLeft K).map (desc f g) =
      (leftDistributor K A B).inv ≫ desc ((tensorLeft K).map f) ((tensorLeft K).map g) :=
  Quotient.inductionOn₂ f g fun p q => Quotient.sound
    (Program.equiv_of_run_eq (Program.run_whiskerLeft_desc (K := K.ty) p q))

/-- Right whiskering of a copair gives the corresponding right split. -/
theorem whiskerRight_desc (K : Interface M policy) {A B C : Interface M policy}
    (f : A ⟶ C) (g : B ⟶ C) :
    (tensorRight K).map (desc f g) =
      (rightDistributor A B K).inv ≫ desc ((tensorRight K).map f) ((tensorRight K).map g) :=
  Quotient.inductionOn₂ f g fun p q => Quotient.sound
    (Program.equiv_of_run_eq (Program.run_whiskerRight_desc (K := K.ty) p q))

/-- Precomposition with an isomorphism preserves and reflects the hom order. -/
def precompOrderIso {A B : Interface M policy} (i : A ≅ B) (T : Interface M policy) :
    (B ⟶ T) ≃o (A ⟶ T) where
  toFun f := i.hom ≫ f
  invFun f := i.inv ≫ f
  left_inv _ := by simp [← Category.assoc]
  right_inv _ := by simp [← Category.assoc]
  map_rel_iff' := by exact DistributivityProofs.precomp_le_iff i

/-- The order-level universal property for the left-whiskered chosen sum. -/
def leftSumOrderIso (K A B T : Interface M policy) :
    (K.tensor (A.sum B) ⟶ T) ≃o ((K.tensor A ⟶ T) × (K.tensor B ⟶ T)) :=
  (precompOrderIso (leftDistributor K A B) T).trans (sumOrderIso (K.tensor A) (K.tensor B) T)

/-- The order-level universal property for the right-whiskered chosen sum. -/
def rightSumOrderIso (A B K T : Interface M policy) :
    ((A.sum B).tensor K ⟶ T) ≃o ((A.tensor K ⟶ T) × (B.tensor K ⟶ T)) :=
  (precompOrderIso (rightDistributor A B K) T).trans (sumOrderIso (A.tensor K) (B.tensor K) T)

@[simp] theorem leftSumOrderIso_apply (K A B T : Interface M policy) (f : K.tensor (A.sum B) ⟶ T) :
    leftSumOrderIso K A B T f = ((tensorLeft K).map (inl A B) ≫ f, (tensorLeft K).map (inr A B) ≫ f) := by
  change (inl _ _ ≫ (leftDistributor K A B).hom ≫ f, inr _ _ ≫ (leftDistributor K A B).hom ≫ f) = _
  simp only [← Category.assoc, inl_leftDistributor, inr_leftDistributor]
  rfl

@[simp] theorem rightSumOrderIso_apply (A B K T : Interface M policy) (f : (A.sum B).tensor K ⟶ T) :
    rightSumOrderIso A B K T f = ((tensorRight K).map (inl A B) ≫ f, (tensorRight K).map (inr A B) ≫ f) := by
  change (inl _ _ ≫ (rightDistributor A B K).hom ≫ f, inr _ _ ≫ (rightDistributor A B K).hom ≫ f) = _
  simp only [← Category.assoc, inl_rightDistributor, inr_rightDistributor]
  rfl

omit [UnitModel D] [CoproductModel D] in
private theorem leftZeroEmpty (K : Interface M policy) (x : D (K.tensor Interface.zero).ty) : False :=
  (EmptyModel.emptyEquiv ((ProductModel.productEquiv K.ty (empty : τ)) x).2).elim

omit [UnitModel D] [CoproductModel D] in
private theorem rightZeroEmpty (K : Interface M policy) (x : D (Interface.zero.tensor K).ty) : False :=
  (EmptyModel.emptyEquiv ((ProductModel.productEquiv (empty : τ) K.ty) x).1).elim

/-- The left tensor with empty projects to empty. Written abort is its inverse. -/
def leftZeroIso (K : Interface M policy) : K.tensor Interface.zero ≅ Interface.zero where
  hom := ofProgram (Program.snd K.ty empty)
  inv := abort _
  hom_inv_id := by exact DistributivityProofs.empty_domain_eq (leftZeroEmpty K) _ _
  inv_hom_id := by
    exact DistributivityProofs.empty_domain_eq (fun x => (EmptyModel.emptyEquiv (D := D) x).elim) _ _

/-- The right tensor with empty projects to empty. Written abort is its inverse. -/
def rightZeroIso (K : Interface M policy) : Interface.zero.tensor K ≅ Interface.zero where
  hom := ofProgram (Program.fst empty K.ty)
  inv := abort _
  hom_inv_id := by exact DistributivityProofs.empty_domain_eq (rightZeroEmpty K) _ _
  inv_hom_id := by
    exact DistributivityProofs.empty_domain_eq (fun x => (EmptyModel.emptyEquiv (D := D) x).elim) _ _

theorem leftZeroIso_central (K : Interface M policy) :
    PremonoidalCategory.IsCentral (leftZeroIso K).hom ∧ PremonoidalCategory.IsCentral (leftZeroIso K).inv := by
  have h := isCentral_of_pureRun (A := K.tensor Interface.zero) (B := Interface.zero)
    (p := Program.snd K.ty empty) ⟨fun x => (leftZeroEmpty K x).elim, fun x => (leftZeroEmpty K x).elim⟩
  exact ⟨h, h.inv (leftZeroIso K)⟩

theorem rightZeroIso_central (K : Interface M policy) :
    PremonoidalCategory.IsCentral (rightZeroIso K).hom ∧ PremonoidalCategory.IsCentral (rightZeroIso K).inv := by
  have h := isCentral_of_pureRun (A := Interface.zero.tensor K) (B := Interface.zero)
    (p := Program.fst empty K.ty) ⟨fun x => (rightZeroEmpty K x).elim, fun x => (rightZeroEmpty K x).elim⟩
  exact ⟨h, h.inv (rightZeroIso K)⟩

end Arrow

/-- Left whiskering preserves the cocone with the written injections. -/
def leftSumIsColimit (K A B : Interface M policy) :
    IsColimit (BinaryCofan.mk ((tensorLeft K).map (Arrow.inl A B)) ((tensorLeft K).map (Arrow.inr A B))) :=
  (sumIsColimit (K.tensor A) (K.tensor B)).ofIsoColimit (BinaryCofan.ext (Arrow.leftDistributor K A B)
    (by
      change _ = (tensorLeft K).map (Arrow.inl A B) ≫ _
      erw [← Arrow.inl_leftDistributor K A B, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rfl)
    (by
      change _ = (tensorLeft K).map (Arrow.inr A B) ≫ _
      erw [← Arrow.inr_leftDistributor K A B, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rfl))

/-- Right whiskering preserves the cocone with the written injections. -/
def rightSumIsColimit (A B K : Interface M policy) :
    IsColimit (BinaryCofan.mk ((tensorRight K).map (Arrow.inl A B)) ((tensorRight K).map (Arrow.inr A B))) :=
  (sumIsColimit (A.tensor K) (B.tensor K)).ofIsoColimit (BinaryCofan.ext (Arrow.rightDistributor A B K)
    (by
      change _ = (tensorRight K).map (Arrow.inl A B) ≫ _
      erw [← Arrow.inl_rightDistributor A B K, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rfl)
    (by
      change _ = (tensorRight K).map (Arrow.inr A B) ≫ _
      erw [← Arrow.inr_rightDistributor A B K, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rfl))

instance : HasFiniteCoproducts (Interface M policy) := hasFiniteCoproducts_of_has_binary_and_initial

instance (K A B : Interface M policy) : PreservesColimit (pair A B) (tensorLeft K) :=
  preservesColimit_of_preserves_colimit_cocone (sumIsColimit A B)
    ((isColimitMapCoconeBinaryCofanEquiv (tensorLeft K) _ _).symm (leftSumIsColimit K A B))

instance (K A B : Interface M policy) : PreservesColimit (pair A B) (tensorRight K) :=
  preservesColimit_of_preserves_colimit_cocone (sumIsColimit A B)
    ((isColimitMapCoconeBinaryCofanEquiv (tensorRight K) _ _).symm (rightSumIsColimit A B K))

instance (K : Interface M policy) : PreservesColimit (Functor.empty.{0} (Interface M policy)) (tensorLeft K) :=
  preservesColimit_of_preserves_colimit_cocone zeroIsInitial
    ((isColimitMapCoconeEmptyCoconeEquiv (tensorLeft K) _).symm (zeroIsInitial.ofIso (Arrow.leftZeroIso K).symm))

instance (K : Interface M policy) : PreservesColimit (Functor.empty.{0} (Interface M policy)) (tensorRight K) :=
  preservesColimit_of_preserves_colimit_cocone zeroIsInitial
    ((isColimitMapCoconeEmptyCoconeEquiv (tensorRight K) _).symm (zeroIsInitial.ofIso (Arrow.rightZeroIso K).symm))

private theorem preservesFiniteOfPairAndEmpty (F : Interface M policy ⥤ Interface M policy)
    [∀ A B, PreservesColimit (pair A B) F] [PreservesColimit (Functor.empty.{0} (Interface M policy)) F] :
    PreservesFiniteCoproducts F := by
  let _ := preservesBinaryCoproducts_of_isIso_coprodComparison F
  let _ := preservesColimitsOfShape_pempty_of_preservesInitial F
  exact ⟨preservesShape_fin_of_preserves_binary_and_initial F⟩

instance (K : Interface M policy) : PreservesFiniteCoproducts (tensorLeft K) :=
  preservesFiniteOfPairAndEmpty (tensorLeft K)

instance (K : Interface M policy) : PreservesFiniteCoproducts (tensorRight K) :=
  preservesFiniteOfPairAndEmpty (tensorRight K)

/-- Chosen preservation supplies the canonical distributor even for the
opaque coproduct selected by the category interface. -/
instance : DistributiveTensor (Interface M policy) where
  left_isIso K A B := by
    change IsIso (coprodComparison (tensorLeft K) A B)
    infer_instance

/-- The canonical right distributor is invertible independently of braiding. -/
theorem rightDistrib_isIso (A B K : Interface M policy) : IsIso (DistributiveTensor.rightHom A B K) := by
  change IsIso (coprodComparison (tensorRight K) A B)
  infer_instance

end Silmaril.Isotope.LetCase.HandledTrace
