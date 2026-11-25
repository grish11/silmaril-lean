module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs

/-! # Totality of the structural λSSA denotation graphs -/

@[expose] public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (splitMapCoprod)

section Term

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : Functor V C) [DistributiveFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

theorem denotes_exists_proof {Γ : VCtx τ} {t : Tm Φ} {A : τ}
    (h : Tm.HasType Γ t A) : ∃ f, Denotes J M h f := by
  induction h with
  | var h => exact ⟨_, .var h⟩
  | op ha ih => rcases ih with ⟨fa, hfa⟩; exact ⟨_, .op hfa⟩
  | let₁ ha hb iha ihb =>
      rcases iha with ⟨fa, hfa⟩; rcases ihb with ⟨fb, hfb⟩
      exact ⟨_, .let₁ hfa hfb⟩
  | pair ha hb iha ihb =>
      rcases iha with ⟨fa, hfa⟩; rcases ihb with ⟨fb, hfb⟩
      exact ⟨_, .pair hfa hfb⟩
  | unit => exact ⟨_, .unit⟩
  | let₂ ha hb iha ihb =>
      rcases iha with ⟨fa, hfa⟩; rcases ihb with ⟨fb, hfb⟩
      exact ⟨_, .let₂ hfa hfb⟩
  | inl ha ih => rcases ih with ⟨fa, hfa⟩; exact ⟨_, .inl hfa⟩
  | inr hb ih => rcases ih with ⟨fb, hfb⟩; exact ⟨_, .inr hfb⟩
  | case he hl hr ihe ihl ihr =>
      rcases ihe with ⟨fe, hfe⟩; rcases ihl with ⟨fl, hfl⟩
      rcases ihr with ⟨fr, hfr⟩
      exact ⟨_, .case hfe hfl hfr⟩
  | abort ha ih => rcases ih with ⟨fa, hfa⟩; exact ⟨_, .abort hfa⟩

end Term

section FiniteCollective

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : Functor V C) [DistributiveFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {n : Nat}

structure FiniteCollective (Γ : VCtx τ) {n : Nat} (R : Fin n → τ) (X : V)
    (block : ∀ i, J.obj (ctxObj M Γ ⊗ M.obj (R i)) ⟶ J.obj X)
    (f : J.obj (ctxObj M Γ ⊗ finiteLabelObj M R) ⟶ J.obj X) : Prop where
  restrict (i : Fin n) :
    J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M R i) ≫ f = block i

noncomputable def labelOneTo (R : Fin 1 → τ) :
    finiteLabelObj M R ⟶ M.obj (R 0) :=
  Limits.Sigma.desc fun i => eqToHom (congrArg (fun j => M.obj (R j)) (Fin.eq_zero i))

omit [SymmetricCategory V] [DistributiveTensor V] in
@[reassoc (attr := simp)] theorem labelOneTo_ι (R : Fin 1 → τ) :
    finiteLabelInject M R 0 ≫ labelOneTo M R = 𝟙 _ := by
  unfold finiteLabelInject labelOneTo
  calc
    _ = eqToHom (congrArg (fun j => M.obj (R j)) (Fin.eq_zero (0 : Fin 1))) :=
      Limits.Sigma.ι_comp_desc _ _
    _ = 𝟙 _ := by simp

noncomputable def finiteConsTo (R : Fin (n + 1) → τ) :
    finiteLabelObj M R ⟶ M.obj (R 0) ⨿ finiteLabelObj M (fun i => R i.succ) :=
  Limits.Sigma.desc fun i => Fin.cases coprod.inl
    (fun j => finiteLabelInject M (fun i => R i.succ) j ≫ coprod.inr) i

omit [SymmetricCategory V] [DistributiveTensor V] in
@[reassoc (attr := simp)] theorem finiteConsTo_head (R : Fin (n + 1) → τ) :
    finiteLabelInject M R 0 ≫ finiteConsTo M R = coprod.inl := by
  exact Limits.Sigma.ι_comp_desc _ _

omit [SymmetricCategory V] [DistributiveTensor V] in
@[reassoc (attr := simp)] theorem finiteConsTo_tail (R : Fin (n + 1) → τ)
    (i : Fin n) : finiteLabelInject M R i.succ ≫ finiteConsTo M R =
      finiteLabelInject M (fun j => R j.succ) i ≫ coprod.inr := by
  exact Limits.Sigma.ι_comp_desc _ _

omit [SymmetricCategory V] in
theorem finiteHead_distribute (R : Fin (n + 1) → τ) (Γ : VCtx τ) :
    ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M R 0) ≫
        ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteConsTo M R) ≫
        (DistributiveTensor.leftIso (ctxObj M Γ) (M.obj (R 0))
          (finiteLabelObj M (fun i => R i.succ))).inv = coprod.inl := by
  rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.comp_id, finiteConsTo_head]
  apply (cancel_mono (DistributiveTensor.leftIso (ctxObj M Γ) (M.obj (R 0))
    (finiteLabelObj M (fun i => R i.succ))).hom).1
  simp [DistributiveTensor.leftIso]

omit [SymmetricCategory V] in
theorem finiteTail_distribute (R : Fin (n + 1) → τ) (Γ : VCtx τ) (i : Fin n) :
    ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M R i.succ) ≫
        ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteConsTo M R) ≫
        (DistributiveTensor.leftIso (ctxObj M Γ) (M.obj (R 0))
          (finiteLabelObj M (fun i => R i.succ))).inv =
      ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M (fun j => R j.succ) i) ≫
        coprod.inr := by
  rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.comp_id, finiteConsTo_tail]
  apply (cancel_mono (DistributiveTensor.leftIso (ctxObj M Γ) (M.obj (R 0))
    (finiteLabelObj M (fun i => R i.succ))).hom).1
  simp [DistributiveTensor.leftIso]

omit [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributivePremonoidalCategory C] [DistributiveFreydCategory J] in
@[reassoc] theorem map_finiteHead_distribute (R : Fin (n + 1) → τ) (Γ : VCtx τ) :
    J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M R 0) ≫
        J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteConsTo M R) ≫
        J.map (DistributiveTensor.leftIso (ctxObj M Γ) (M.obj (R 0))
          (finiteLabelObj M (fun i => R i.succ))).inv = J.map coprod.inl := by
  simpa only [Functor.map_comp] using
    congrArg J.map (finiteHead_distribute M R Γ)

omit [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributivePremonoidalCategory C] [DistributiveFreydCategory J] in
@[reassoc] theorem map_finiteTail_distribute (R : Fin (n + 1) → τ) (Γ : VCtx τ)
    (i : Fin n) :
    J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M R i.succ) ≫
        J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteConsTo M R) ≫
        J.map (DistributiveTensor.leftIso (ctxObj M Γ) (M.obj (R 0))
          (finiteLabelObj M (fun i => R i.succ))).inv =
      J.map (((𝟙 (ctxObj M Γ)) ⊗ₘ
        finiteLabelInject M (fun j => R j.succ) i) ≫ coprod.inr) := by
  simpa only [Functor.map_comp] using
    congrArg J.map (finiteTail_distribute M R Γ i)

omit [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [DistributiveFreydCategory J] in
theorem finiteCollective_one (Γ : VCtx τ) (R : Fin 1 → τ) (X : V)
    (block : ∀ i, J.obj (ctxObj M Γ ⊗ M.obj (R i)) ⟶ J.obj X) :
    FiniteCollective J M Γ R X block
      (J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ labelOneTo M R) ≫ block 0) := by
  constructor
  intro i
  obtain rfl := Fin.eq_zero i
  rw [← Category.assoc, ← J.map_comp,
    MonoidalCategory.tensorHom_comp_tensorHom]
  simp

theorem finiteCollective_exists_succ (n : Nat) (Γ : VCtx τ)
    (R : Fin (n + 1) → τ) (X : V)
    (block : ∀ i, J.obj (ctxObj M Γ ⊗ M.obj (R i)) ⟶ J.obj X) :
    ∃ f, FiniteCollective J M Γ R X block f := by
  induction n with
  | zero => exact ⟨_, finiteCollective_one J M Γ R X block⟩
  | succ n ih =>
      let Rt : Fin (n + 1) → τ := fun i => R i.succ
      rcases ih Rt (fun i => block i.succ) with ⟨ft, dft⟩
      let f := J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteConsTo M R) ≫
        J.map (DistributiveTensor.leftIso (ctxObj M Γ)
          (M.obj (R 0)) (finiteLabelObj M Rt)).inv ≫
        splitMapCoprod J _ _ ≫ coprod.desc (block 0) ft
      refine ⟨f, ?_⟩
      constructor
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [f, Rt]
        rw [map_finiteHead_distribute_assoc]
        simp only [splitMapCoprod]
        rw [map_inl_inv_coprodComparison_assoc]
        rw [coprod.inl_desc]
      · simp only [f, Rt]
        rw [map_finiteTail_distribute_assoc]
        simp only [splitMapCoprod]
        rw [Functor.map_comp, Category.assoc,
          map_inr_inv_coprodComparison_assoc, coprod.inr_desc]
        simpa [Rt] using dft.restrict j

private noncomputable def finiteConsTailFrom (R : Fin (n + 1) → τ) :
    finiteLabelObj M (fun i => R i.succ) ⟶ finiteLabelObj M R :=
  Limits.Sigma.desc (fun i => finiteLabelInject M R i.succ)

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem finiteConsTailFrom_ι (R : Fin (n + 1) → τ) (i : Fin n) :
    finiteLabelInject M (fun i => R i.succ) i ≫ finiteConsTailFrom M R =
      finiteLabelInject M R i.succ :=
  Limits.Sigma.ι_comp_desc _ _

private noncomputable def finiteConsFrom (R : Fin (n + 1) → τ) :
    M.obj (R 0) ⨿ finiteLabelObj M (fun i => R i.succ) ⟶ finiteLabelObj M R :=
  coprod.desc (finiteLabelInject M R 0) (finiteConsTailFrom M R)

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem finiteConsTo_isIso (R : Fin (n + 1) → τ) :
    IsIso (finiteConsTo M R) := by
  refine ⟨⟨finiteConsFrom M R, ?_, ?_⟩⟩
  · apply Limits.Sigma.hom_ext
    intro i
    change finiteLabelInject M R i ≫ _ = finiteLabelInject M R i ≫ _
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [← Category.assoc, finiteConsTo_head, finiteConsFrom, coprod.inl_desc,
        Category.comp_id]
    · rw [← Category.assoc, finiteConsTo_tail, Category.assoc, finiteConsFrom,
        coprod.inr_desc, finiteConsTailFrom_ι, Category.comp_id]
  · apply coprod.hom_ext
    · rw [← Category.assoc, finiteConsFrom, coprod.inl_desc, finiteConsTo_head,
        Category.comp_id]
    · rw [← Category.assoc, finiteConsFrom, coprod.inr_desc, Category.comp_id]
      apply Limits.Sigma.hom_ext
      intro i
      change finiteLabelInject M (fun j => R j.succ) i ≫ _ =
        finiteLabelInject M (fun j => R j.succ) i ≫ _
      rw [← Category.assoc, finiteConsTailFrom_ι, finiteConsTo_tail]

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem finiteLabelInject_one_isIso (R : Fin 1 → τ) :
    IsIso (finiteLabelInject M R 0) := by
  refine ⟨⟨labelOneTo M R, labelOneTo_ι M R, ?_⟩⟩
  apply Limits.Sigma.hom_ext
  intro i
  obtain rfl := Fin.eq_zero i
  change finiteLabelInject M R 0 ≫ _ = finiteLabelInject M R 0 ≫ _
  rw [← Category.assoc, labelOneTo_ι, Category.id_comp, Category.comp_id]

/-- The contextual injections of a nonempty family jointly determine an arrow. -/
theorem collective_ext_proof (n : Nat) (Γ : VCtx τ) (R : Fin (n + 1) → τ)
    {Y : C} {f g : J.obj (ctxObj M Γ ⊗ finiteLabelObj M R) ⟶ Y}
    (h : ∀ i, J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M R i) ≫ f =
      J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M R i) ≫ g) :
    f = g := by
  induction n with
  | zero =>
      let := finiteLabelInject_one_isIso M R
      exact (cancel_epi _).mp (h 0)
  | succ n ih =>
      let Γobj := ctxObj M Γ
      let Rt : Fin (n + 1) → τ := fun i => R i.succ
      let transport : J.obj (Γobj ⊗ finiteLabelObj M R) ⟶
          J.obj (Γobj ⊗ M.obj (R 0)) ⨿ J.obj (Γobj ⊗ finiteLabelObj M Rt) :=
        J.map ((𝟙 Γobj) ⊗ₘ finiteConsTo M R) ≫
          J.map (DistributiveTensor.leftIso Γobj (M.obj (R 0))
            (finiteLabelObj M Rt)).inv ≫
          splitMapCoprod J _ _
      have : IsIso transport := by
        let := finiteConsTo_isIso M R
        dsimp only [transport, splitMapCoprod]
        infer_instance
      apply (cancel_epi (inv transport)).mp
      apply coprod.hom_ext
      · have head : J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M R 0) ≫
            transport = coprod.inl := by
          simp only [transport, Γobj, Rt, map_finiteHead_distribute_assoc,
            splitMapCoprod, map_inl_inv_coprodComparison]
        have headInv : coprod.inl ≫ inv transport =
            J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M R 0) := by
          rw [← head, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
        simp only [← Category.assoc, headInv]
        exact h 0
      · rw [← Category.assoc, ← Category.assoc]
        apply ih Rt
        intro i
        have tail : J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M R i.succ) ≫
            transport = J.map ((𝟙 Γobj) ⊗ₘ finiteLabelInject M Rt i) ≫ coprod.inr := by
          simp only [transport, Γobj, Rt, map_finiteTail_distribute_assoc, splitMapCoprod,
            Functor.map_comp, Category.assoc, map_inr_inv_coprodComparison]
        have tailInv : (J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M Rt i) ≫
            coprod.inr) ≫ inv transport =
            J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ finiteLabelInject M R i.succ) := by
          rw [← tail, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
        simp only [← Category.assoc]
        erw [tailInv]
        exact h i.succ

end FiniteCollective

section Region

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

theorem collectiveDenotes_exists_succ_proof (n : Nat) (Γ : VCtx τ)
    (R : Fin (n + 1) → τ) (L : LCtx τ)
    (block : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶
      J.obj (labelObj M (List.ofFn R ++ L))) :
    ∃ f, CollectiveDenotes J M Γ R L block f := by
  obtain ⟨f, hf⟩ := finiteCollective_exists_succ J M n Γ R _ block
  exact ⟨f, ⟨hf.restrict⟩⟩

theorem regionDenotes_exists_proof
    {Γ : VCtx τ} {r : Region Φ} {L : LCtx τ}
    (h : Region.HasType Γ r L) : ∃ f, RegionDenotes J M h f := by
  induction h with
  | br h ha => exact ⟨_, .br (h := h) (denotes_exists_proof J M ha).choose_spec⟩
  | case he hl hr ihl ihr =>
      rcases ihl with ⟨fl, dl⟩
      rcases ihr with ⟨fr, dr⟩
      exact ⟨_, .case (denotes_exists_proof J M he).choose_spec dl dr⟩
  | let₁ ha hb ih =>
      rcases ih with ⟨fb, db⟩
      exact ⟨_, .let₁ (denotes_exists_proof J M ha).choose_spec db⟩
  | let₂ ha hb ih =>
      rcases ih with ⟨fb, db⟩
      exact ⟨_, .let₂ (denotes_exists_proof J M ha).choose_spec db⟩
  | @cfg _ _ _ n _ R he hb ihe ihb =>
      cases n with
      | zero =>
          rcases ihe with ⟨fe, de⟩
          exact ⟨fe, .cfgZero he hb de⟩
      | succ n =>
          rcases ihe with ⟨fe, de⟩
          choose fb db using ihb
          rcases collectiveDenotes_exists_succ_proof J M n _ R _ fb with ⟨fc, dc⟩
          exact ⟨_, .cfg he hb de db dc⟩

end Region

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
