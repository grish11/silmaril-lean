module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Substitution.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (duplicate caseWithContext extend)

universe u v w u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

local notation "Env" => envObj M Γ
local notation "pairArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair
local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
local notation "tensorIso" => Functor.StrongPremonoidal.tensorIso (J := J)

omit [DecidableEq ν] [SymmetricCategory V] [DistributiveTensor V] in
private theorem envPairHom_associator {n : Nat} (β : BoundCtx τ n) (A B : τ) :
    envPairHom M Γ β A B = (α_ (Env β) (M.obj A) (M.obj B)).inv ≫
      (envSnocIso M Γ β A).hom ▷ M.obj B ≫ (envSnocIso M Γ (.snoc β A) B).hom :=
  MonoidalCategory.pentagon_inv_hom_hom_hom_inv.symm

theorem denote_bind_let_of_diagonal_proof {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b c : Tm ν Φ (n + 1)} {A B D : τ}
    (central : IsCentral
      (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ (.snoc β A) b B)
    (dc : Derivation Φ Γ (.snoc β B) c D) :
    denote J M (.let₁ (.let₁ da db) dc) =
      denote J M (.let₁ da (.let₁ db
        (dc.rename (TypedRenaming.underBinder β A B)))) := by
  rw [denote, denote, denote, denote, denote_underBinder]
  refine bind_assoc_reindex J central _ _ _ _ ?_ _
  simp [dropSlot]

theorem denote_bind_let_case_of_diagonal_proof {n : Nat} {β : BoundCtx τ n}
    {e : Tm ν Φ n} {l r c : Tm ν Φ (n + 1)} {A B D F : τ}
    (central : IsCentral
      (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (de : Derivation Φ Γ β e (coprod A B))
    (dl : Derivation Φ Γ (.snoc β A) l D) (dr : Derivation Φ Γ (.snoc β B) r D)
    (dc : Derivation Φ Γ (.snoc β D) c F) :
    denote J M (.let₁ (.case de dl dr) dc) =
      denote J M (.case de
        (.let₁ dl (dc.rename (TypedRenaming.underBinder β A D)))
        (.let₁ dr (dc.rename (TypedRenaming.underBinder β B D)))) := by
  let f := denote J M de ≫ J.map (M.coprodIso A B).hom
  let k := J.map (envSnocIso M Γ β D).hom ≫ denote J M dc
  have branch {X : τ} {t : Tm ν Φ (n + 1)} (dx : Derivation Φ Γ (.snoc β X) t D) :
      J.map (envSnocIso M Γ β X).hom ≫
        denote J M (.let₁ dx (dc.rename (TypedRenaming.underBinder β X D))) =
      bindArrow J (J.map (envSnocIso M Γ β X).hom ≫ denote J M dx)
        (J.map (fst (Env β) (M.obj X) ▷ M.obj D) ≫ k) := by
    rw [denote, denote_underBinder]
    change J.map (envSnocIso M Γ β X).hom ≫
      bindArrow J (denote J M dx) (J.map (dropSlot M β X ▷ M.obj D) ≫ k) = _
    rw [← bind_pre_map, ← J.map_comp_assoc, ← MonoidalCategory.comp_whiskerRight]
    have h : (envSnocIso M Γ β X).hom ≫ dropSlot M β X = fst (Env β) (M.obj X) := by
      simp [dropSlot]
    rw [h]
  change bindArrow J (caseWithContext J f
      (J.map (envSnocIso M Γ β A).hom ≫ denote J M dl)
      (J.map (envSnocIso M Γ β B).hom ≫ denote J M dr)) k =
    caseWithContext J f
      (J.map (envSnocIso M Γ β A).hom ≫
        denote J M (.let₁ dl (dc.rename (TypedRenaming.underBinder β A D))))
      (J.map (envSnocIso M Γ β B).hom ≫
        denote J M (.let₁ dr (dc.rename (TypedRenaming.underBinder β B D))))
  rw [bind_case_capture J central, branch dl, branch dr]

theorem denote_bind_let_pair_of_diagonal_proof {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 2)} {c : Tm ν Φ (n + 1)} {A B D F : τ}
    (central : IsCentral
      (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (da : Derivation Φ Γ β a (product A B))
    (db : Derivation Φ Γ (.snoc (.snoc β A) B) b D)
    (dc : Derivation Φ Γ (.snoc β D) c F) :
    denote J M (.let₁ (.let₂ da db) dc) =
      denote J M (.let₂ da (.let₁ db
        ((dc.rename (TypedRenaming.underBinder β A D)).rename
          (TypedRenaming.underBinder (.snoc β A) B D)))) := by
  let p := (𝟙 (Env β) ⊗ₘ (M.productIso A B).hom) ≫ envPairHom M Γ β A B
  let q := dropSlot M (Γ := Γ) (.snoc β A) B ≫ dropSlot M β A
  let k := J.map (envSnocIso M Γ β D).hom ≫ denote J M dc
  let dc' := dc.rename (TypedRenaming.underBinder β A D)
  let dc'' := dc'.rename (TypedRenaming.underBinder (.snoc β A) B D)
  have project : p ≫ q = fst (Env β) (M.obj (product A B)) := by
    simp only [p, q, envPairHom_associator, dropSlot, Category.assoc, Iso.hom_inv_id_assoc,
      whiskerRight_fst_assoc, associator_inv_fst_fst, MonoidalCategory.id_tensorHom, whiskerLeft_fst]
  have lifted :
      J.map (envSnocIso M Γ (.snoc (.snoc β A) B) D).hom ≫ denote J M dc'' =
        J.map (q ▷ M.obj D) ≫ k := by
    rw [denote_underBinder, denote_underBinder, ← J.map_comp_assoc, ← MonoidalCategory.comp_whiskerRight]
  change bindArrow J (bindArrow J (denote J M da)
      (J.map (𝟙 (Env β) ⊗ₘ (M.productIso A B).hom) ≫ J.map (envPairHom M Γ β A B) ≫ denote J M db)) k =
    bindArrow J (denote J M da)
      (J.map (𝟙 (Env β) ⊗ₘ (M.productIso A B).hom) ≫ J.map (envPairHom M Γ β A B) ≫
        denote J M (.let₁ db dc''))
  rw [← J.map_comp_assoc, ← J.map_comp_assoc, bind_assoc_reindex J central _ p _ q project, denote, lifted]

private theorem bind_pair_associator {R A B D : V}
    (central : IsCentral
      (J.map (duplicate R) ≫ (tensorIso R R).inv))
    (centralExtended : IsCentral
      (J.map (duplicate (R ⊗ A)) ≫ (tensorIso (R ⊗ A) (R ⊗ A)).inv))
    (f : J.obj R ⟶ J.obj A) (g : J.obj R ⟶ J.obj B)
    (k : J.obj (R ⊗ (A ⊗ B)) ⟶ J.obj D) :
    bindArrow J (pairArrow J f g) k = bindArrow J f
      (bindArrow J (J.map (fst R A) ≫ g) (J.map (α_ R A B).hom ≫ k)) := by
  let u := lift (fst (R ⊗ A) B ≫ snd R A) (snd (R ⊗ A) B)
  change bindArrow J (bindArrow J f (bindArrow J (J.map (fst R A) ≫ g) (J.map u))) k = _
  rw [bind_assoc_capture J central, bind_assoc_capture J centralExtended]
  have h : lift (𝟙 ((R ⊗ A) ⊗ B)) u ≫
      (fst (R ⊗ A) B ▷ (A ⊗ B)) ≫ (fst R A ▷ (A ⊗ B)) = (α_ R A B).hom := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [Category.assoc]
    · apply CartesianMonoidalCategory.hom_ext <;> simp [u, Category.assoc]
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, extend_map]
  rw [← J.map_comp_assoc (lift (𝟙 ((R ⊗ A) ⊗ B)) u),
    ← J.map_comp_assoc (lift (𝟙 ((R ⊗ A) ⊗ B)) u ≫ fst (R ⊗ A) B ▷ (A ⊗ B)),
    Category.assoc (lift (𝟙 ((R ⊗ A) ⊗ B)) u), h]

theorem denote_pair_beta_of_diagonals_proof {n : Nat} {β : BoundCtx τ n}
    {a b : Tm ν Φ n} {c : Tm ν Φ (n + 2)} {A B D : τ}
    (central : IsCentral
      (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (centralExtended : IsCentral
      (J.map (duplicate (Env β ⊗ M.obj A)) ≫
        (tensorIso (Env β ⊗ M.obj A) (Env β ⊗ M.obj A)).inv))
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ β b B)
    (dc : Derivation Φ Γ (.snoc (.snoc β A) B) c D) :
    denote J M (.let₂ (.pair da db) dc) =
      denote J M (.let₁ da (.let₁ (db.lift (B := A)) dc)) := by
  let R := Env β
  let p := (M.productIso A B).hom
  let q := (M.productIso A B).inv
  let f := denote J M da
  let g := denote J M db
  let s := (envSnocIso M Γ β A).hom
  let t := (envSnocIso M Γ (.snoc β A) B).hom
  let k := J.map (envPairHom M Γ β A B) ≫ denote J M dc
  change extend J (pairArrow J f g ≫ J.map q) ≫ J.map (𝟙 R ⊗ₘ p) ≫ k =
    bindArrow J f (J.map s ≫ bindArrow J (denote J M (db.lift (B := A)))
      (J.map t ≫ denote J M dc))
  rw [extend_postmap, Category.assoc, ← J.map_comp_assoc, MonoidalCategory.id_tensorHom R p,
    ← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id, MonoidalCategory.whiskerLeft_id,
    J.map_id, Category.id_comp]
  change bindArrow J (pairArrow J f g) k = _
  rw [bind_pair_associator J central centralExtended, denote_lift, ← bind_pre_map,
    ← J.map_comp_assoc s (dropSlot M β A)]
  have drop : s ≫ dropSlot M β A = fst R (M.obj A) := by simp [s, dropSlot, R]
  have comparison : (α_ R (M.obj A) (M.obj B)).hom ≫ envPairHom M Γ β A B =
      (s ▷ M.obj B) ≫ t := by
    rw [envPairHom_associator, Iso.hom_inv_id_assoc]
  rw [drop]
  dsimp only [k]
  rw [← J.map_comp_assoc, comparison, J.map_comp_assoc]

end Silmaril.Isotope.LetIter.Semantics.Categorical
