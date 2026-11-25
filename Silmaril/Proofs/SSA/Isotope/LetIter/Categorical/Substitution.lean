module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Substitution.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Purity.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Coherence.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend caseWithContext contextualLoop)

section

variable {τ : Type u} [TypeFormers τ] {ν : Type w} {V : Type u₁} [Category.{v₁} V]
  [CartesianMonoidalCategory V] [HasFiniteCoproducts V] (M : TypeModel τ V)
  {Γ : Ctx ν τ}

local notation "Env" => envObj M Γ
local notation "freePart" => CartesianMonoidalCategory.fst (ctxObj M Γ)

@[reassoc] private theorem boundTuple_lookup {R : V} {n : Nat} (β : BoundCtx τ n)
    (p : ∀ i, R ⟶ M.obj (β.get i)) (i : Fin n) : boundTuple M β p ≫ boundLookup M i = p i := by
  induction β with
  | nil => exact i.elim0
  | snoc β A ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact lift_snd _ _
    · change lift (boundTuple M β (fun i => p i.succ)) (p 0) ≫
        fst _ _ ≫ boundLookup M j = p j.succ
      exact (lift_fst_assoc _ _ _).trans (ih _ _)

@[reassoc] private theorem envSubstMap_bound {n m : Nat} (β : BoundCtx τ n) (δ : BoundCtx τ m)
    (p : ∀ i, Env δ ⟶ M.obj (β.get i)) (i : Fin n) :
    envSubstMap M Γ β δ p ≫ boundVar M (Γ := Γ) i = p i := by
  exact (lift_snd_assoc _ _ _).trans (boundTuple_lookup M β p i)

private def liftEnvMap {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m} (p : Env δ ⟶ Env β) (A : τ) :
    Env (.snoc δ A) ⟶ Env (.snoc β A) :=
  (envSnocIso M Γ δ A).inv ≫ (p ▷ M.obj A) ≫ (envSnocIso M Γ β A).hom

@[reassoc] private theorem snoc_liftEnvMap {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    (p : Env δ ⟶ Env β) (A : τ) :
    (envSnocIso M Γ δ A).hom ≫ liftEnvMap M p A = (p ▷ M.obj A) ≫ (envSnocIso M Γ β A).hom := by
  simp [liftEnvMap]

@[reassoc] private theorem dropSlot_free {n : Nat} (β : BoundCtx τ n) (A : τ) :
    dropSlot M (Γ := Γ) β A ≫ freePart _ = freePart _ := by
  exact (Category.assoc (envSnocIso M Γ β A).inv _ _).trans
    (associator_inv_fst_fst (ctxObj M Γ) (boundObj M β) (M.obj A))

@[reassoc] private theorem dropSlot_bound {n : Nat} (β : BoundCtx τ n) (A : τ) (i : Fin n) :
    dropSlot M (Γ := Γ) β A ≫ boundVar M (Γ := Γ) i =
      boundVar M (Γ := Γ) (β := .snoc β A) i.succ := by
  change ((α_ _ _ _).inv ≫ fst _ _) ≫ snd _ _ ≫ boundLookup M i =
    snd _ _ ≫ (fst _ _ ≫ boundLookup M i)
  rw [Category.assoc, associator_inv_fst_snd_assoc]

@[reassoc] private theorem liftEnvMap_drop {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    (p : Env δ ⟶ Env β) (A : τ) :
    liftEnvMap M p A ≫ dropSlot M β A = dropSlot M δ A ≫ p := by
  simp [liftEnvMap, dropSlot, Category.assoc]

@[reassoc] private theorem liftEnvMap_free {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    {p : Env δ ⟶ Env β} (h : p ≫ freePart _ = freePart _) (A : τ) :
    liftEnvMap M p A ≫ freePart _ = freePart _ := by
  exact (congrArg (fun f => liftEnvMap M p A ≫ f) (dropSlot_free M β A).symm).trans
    ((liftEnvMap_drop_assoc M p A (freePart (boundObj M β))).trans
      ((congrArg (fun f => dropSlot M δ A ≫ f) h).trans (dropSlot_free M δ A)))

@[reassoc] private theorem liftEnvMap_zero {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    (p : Env δ ⟶ Env β) (A : τ) :
    liftEnvMap M p A ≫ boundVar M (Γ := Γ) (β := .snoc β A) 0 =
      boundVar M (Γ := Γ) (β := .snoc δ A) 0 := by
  simp only [liftEnvMap, boundVar, envSnocIso, Category.assoc]
  change (α_ _ _ _).inv ≫ (p ▷ M.obj A) ≫ (α_ _ _ _).hom ≫ snd _ _ ≫ snd _ _ =
    snd _ _ ≫ snd _ _
  rw [associator_hom_snd_snd]
  exact (congrArg (fun f => (α_ (ctxObj M Γ) (boundObj M δ) (M.obj A)).inv ≫ f)
    (whiskerRight_snd p (M.obj A))).trans (associator_inv_snd _ _ _)

@[reassoc] private theorem liftEnvMap_succ {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    (p : Env δ ⟶ Env β) (A : τ) (i : Fin n) :
    liftEnvMap M p A ≫ boundVar M (Γ := Γ) (β := .snoc β A) i.succ =
      dropSlot M δ A ≫ p ≫ boundVar M i := by
  exact (congrArg (fun f => liftEnvMap M p A ≫ f) (dropSlot_bound M β A i).symm).trans
    (liftEnvMap_drop_assoc M p A _)

private theorem envPairHom_expand {n : Nat} (β : BoundCtx τ n) (A B : τ) :
    envPairHom M Γ β A B = (α_ (Env β) (M.obj A) (M.obj B)).inv ≫
      (envSnocIso M Γ β A).hom ▷ M.obj B ≫ (envSnocIso M Γ (.snoc β A) B).hom :=
  MonoidalCategory.pentagon_inv_hom_hom_hom_inv.symm

@[reassoc] private theorem envPair_liftEnvMap {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    (p : Env δ ⟶ Env β) (A B : τ) :
    envPairHom M Γ δ A B ≫ liftEnvMap M (liftEnvMap M p A) B =
      (p ▷ (M.obj A ⊗ M.obj B)) ≫ envPairHom M Γ β A B := by
  rw [envPairHom_expand, envPairHom_expand]
  simp only [liftEnvMap, MonoidalCategory.comp_whiskerRight, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← MonoidalCategory.comp_whiskerRight_assoc, Iso.hom_inv_id,
    MonoidalCategory.id_whiskerRight, Category.id_comp,
    MonoidalCategory.associator_inv_naturality_left_assoc]

end

section

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
local notation "freePart" => CartesianMonoidalCategory.fst (ctxObj M Γ)
local notation "bindContext" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
local notation "pairContext" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair

omit [DecidableEq ν] in
private theorem let_transport {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    (p : Env δ ⟶ Env β) {A B : τ}
    (f : J.obj (Env β) ⟶ J.obj (M.obj A)) (g : J.obj (Env (.snoc β A)) ⟶ J.obj (M.obj B)) :
    bindContext J (J.map p ≫ f)
      (J.map (envSnocIso M Γ δ A).hom ≫ J.map (liftEnvMap M p A) ≫ g) =
    J.map p ≫ bindContext J f (J.map (envSnocIso M Γ β A).hom ≫ g) := by
  rw [← J.map_comp_assoc, snoc_liftEnvMap, J.map_comp_assoc, bind_pre_map]

omit [DecidableEq ν] in
private theorem pairLet_transport {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    (p : Env δ ⟶ Env β) {A B D : τ}
    (f : J.obj (Env β) ⟶ J.obj (M.obj (product A B)))
    (g : J.obj (Env (.snoc (.snoc β A) B)) ⟶ J.obj (M.obj D)) :
    bindContext J (J.map p ≫ f)
      (J.map (Env δ ◁ (M.productIso A B).hom) ≫ J.map (envPairHom M Γ δ A B) ≫
        J.map (liftEnvMap M (liftEnvMap M p A) B) ≫ g) =
    J.map p ≫ bindContext J f
      (J.map (Env β ◁ (M.productIso A B).hom) ≫ J.map (envPairHom M Γ β A B) ≫ g) := by
  have exchange : (Env δ ◁ (M.productIso A B).hom) ≫
      (p ▷ (M.obj A ⊗ M.obj B)) =
      (p ▷ M.obj (product A B)) ≫ (Env β ◁ (M.productIso A B).hom) := by
    exact MonoidalCategory.whisker_exchange _ _
  rw [← J.map_comp_assoc (envPairHom M Γ δ A B), envPair_liftEnvMap,
    J.map_comp_assoc, ← J.map_comp_assoc (Env δ ◁ (M.productIso A B).hom),
    exchange, J.map_comp_assoc, bind_pre_map]

omit [DecidableEq ν] in
private theorem case_transport {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    (p : Env δ ⟶ Env β) {A B D : τ}
    (f : J.obj (Env β) ⟶ J.obj (M.obj (coprod A B)))
    (l : J.obj (Env (.snoc β A)) ⟶ J.obj (M.obj D))
    (r : J.obj (Env (.snoc β B)) ⟶ J.obj (M.obj D)) :
    caseWithContext J (J.map p ≫ f ≫ J.map (M.coprodIso A B).hom)
      (J.map (envSnocIso M Γ δ A).hom ≫ J.map (liftEnvMap M p A) ≫ l)
      (J.map (envSnocIso M Γ δ B).hom ≫ J.map (liftEnvMap M p B) ≫ r) =
    J.map p ≫ caseWithContext J (f ≫ J.map (M.coprodIso A B).hom)
      (J.map (envSnocIso M Γ β A).hom ≫ l) (J.map (envSnocIso M Γ β B).hom ≫ r) := by
  rw [← J.map_comp_assoc (envSnocIso M Γ δ A).hom,
    ← J.map_comp_assoc (envSnocIso M Γ δ B).hom, snoc_liftEnvMap, snoc_liftEnvMap,
    J.map_comp_assoc, J.map_comp_assoc, case_pre_map]

omit [DecidableEq ν] in
private theorem iter_transport {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    (p : Env δ ⟶ Env β) {A B : τ}
    (f : J.obj (Env β) ⟶ J.obj (M.obj A))
    (g : J.obj (Env (.snoc β A)) ⟶ J.obj (M.obj (coprod B A))) :
    bindContext J (J.map p ≫ f) (contextualLoop J
      (J.map (envSnocIso M Γ δ A).hom ≫ J.map (liftEnvMap M p A) ≫ g ≫
        J.map (M.coprodIso B A).hom)) =
    J.map p ≫ bindContext J f (contextualLoop J
      (J.map (envSnocIso M Γ β A).hom ≫ g ≫ J.map (M.coprodIso B A).hom)) := by
  rw [← J.map_comp_assoc,
    snoc_liftEnvMap, J.map_comp_assoc, contextualLoop_pre_map, bind_pre_map]

private theorem free_transport {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    (p : Env δ ⟶ Env β) (hp : p ≫ freePart _ = freePart _) {x : ν} {A : τ}
    (h : Γ.lookup x = some A) :
    denote J M (Derivation.fv (Φ := Φ) (β := δ) h) =
      J.map p ≫ denote J M (Derivation.fv (Φ := Φ) (β := β) h) := by
  simp only [denote, ← J.map_comp, freeLookup]
  exact congrArg J.map ((Category.assoc p _ _).symm.trans
    (congrArg (fun f => f ≫ ctxLookup M x h) hp)).symm

private theorem unit_transport {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    (p : Env δ ⟶ Env β) :
    denote J M (Derivation.unit (Φ := Φ) (Γ := Γ) (β := δ)) =
      J.map p ≫ denote J M (Derivation.unit (Φ := Φ) (Γ := Γ) (β := β)) := by
  simp only [denote, ← J.map_comp, ← Category.assoc]
  congr 2
  exact isTerminalTensorUnit.hom_ext _ _

private theorem denote_cast_result {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n}
    {A B : τ} (h : A = B) (d : Derivation Φ Γ β t A) :
    denote J M (h ▸ d) = denote J M d ≫ J.map (eqToHom (congrArg M.obj h)) := by
  cases h
  simp

omit [DecidableEq ν] [SymmetricCategory V] [DistributiveTensor V] in
private theorem renaming_vars_up {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    (ρ : TypedRenaming β δ) (p : Env δ ⟶ Env β)
    (h : ∀ i, p ≫ boundVar M (Γ := Γ) i =
      boundVar M (Γ := Γ) (ρ.toFun i) ≫ eqToHom (congrArg M.obj (ρ.typed i)))
    (A : τ) : ∀ i,
      liftEnvMap M p A ≫ boundVar M (Γ := Γ) i =
      boundVar M (Γ := Γ) ((TypedRenaming.up ρ A).toFun i) ≫
        eqToHom (congrArg M.obj ((TypedRenaming.up ρ A).typed i)) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (liftEnvMap_zero M p A).trans (Category.comp_id _).symm
  · change liftEnvMap M p A ≫ boundVar M (Γ := Γ) (β := .snoc β A) j.succ =
      boundVar M (Γ := Γ) (β := .snoc δ A) (ρ.toFun j).succ ≫
        eqToHom (congrArg M.obj (ρ.typed j))
    exact (liftEnvMap_succ M p A j).trans
      ((congrArg (fun k => dropSlot M δ A ≫ k) (h j)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ _) (dropSlot_bound M δ A (ρ.toFun j)))))

private theorem denote_rename_along_proof {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) :
    ∀ {m : Nat} {δ : BoundCtx τ m} (ρ : TypedRenaming β δ) (p : Env δ ⟶ Env β),
      (p ≫ freePart _ = freePart _) →
      (∀ i, p ≫ boundVar M (Γ := Γ) i =
        boundVar M (Γ := Γ) (ρ.toFun i) ≫ eqToHom (congrArg M.obj (ρ.typed i))) →
        denote J M (d.rename ρ) = J.map p ≫ denote J M d := by
  induction d with
  | fv h =>
    intro m δ ρ p hp _
    exact free_transport J M p hp h
  | @bv n β i =>
    intro m δ ρ p _ hv
    change denote J M (ρ.typed i ▸ (Derivation.bv (Φ := Φ) (Γ := Γ) (β := δ)
      (ι := ρ.toFun i))) = J.map p ≫ J.map (boundVar M (Γ := Γ) (β := β) i)
    rw [denote_cast_result, denote, ← J.map_comp, ← J.map_comp, hv i]
  | op _ ih =>
    intro m δ ρ p hp hv
    simp [Derivation.rename, Tm.rename, denote, ih ρ p hp hv, Category.assoc]
  | let₁ _ _ ih ih' =>
    intro m δ ρ p hp hv
    simp [Derivation.rename, Tm.rename, denote, ih ρ p hp hv,
      ih' _ _ (liftEnvMap_free M hp _) (renaming_vars_up M ρ p hv _)]
    exact let_transport J M p _ _
  | unit =>
    intro m δ ρ p _ _
    exact unit_transport J M p
  | pair _ _ ih ih' =>
    intro m δ ρ p hp hv
    simp [Derivation.rename, Tm.rename, denote, ih ρ p hp hv, ih' ρ p hp hv, pair_pre_map J,
      Category.assoc]
  | let₂ _ _ ih ih' =>
    intro m δ ρ p hp hv
    simp [Derivation.rename, Tm.rename, denote, ih ρ p hp hv,
      ih' _ _ (liftEnvMap_free M (liftEnvMap_free M hp _) _)
        (renaming_vars_up M _ _ (renaming_vars_up M ρ p hv _) _)]
    exact pairLet_transport J M p _ _
  | inl _ ih | inr _ ih | abort _ ih =>
    intro m δ ρ p hp hv
    simp [Derivation.rename, Tm.rename, denote, ih ρ p hp hv, Category.assoc]
  | case _ _ _ ih il ir =>
    intro m δ ρ p hp hv
    simp [Derivation.rename, Tm.rename, denote, ih ρ p hp hv,
      il _ _ (liftEnvMap_free M hp _) (renaming_vars_up M ρ p hv _),
      ir _ _ (liftEnvMap_free M hp _) (renaming_vars_up M ρ p hv _), Category.assoc]
    exact case_transport J M p _ _ _
  | iter _ _ ih ih' =>
    intro m δ ρ p hp hv
    simp [Derivation.rename, Tm.rename, denote, ih ρ p hp hv,
      ih' _ _ (liftEnvMap_free M hp _) (renaming_vars_up M ρ p hv _)]
    exact iter_transport J M p _ _

theorem denote_lift_proof {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A B : τ}
    (d : Derivation Φ Γ β t A) :
    denote J M (d.lift (B := B)) = J.map (dropSlot M β B) ≫ denote J M d := by
  apply denote_rename_along_proof J M d (TypedRenaming.succ β B) (dropSlot M β B)
    (dropSlot_free M β B)
  intro i
  exact (dropSlot_bound M (Γ := Γ) β B i).trans (Category.comp_id _).symm

private theorem subst_vars_up {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    {σ : Fin n → Tm ν Φ m} (s : DerivSubst (Γ := Γ) β δ σ) (p : Env δ ⟶ Env β)
    (h : ∀ i, denote J M (s i) = J.map (p ≫ boundVar M (Γ := Γ) i)) (A : τ) :
    ∀ i, denote J M (s.up A i) =
      J.map (liftEnvMap M p A ≫ boundVar M (Γ := Γ) i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact congrArg J.map (liftEnvMap_zero M p A).symm
  · change denote J M ((s j).lift (B := A)) =
      J.map (liftEnvMap M p A ≫ boundVar M (Γ := Γ) (β := .snoc β A) j.succ)
    rw [denote_lift_proof, h j, ← J.map_comp, liftEnvMap_succ]

private theorem denote_bsubst_along_proof {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) :
    ∀ {m : Nat} {δ : BoundCtx τ m} {σ : Fin n → Tm ν Φ m}
      (s : DerivSubst (Γ := Γ) β δ σ) (p : Env δ ⟶ Env β),
      (p ≫ freePart _ = freePart _) →
      (∀ i, denote J M (s i) = J.map (p ≫ boundVar M (Γ := Γ) i)) →
        denote J M (d.bsubst s) = J.map p ≫ denote J M d := by
  induction d with
  | fv h =>
    intro m δ σ s p hp _
    exact free_transport J M p hp h
  | @bv n β i =>
    intro m δ σ s p _ hv
    exact (hv i).trans (J.map_comp _ _)
  | op _ ih =>
    intro m δ σ s p hp hv
    simp [Derivation.bsubst, Tm.bsubst, denote, ih s p hp hv, Category.assoc]
  | let₁ _ _ ih ih' =>
    intro m δ σ s p hp hv
    simp [Derivation.bsubst, Tm.bsubst, denote, ih s p hp hv,
      ih' _ _ (liftEnvMap_free M hp _) (subst_vars_up J M s p hv _)]
    exact let_transport J M p _ _
  | unit =>
    intro m δ σ s p _ _
    exact unit_transport J M p
  | pair _ _ ih ih' =>
    intro m δ σ s p hp hv
    simp [Derivation.bsubst, Tm.bsubst, denote, ih s p hp hv, ih' s p hp hv, pair_pre_map J,
      Category.assoc]
  | let₂ _ _ ih ih' =>
    intro m δ σ s p hp hv
    simp [Derivation.bsubst, Tm.bsubst, denote, ih s p hp hv,
      ih' _ _ (liftEnvMap_free M (liftEnvMap_free M hp _) _)
        (subst_vars_up J M _ _ (subst_vars_up J M s p hv _) _)]
    exact pairLet_transport J M p _ _
  | inl _ ih | inr _ ih | abort _ ih =>
    intro m δ σ s p hp hv
    simp [Derivation.bsubst, Tm.bsubst, denote, ih s p hp hv, Category.assoc]
  | case _ _ _ ih il ir =>
    intro m δ σ s p hp hv
    simp [Derivation.bsubst, Tm.bsubst, denote, ih s p hp hv,
      il _ _ (liftEnvMap_free M hp _) (subst_vars_up J M s p hv _),
      ir _ _ (liftEnvMap_free M hp _) (subst_vars_up J M s p hv _)]
    exact case_transport J M p _ _ _
  | iter _ _ ih ih' =>
    intro m δ σ s p hp hv
    simp [Derivation.bsubst, Tm.bsubst, denote, ih s p hp hv,
      ih' _ _ (liftEnvMap_free M hp _) (subst_vars_up J M s p hv _)]
    exact iter_transport J M p _ _

theorem denote_bsubst_proof {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    {t : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β t A)
    {σ : Fin n → Tm ν Φ m} (s : DerivSubst (Γ := Γ) β δ σ)
    (p : ∀ i, Env δ ⟶ M.obj (β.get i)) (hs : ∀ i, denote J M (s i) = J.map (p i)) :
    denote J M (d.bsubst s) = J.map (envSubstMap M Γ β δ p) ≫ denote J M d := by
  apply denote_bsubst_along_proof J M d s (envSubstMap M Γ β δ p)
  · exact lift_fst _ _
  · intro i
    exact (hs i).trans (congrArg J.map (envSubstMap_bound M β δ p i).symm)

theorem denote_instantiate_proof {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ (.snoc β A) b B)
    (f : Env β ⟶ M.obj A) (hf : denote J M da = J.map f) :
    denote J M (db.instantiate da) =
      J.map (lift (𝟙 (Env β)) f ≫ (envSnocIso M Γ β A).hom) ≫ denote J M db := by
  let p := lift (𝟙 (Env β)) f ≫ (envSnocIso M Γ β A).hom
  let s : DerivSubst (Γ := Γ) (.snoc β A) β (Fin.cases a (fun i => .bv i)) :=
    Fin.cases da (fun _ => .bv)
  have drop : p ≫ dropSlot M (Γ := Γ) β A = 𝟙 (Env β) := by
    simp [p, dropSlot, Category.assoc]
  have proj {R : V} (g : Env β ⟶ R) : p ≫ dropSlot M β A ≫ g = g :=
    (Category.assoc p _ g).symm.trans ((congrArg (fun h => h ≫ g) drop).trans (Category.id_comp g))
  apply denote_bsubst_along_proof J M db s p
  · exact (congrArg (fun k => p ≫ k) (dropSlot_free M β A).symm).trans (proj _)
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have h : p ≫ boundVar M (Γ := Γ) (β := .snoc β A) 0 = f := by
        have newest : (envSnocIso M Γ β A).hom ≫
            boundVar M (Γ := Γ) (β := .snoc β A) 0 = snd (Env β) (M.obj A) :=
          associator_hom_snd_snd (ctxObj M Γ) (boundObj M β) (M.obj A)
        exact (Category.assoc (lift (𝟙 (Env β)) f) _ _).trans
          ((congrArg (fun k => lift (𝟙 (Env β)) f ≫ k) newest).trans (lift_snd _ _))
      exact hf.trans (congrArg J.map h.symm)
    · exact congrArg J.map ((congrArg (fun k => p ≫ k)
        (dropSlot_bound M β A j).symm).trans (proj _)).symm

theorem denote_rename_proof {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    {t : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β t A) (ρ : TypedRenaming β δ) :
    denote J M (d.rename ρ) = J.map (envRenameMap M Γ ρ) ≫ denote J M d := by
  apply denote_rename_along_proof J M d ρ (envRenameMap M Γ ρ)
  · exact lift_fst _ _
  · intro i
    exact envSubstMap_bound M β δ _ i

theorem denote_underBinder_proof {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ (n + 1)} {A X Y : τ} (d : Derivation Φ Γ (.snoc β Y) t A) :
    J.map (envSnocIso M Γ (.snoc β X) Y).hom ≫
        denote J M (d.rename (TypedRenaming.underBinder β X Y)) =
      J.map (dropSlot M β X ▷ M.obj Y) ≫
        J.map (envSnocIso M Γ β Y).hom ≫ denote J M d := by
  have h := denote_rename_along_proof J M d (TypedRenaming.underBinder β X Y)
    (liftEnvMap M (dropSlot M β X) Y) (liftEnvMap_free M (dropSlot_free M β X) Y)
    (renaming_vars_up M (TypedRenaming.succ β X) (dropSlot M β X)
      (fun i => (dropSlot_bound M (Γ := Γ) β X i).trans (Category.comp_id _).symm) Y)
  rw [h, ← J.map_comp_assoc, snoc_liftEnvMap, J.map_comp_assoc]

theorem denote_underTwoBinders_proof {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ (n + 2)} {D X A B : τ}
    (d : Derivation Φ Γ (.snoc (.snoc β A) B) t D) :
    J.map (envPairHom M Γ (.snoc β X) A B) ≫
        denote J M (d.rename (TypedRenaming.underTwoBinders β X A B)) =
      J.map (dropSlot M β X ▷ (M.obj A ⊗ M.obj B)) ≫
        J.map (envPairHom M Γ β A B) ≫ denote J M d := by
  let ρ := TypedRenaming.succ β X
  let p := dropSlot M (Γ := Γ) β X
  have hρ : TypedRenaming.underTwoBinders β X A B = TypedRenaming.up (TypedRenaming.up ρ A) B := by
    have h : (TypedRenaming.underTwoBinders β X A B).toFun =
        (TypedRenaming.up (TypedRenaming.up ρ A) B).toFun := by
      funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun _ => rfl) j) i
    have extensional (r s : TypedRenaming (.snoc (.snoc β A) B) (.snoc (.snoc (.snoc β X) A) B))
        (he : r.toFun = s.toFun) : r = s := by
      rcases r with ⟨f, hf⟩
      rcases s with ⟨g, hg⟩
      change f = g at he
      subst g
      rfl
    exact extensional _ _ h
  have hp : ∀ i, p ≫ boundVar M (Γ := Γ) i =
      boundVar M (Γ := Γ) (ρ.toFun i) ≫ eqToHom (congrArg M.obj (ρ.typed i)) :=
    fun i => (dropSlot_bound M (Γ := Γ) β X i).trans (Category.comp_id _).symm
  rw [hρ, denote_rename_along_proof J M d _
    (liftEnvMap M (liftEnvMap M p A) B)
    (liftEnvMap_free M (liftEnvMap_free M (dropSlot_free M β X) A) B)
    (renaming_vars_up M _ _ (renaming_vars_up M ρ p hp A) B),
    ← J.map_comp_assoc, envPair_liftEnvMap, J.map_comp_assoc]

variable {ε : Type*} [HasEff Φ ε] {pe : ε}
variable (pureInstr : ∀ f : Φ, IsPure pe f →
  ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
    InstructionModel.denote (J := J) (M := M) f = J.map p)

include pureInstr

theorem denote_pure_bsubst_proof {n m : Nat} {β : BoundCtx τ n} {δ : BoundCtx τ m}
    {t : Tm ν Φ n} {A : τ} (d : Derivation Φ Γ β t A)
    {σ : Fin n → Tm ν Φ m} (s : DerivSubst (Γ := Γ) β δ σ)
    (hs : ∀ i, Pure pe (σ i)) :
    ∃ p : ∀ i, Env δ ⟶ M.obj (β.get i),
      (∀ i, denote J M (s i) = J.map (p i)) ∧
        denote J M (d.bsubst s) = J.map (envSubstMap M Γ β δ p) ≫ denote J M d := by
  choose p hp using fun i => denote_pure_factor J M pureInstr (s i) (hs i)
  exact ⟨p, hp, denote_bsubst_proof J M d s p hp⟩

theorem denote_let_beta_proof {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (da : Derivation Φ Γ β a A) (db : Derivation Φ Γ (.snoc β A) b B) (p : Pure pe a) :
    denote J M (.let₁ da db) = denote J M (db.instantiate da) := by
  obtain ⟨f, hf⟩ := denote_pure_factor J M pureInstr da p
  rw [denote, hf, ProofRelevant.Semantics.Categorical.bind, extend_map, ← J.map_comp_assoc]
  exact (denote_instantiate_proof J M da db f hf).symm

end

end Silmaril.Isotope.LetIter.Semantics.Categorical
