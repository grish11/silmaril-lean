module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag.Pruning
import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.CfgReadback.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.UnusedSummand.Trim.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms

/-! # Remove a known left tag after evaluating its payload -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.KnownTag

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd)
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel case_pre_map case_inl_context extend_map extend_postmap)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext extend)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite (SubstDenotes regionDenotes_subst case_inr)

local notation "bindRegion" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
local notation "pairMap" => CartesianMonoidalCategory.lift

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C)

variable [DistributiveFreydCategory J] in
private theorem bind_tag_case {E A B P X T : V} (unpack : P ≅ A ⨿ B)
    (inj : T ⟶ A ⨿ B) (value : J.obj E ⟶ J.obj T)
    (left : J.obj ((E ⊗ P) ⊗ A) ⟶ J.obj X)
    (right : J.obj ((E ⊗ P) ⊗ B) ⟶ J.obj X)
    (selected : J.obj ((E ⊗ P) ⊗ T) ⟶ J.obj X)
    (beta : ∀ k : E ⊗ T ⟶ E ⊗ P,
      caseWithContext J (J.map (snd E T) ≫ J.map inj)
        (J.map (k ▷ A) ≫ left) (J.map (k ▷ B) ≫ right) =
      bindRegion J (J.map (snd E T)) (J.map (k ▷ T) ≫ selected)) :
    let tagged : T ⟶ P := inj ≫ unpack.inv
    let input := E ◁ tagged
    bindRegion J (value ≫ J.map tagged)
      (caseWithContext J (J.map (snd E P ≫ unpack.hom)) left right) =
    bindRegion J value (J.map (pairMap input (snd E T)) ≫ selected) := by
  dsimp only
  let tagged : T ⟶ P := inj ≫ unpack.inv
  let input := E ◁ tagged
  have test : input ≫ snd E P ≫ unpack.hom = snd E T ≫ inj := by
    simp only [input, CartesianMonoidalCategory.whiskerLeft_snd_assoc, tagged, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have branchInput :
      pairMap (𝟙 (E ⊗ T)) (snd E T) ≫ (input ▷ T) = pairMap input (snd E T) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  change extend J (value ≫ J.map tagged) ≫
      caseWithContext J (J.map (snd E P ≫ unpack.hom)) left right =
    extend J value ≫ J.map (pairMap input (snd E T)) ≫ selected
  rw [extend_postmap, Category.assoc, ← case_pre_map, ← J.map_comp, test, J.map_comp,
    beta]
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, extend_map,
    ← J.map_comp_assoc]
  change extend J value ≫ J.map (pairMap (𝟙 (E ⊗ T)) (snd E T) ≫ (input ▷ T)) ≫ selected =
    extend J value ≫ J.map (pairMap input (snd E T)) ≫ selected
  rw [branchInput]

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
  {κ : Type u} (M : TypeModel (Ty κ) V) {Φ : Type v} [HasTy Φ (Ty κ)] [InstructionModel J M Φ]

private theorem supplyTag_after_shift (b : Region Φ) :
    (b.renameVars (Silmaril.DeBruijn.lift Nat.succ)).substVars (Tm.restoreTag .inl) = b := by
  rw [Region.substVars_renameVars]
  have vars : (Tm.restoreTag .inl) ∘ Silmaril.DeBruijn.lift Nat.succ = (Tm.var : Nat → Tm Φ) := by
    funext i
    cases i <;> rfl
  rw [vars, Region.substVars_var]

set_option backward.isDefEq.respectTransparency false in
private theorem restoreTag_denotes (tag : CaseTag) {Γ : VCtx (Ty κ)} {T S : Ty κ}
    (tagged : M.obj T ⟶ M.obj S)
    {ht : (tag.inject (.var 0 : Tm Φ)).HasType (T :: Γ) S}
    (dt : Denotes J M ht (J.map (snd (ctxObj M Γ) (M.obj T) ≫ tagged))) :
    let E := ctxObj M Γ
    SubstDenotes J M (Φ := Φ) (Γ := T :: S :: Γ) (Δ := T :: Γ)
      (Tm.restoreTag tag) (pairMap (E ◁ tagged) (snd E (M.obj T))) := by
  intro E i D hit
  cases i with
  | zero =>
      cases Option.some.inj hit
      refine ⟨.var rfl, ?_⟩
      simp only [lookup, CartesianMonoidalCategory.lift_snd]
      exact .var (i := 0) rfl
  | succ i =>
      cases i with
      | zero =>
          cases Option.some.inj hit
          simp only [lookup, CartesianMonoidalCategory.lift_fst_assoc]
          change ∃ h : (tag.inject (.var 0 : Tm Φ)).HasType (T :: Γ) S,
            Denotes J M h (J.map ((E ◁ tagged) ≫ snd E (M.obj S)))
          rw [CartesianMonoidalCategory.whiskerLeft_snd]
          exact ⟨ht, dt⟩
      | succ i =>
          simp only [lookup, CartesianMonoidalCategory.lift_fst_assoc]
          change ∃ h : Tm.HasType (T :: Γ) (.var (i + 1)) D,
            Denotes J M h (J.map ((E ◁ tagged) ≫ fst E (M.obj S) ≫ lookup M i hit))
          rw [CartesianMonoidalCategory.whiskerLeft_fst_assoc]
          exact ⟨_, by simpa only [lookup] using
            (Denotes.var (J := J) (M := M) (Φ := Φ) (Γ := T :: Γ) (i := i + 1) hit)⟩

set_option backward.isDefEq.respectTransparency false in
theorem let_inl_case_subst {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)} {a : Tm Φ} {A : Ty κ}
    (determined : TypeDetermined Γ a A) {left right : Region Φ}
    {h : Region.HasType Γ (.let₁ (.inl a)
      (.case (.var 0) (left) right)) L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} (d : RegionDenotes J M h f) :
    ∃ (ha : a.HasType Γ A) (hb : (left.substVars (Tm.restoreTag .inl)).HasType (A :: Γ) L),
      RegionDenotes J M (.let₁ ha hb) f := by
  cases d with
  | let₁ dv body =>
      cases dv with
      | inl payload =>
          rename_i D B _ ha _ _
          have fixed := determined D ha
          subst D
          cases body with
          | case test yes no =>
              cases test with
              | var hit =>
                  obtain ⟨rfl, rfl⟩ := Ty.coprod.inj (Option.some.inj hit)
                  let tagged : M.obj A ⟶ M.obj (Silmaril.coprod A B) :=
                    coprod.inl ≫ (M.coprodIso A B).inv
                  have dt : Denotes J M (Tm.HasType.inl (B := B)
                      (Tm.HasType.var (Γ := A :: Γ) (Φ := Φ) (i := 0) rfl))
                      (J.map (snd (ctxObj M Γ) (M.obj A) ≫ tagged)) := by
                    rw [J.map_comp]
                    exact .inl (.var rfl)
                  obtain ⟨hb, selected⟩ := regionDenotes_subst J M yes
                    (restoreTag_denotes J M .inl tagged dt)
                  refine ⟨ha, hb, ?_⟩
                  simp only [lookup, ← J.map_comp]
                  rw [bind_tag_case J (M.coprodIso A B) coprod.inl _ _ _ _
                    (fun _ => case_inl_context J _ _ _)]
                  exact .let₁ payload selected

set_option backward.isDefEq.respectTransparency false in
theorem let_inr_case_subst {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)} {a : Tm Φ} {A : Ty κ}
    (determined : TypeDetermined Γ a A) {left right : Region Φ}
    {h : Region.HasType Γ (.let₁ (.inr a)
      (.case (.var 0) (left) right)) L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} (d : RegionDenotes J M h f) :
    ∃ (ha : a.HasType Γ A) (hb : (right.substVars (Tm.restoreTag .inr)).HasType (A :: Γ) L),
      RegionDenotes J M (.let₁ ha hb) f := by
  cases d with
  | let₁ dv body =>
      cases dv with
      | inr payload =>
          rename_i D B _ ha _ _
          have fixed := determined D ha
          subst D
          cases body with
          | case test yes no =>
              cases test with
              | var hit =>
                  obtain ⟨rfl, rfl⟩ := Ty.coprod.inj (Option.some.inj hit)
                  let tagged : M.obj A ⟶ M.obj (Silmaril.coprod B A) :=
                    coprod.inr ≫ (M.coprodIso B A).inv
                  have dt : Denotes J M (Tm.HasType.inr (A := B)
                      (Tm.HasType.var (Γ := A :: Γ) (Φ := Φ) (i := 0) rfl))
                      (J.map (snd (ctxObj M Γ) (M.obj A) ≫ tagged)) := by
                    rw [J.map_comp]
                    exact .inr (.var rfl)
                  obtain ⟨hb, selected⟩ := regionDenotes_subst J M no
                    (restoreTag_denotes J M .inr tagged dt)
                  refine ⟨ha, hb, ?_⟩
                  simp only [lookup, ← J.map_comp]
                  rw [bind_tag_case J (M.coprodIso B A) coprod.inr _ _ _ _
                    (fun _ => case_inr J _ _ _)]
                  exact .let₁ payload selected

theorem let_inl_case {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)} {a : Tm Φ} {A : Ty κ}
    (determined : TypeDetermined Γ a A) {left right : Region Φ}
    {h : Region.HasType Γ (.let₁ (.inl a)
      (.case (.var 0) (left.renameVars (Silmaril.DeBruijn.lift Nat.succ)) right)) L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} (d : RegionDenotes J M h f) :
    ∃ (ha : a.HasType Γ A) (hb : left.HasType (A :: Γ) L),
      RegionDenotes J M (.let₁ ha hb) f := by
  have moved := let_inl_case_subst J M determined d
  rw [supplyTag_after_shift] at moved
  exact moved

theorem let_case_prune {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)} {a : Tm Φ} {A : Ty κ}
    (tag : CaseTag) (determined : TypeDetermined Γ a A) {left right live : Region Φ}
    (steps : Region.PruneConstructorTests ((tag.select left right).substVars (Tm.restoreTag tag)) live)
    {h : Region.HasType Γ (.let₁ (tag.inject a) (.case (.var 0) left right)) L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} (d : RegionDenotes J M h f) :
    ∃ ht : Region.HasType Γ (.let₁ a live) L, RegionDenotes J M ht f := by
  have moved : ∃ (ha : a.HasType Γ A)
      (hb : ((tag.select left right).substVars (Tm.restoreTag tag)).HasType (A :: Γ) L),
      RegionDenotes J M (.let₁ ha hb) f := by
    cases tag with
    | inl => exact let_inl_case_subst J M determined d
    | inr => exact let_inr_case_subst J M determined d
  obtain ⟨_, _, moved⟩ := moved
  exact prune_denotes J M (.let₁ steps) moved

theorem cfg_entry_prune {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)} {a : Tm Φ} {A : Ty κ}
    (tag : CaseTag) (determined : TypeDetermined Γ a A) {left right live : Region Φ}
    (steps : Region.PruneConstructorTests ((tag.select left right).substVars (Tm.restoreTag tag)) live)
    {n : Nat} {blocks : Fin (n + 1) → Region Φ}
    {h : Region.HasType Γ (.cfg (.let₁ (tag.inject a) (.case (.var 0) left right)) (n + 1) blocks) L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} (d : RegionDenotes J M h f) :
    ∃ ht : Region.HasType Γ (.cfg (.let₁ a live) (n + 1) blocks) L, RegionDenotes J M ht f := by
  obtain ⟨S, _, hb, _, _, _, de, db, dc, rfl⟩ := d.cfg_readback J M
  obtain ⟨he, de'⟩ := let_case_prune J M tag determined steps de
  exact ⟨.cfg S he hb, RegionDenotes.cfg he hb de' db dc⟩

theorem cfg_prune_agree {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)} {a : Tm Φ} {A : Ty κ}
    {left right live : Region Φ} {n : Nat} {P : Fin (n + 1) → Ty κ}
    {blocks : Fin (n + 1) → Region Φ} {renderTag : Bool}
    (p : UnusedSummand.Program (Φ := Φ) P L Γ) (roll : IterationRolling C) (tag : CaseTag)
    (determined : TypeDetermined Γ a A)
    (steps : Region.PruneConstructorTests ((tag.select left right).substVars (Tm.restoreTag tag)) live)
    (shape : p.region renderTag = .cfg (.let₁ a live) (n + 1) blocks)
    {h : Region.HasType Γ (.cfg (.let₁ (tag.inject a) (.case (.var 0) left right)) (n + 1) blocks) L}
    {f g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M h f) (e : RegionDenotes J M h g) : f = g := by
  have moved {x} (w : RegionDenotes J M h x) :
      ∃ t : (p.region renderTag).HasType Γ L, RegionDenotes J M t x := by
    rw [shape]
    exact cfg_entry_prune J M tag determined steps w
  obtain ⟨_, d'⟩ := moved d
  obtain ⟨_, e'⟩ := moved e
  exact p.denotes_eq_trimmed J M roll d' e'

theorem cfg_entry {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)} {a : Tm Φ} {A : Ty κ}
    (determined : TypeDetermined Γ a A) {left right : Region Φ}
    {n : Nat} {blocks : Fin (n + 1) → Region Φ}
    {h : Region.HasType Γ (.cfg (.let₁ (.inl a)
      (.case (.var 0) (left.renameVars (Silmaril.DeBruijn.lift Nat.succ)) right)) (n + 1) blocks) L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} (d : RegionDenotes J M h f) :
    ∃ ht : Region.HasType Γ (.cfg (.let₁ a left) (n + 1) blocks) L, RegionDenotes J M ht f := by
  obtain ⟨S, _, hb, entry, rows, joint, de, db, dc, rfl⟩ := d.cfg_readback J M
  obtain ⟨ha, hl, de'⟩ := let_inl_case J M determined de
  exact ⟨.cfg S (.let₁ ha hl) hb, RegionDenotes.cfg (.let₁ ha hl) hb de' db dc⟩

theorem cfg_agree {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)} {a : Tm Φ} {A : Ty κ}
    {left right right' : Region Φ} {n : Nat} {P : Fin (n + 1) → Ty κ}
    {blocks : Fin (n + 1) → Region Φ} {tag : Bool}
    (p : UnusedSummand.Program (Φ := Φ) P L Γ) (roll : IterationRolling C)
    (determined : TypeDetermined Γ a A)
    (shape : p.region tag = .cfg (.let₁ a left) (n + 1) blocks)
    {h : Region.HasType Γ (.cfg (.let₁ (.inl a)
      (.case (.var 0) (left.renameVars (Silmaril.DeBruijn.lift Nat.succ)) right)) (n + 1) blocks) L}
    {h' : Region.HasType Γ (.cfg (.let₁ (.inl a)
      (.case (.var 0) (left.renameVars (Silmaril.DeBruijn.lift Nat.succ)) right')) (n + 1) blocks) L}
    {f g : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)}
    (d : RegionDenotes J M h f) (e : RegionDenotes J M h' g) : f = g := by
  have leftResult : ∃ t : (p.region tag).HasType Γ L, RegionDenotes J M t f := by
    rw [shape]
    exact cfg_entry J M determined d
  have rightResult : ∃ t : (p.region tag).HasType Γ L, RegionDenotes J M t g := by
    rw [shape]
    exact cfg_entry J M determined e
  obtain ⟨_, d'⟩ := leftResult
  obtain ⟨_, e'⟩ := rightResult
  exact p.denotes_eq_trimmed J M roll d' e'

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.KnownTag
