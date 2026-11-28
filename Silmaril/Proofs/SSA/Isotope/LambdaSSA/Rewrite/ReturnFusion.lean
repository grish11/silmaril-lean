module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Outward.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Values.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.Thms

/-! # Categorical evaluation of typed returns and fused binders -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ReturnFusion

open Silmaril Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory (fst snd lift)
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel case_postcomp extend_map extend_postmap)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (duplicate extend retainedContext)
open Region.CfgEta.TypeCategory (returnRegion returnRegion_typed)
open SingletonDispatcher (labelInject_payload)

open scoped MonoidalCategory

local notation "pairArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair
local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

universe u v u₁ v₁ u₂ v₂

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

private theorem boundReturn_denotes {Γ : VCtx τ} {L : LCtx τ} {i : Nat} {A : τ} {a : Tm Φ}
    (hi : At L i A) {ha : Tm.HasType Γ a A} {f : J.obj (ctxObj M Γ) ⟶ J.obj (M.obj A)}
    (da : Denotes J M ha f) :
    RegionDenotes J M (.let₁ ha (.br hi (.var (i := 0) rfl))) (f ≫ J.map (labelInject M i hi)) := by
  have e := (RegionDenotes.eq_denote J M (RegionDenotes.br (h := hi) da)).trans
    (denoteRegion_branchBind J M (FreydCategory.CentralUnit.unit_central (J := J)) hi ha)
  exact e.symm ▸ denoteRegion_spec J M (.let₁ ha (.br hi (.var (i := 0) rfl)))

private theorem extend_snd {E X : V} (f : J.obj E ⟶ J.obj X) :
    extend J f ≫ J.map (snd E X) = f := by
  simp only [extend, PremonoidalCategory.leftTensor, PremonoidalCategory.id_whiskerRight,
    Category.id_comp, Category.assoc]
  rw [FreydCategory.whiskerLeft_snd J, ← J.map_comp_assoc]
  simp [duplicate]

set_option backward.isDefEq.respectTransparency false in
theorem denote_op_boundReturn_sequencing {Γ : VCtx τ} {L : LCtx τ} {i : Nat}
    {a : Tm Φ} (p : Φ) (hi : At L i (instrTrg p)) (ha : Tm.HasType Γ a (instrSrc p)) :
    denoteRegion J M (.let₁ (.op ha) (.br hi (.var (i := 0) rfl))) =
      denoteRegion J M (.let₁ (.let₁ ha (.op (f := p) (.var (i := 0) rfl))) (.br hi (.var (i := 0) rfl))) := by
  let arg := denote J M ha
  have value := denote_spec J M ha
  have newest := Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At (instrSrc p :: Γ) 0 (instrSrc p))
  rw [← RegionDenotes.eq_denote J M (boundReturn_denotes J M hi (Denotes.op value)),
    ← RegionDenotes.eq_denote J M (boundReturn_denotes J M hi (Denotes.let₁ value (Denotes.op newest)))]
  change (arg ≫ _) ≫ _ = (bindArrow J arg (J.map (snd (ctxObj M Γ) (M.obj (instrSrc p))) ≫ _)) ≫ _
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, ← Category.assoc, extend_snd]

set_option backward.isDefEq.respectTransparency false in
theorem denote_inl_boundReturn_sequencing {Γ : VCtx τ} {L : LCtx τ} {i : Nat}
    {A B : τ} {a : Tm Φ} (hi : At L i (coprod A B)) (ha : Tm.HasType Γ a A) :
    denoteRegion J M (.let₁ (.inl ha) (.br hi (.var (i := 0) rfl))) =
      denoteRegion J M (.let₁ ha (.br hi (.inl (.var (i := 0) rfl)))) := by
  have da := denote_spec J M ha
  have dv := Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At (A :: Γ) 0 A)
  have original := boundReturn_denotes J M hi (Denotes.inl da)
  have sequenced := RegionDenotes.let₁ da (RegionDenotes.br (h := hi) (Denotes.inl dv))
  rw [← RegionDenotes.eq_denote J M original, ← RegionDenotes.eq_denote J M sequenced]
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, lookup, ctxObj, ← Category.assoc, extend_snd]

set_option backward.isDefEq.respectTransparency false in
theorem denote_inr_boundReturn_sequencing {Γ : VCtx τ} {L : LCtx τ} {i : Nat}
    {A B : τ} {a : Tm Φ} (hi : At L i (coprod A B)) (ha : Tm.HasType Γ a B) :
    denoteRegion J M (.let₁ (.inr ha) (.br hi (.var (i := 0) rfl))) =
      denoteRegion J M (.let₁ ha (.br hi (.inr (.var (i := 0) rfl)))) := by
  have da := denote_spec J M ha
  have dv := Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At (B :: Γ) 0 B)
  have original := boundReturn_denotes J M hi (Denotes.inr da)
  have sequenced := RegionDenotes.let₁ da (RegionDenotes.br (h := hi) (Denotes.inr dv))
  rw [← RegionDenotes.eq_denote J M original, ← RegionDenotes.eq_denote J M sequenced]
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, lookup, ctxObj, ← Category.assoc, extend_snd]

set_option backward.isDefEq.respectTransparency false in
theorem denote_abort_boundReturn_sequencing {Γ : VCtx τ} {L : LCtx τ} {i : Nat}
    {D : τ} {a : Tm Φ} (hi : At L i D) (ha : Tm.HasType Γ a empty) :
    denoteRegion J M (.let₁ (.abort ha) (.br hi (.var (i := 0) rfl))) =
      denoteRegion J M (.let₁ ha (.let₁ (.abort (.var (i := 0) rfl)) (.br hi (.var (i := 0) rfl)))) := by
  have da := denote_spec J M ha
  have dv := Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At (empty :: Γ) 0 empty)
  have original := boundReturn_denotes J M hi (Denotes.abort da)
  have sequenced := RegionDenotes.let₁ da (boundReturn_denotes J M hi (Denotes.abort dv))
  rw [← RegionDenotes.eq_denote J M original, ← RegionDenotes.eq_denote J M sequenced]
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, lookup, ctxObj, ← Category.assoc, extend_snd]

theorem denote_let₂_boundReturn_fusion {Γ : VCtx τ} {L : LCtx τ} {i : Nat}
    {A B D : τ} {a b : Tm Φ} (hi : At L i D)
    (ha : Tm.HasType Γ a (product A B)) (hb : Tm.HasType (B :: A :: Γ) b D) :
    denoteRegion J M (.let₂ ha (.let₁ hb (.br hi (.var (i := 0) rfl)))) =
      denoteRegion J M (.let₁ (.let₂ ha hb) (.br hi (.var (i := 0) rfl))) := by
  have da := denote_spec J M ha
  have db := denote_spec J M hb
  have dl := RegionDenotes.let₂ da (boundReturn_denotes J M hi db)
  have dr := boundReturn_denotes J M hi (Denotes.let₂ da db)
  rw [← RegionDenotes.eq_denote J M dl, ← RegionDenotes.eq_denote J M dr]
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, Category.assoc]

theorem denote_case_boundReturn_fusion {Γ : VCtx τ} {L : LCtx τ} {i : Nat}
    {A B D : τ} {e l r : Tm Φ} (hi : At L i D)
    (he : Tm.HasType Γ e (coprod A B)) (hl : Tm.HasType (A :: Γ) l D)
    (hr : Tm.HasType (B :: Γ) r D) :
    denoteRegion J M (.case he (.let₁ hl (.br hi (.var (i := 0) rfl)))
      (.let₁ hr (.br hi (.var (i := 0) rfl)))) =
        denoteRegion J M (.let₁ (.case he hl hr) (.br hi (.var (i := 0) rfl))) := by
  have de := denote_spec J M he
  have dl := denote_spec J M hl
  have dr := denote_spec J M hr
  have d₁ := RegionDenotes.case de (boundReturn_denotes J M hi dl) (boundReturn_denotes J M hi dr)
  have d₂ := boundReturn_denotes J M hi (Denotes.case de dl dr)
  rw [← RegionDenotes.eq_denote J M d₁, ← RegionDenotes.eq_denote J M d₂]
  exact (case_postcomp J (denote J M he ≫ J.map (M.coprodIso A B).hom)
    (denote J M hl) (denote J M hr) (J.map (labelInject M i hi))).symm

private theorem denote_pair_boundReturn_order {Γ : VCtx τ} {L : LCtx τ} {i : Nat}
    {A B : τ} {a b : Tm Φ} (hi : At L i (product A B))
    (ha : Tm.HasType Γ a A) (hb : Tm.HasType Γ b B) :
    denoteRegion J M (.let₁ (.pair ha hb) (.br hi (.var (i := 0) rfl))) =
      bindArrow J (denote J M ha) (bindArrow J
        (J.map (CartesianMonoidalCategory.fst (ctxObj M Γ) (M.obj A)) ≫ denote J M hb)
        (J.map (CartesianMonoidalCategory.lift
          (CartesianMonoidalCategory.fst (ctxObj M Γ ⊗ M.obj A) (M.obj B) ≫
            CartesianMonoidalCategory.snd (ctxObj M Γ) (M.obj A))
          (CartesianMonoidalCategory.snd (ctxObj M Γ ⊗ M.obj A) (M.obj B))) ≫
          J.map (M.productIso A B).inv ≫ J.map (labelInject M i hi))) := by
  rw [← RegionDenotes.eq_denote J M (boundReturn_denotes J M hi
    (Denotes.pair (denote_spec J M ha) (denote_spec J M hb)))]
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair,
    Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.retainedContext,
    Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem denote_pair_boundReturn_sequencing {Γ : VCtx τ} {L : LCtx τ} {i : Nat}
    {A B : τ} {a b : Tm Φ} (hi : At L i (product A B))
    (ha : Tm.HasType Γ a A) (hb : Tm.HasType Γ b B) :
    denoteRegion J M (.let₁ (.pair ha hb) (.br hi (.var (i := 0) rfl))) =
      denoteRegion J M (.let₁ ha (.let₁ (hb.rename (Ren.wk Γ A))
        (.br hi (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))))) := by
  let R := ctxObj M Γ
  let U := M.obj A
  let W := M.obj B
  let left : (R ⊗ U) ⊗ W ⟶ U := fst (R ⊗ U) W ≫ snd R U
  let right : (R ⊗ U) ⊗ W ⟶ W := snd (R ⊗ U) W
  have pair_of_maps : pairArrow J (J.map left) (J.map right) = J.map (lift left right) := by
    unfold Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair
      Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind retainedContext
    rw [extend_map, ← J.map_comp, extend_map, ← J.map_comp, ← J.map_comp]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have dLeft :
      Denotes J M (Φ := Φ) (.var (i := 1) (rfl : At (B :: A :: Γ) 1 A)) (J.map left) := by
    simpa [left, R, U, W, lookup, ctxObj] using
      (Denotes.var (J := J) (M := M) (Φ := Φ) (i := 1) (rfl : At (B :: A :: Γ) 1 A))
  have dRight :
      Denotes J M (Φ := Φ) (.var (i := 0) (rfl : At (B :: A :: Γ) 0 B)) (J.map right) := by
    simpa [right, R, U, W, lookup, ctxObj] using
      (Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (rfl : At (B :: A :: Γ) 0 B))
  have db := (denote_spec J M hb).weaken J M A
  have dr := RegionDenotes.br (h := hi) (Denotes.pair dLeft dRight)
  rw [pair_of_maps] at dr
  have dr' := RegionDenotes.let₁ (denote_spec J M ha) (RegionDenotes.let₁ db dr)
  rw [← RegionDenotes.eq_denote J M dr', denote_pair_boundReturn_order J M hi ha hb]
  simp only [left, right, R, U, W, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, Category.assoc]

private theorem noBlocks_rename {r : Region Φ} (h : r.NoLocalBlocks) (ρ : Nat → Nat) :
    (r.renameVars ρ).NoLocalBlocks := by
  induction r generalizing ρ <;> simp_all [Region.NoLocalBlocks, Region.renameVars]

private theorem noBlocks_subst {r : Region Φ} (h : r.NoLocalBlocks) (θ : Nat → Tm Φ) :
    (r.substVars θ).NoLocalBlocks := by
  induction r generalizing θ <;> simp_all [Region.NoLocalBlocks, Region.substVars]

private theorem noBlocks_lsubst {r : Region Φ} (h : r.NoLocalBlocks)
    {σ : Nat → Region Φ} (hσ : ∀ i, (σ i).NoLocalBlocks) : (r.lsubst σ).NoLocalBlocks := by
  have liftNoBlocks {s : Nat → Region Φ} (hs : ∀ i, (s i).NoLocalBlocks) (i : Nat) :
      (Region.liftLSubstVars s i).NoLocalBlocks := noBlocks_rename (hs i) _
  induction r generalizing σ with
  | br i a => exact noBlocks_subst (hσ i) _
  | let₁ a r ih => exact ih h (liftNoBlocks hσ)
  | let₂ a r ih => exact ih h (liftNoBlocks (liftNoBlocks hσ))
  | case a l r ihl ihr => exact ⟨ihl h.1 (liftNoBlocks hσ), ihr h.2 (liftNoBlocks hσ)⟩
  | cfg e n bs ihe ihbs =>
    obtain ⟨rfl, he⟩ := h
    exact ⟨rfl, ihe he hσ⟩

private theorem returnRegion_noBlocks (a : Tm Φ) : (returnRegion a).NoLocalBlocks := by
  induction a with
  | let₁ a b iha ihb => exact noBlocks_lsubst iha (fun _ => ihb)
  | _ => trivial

set_option backward.isDefEq.respectTransparency false in
theorem denote_returnRegion_boundReturn
    (copyCentral : ∀ E : V, PremonoidalCategory.IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))
    {Γ : VCtx τ} {D : τ} {a : Tm Φ} (ht : Tm.HasType Γ a D) :
    denoteRegion J M (returnRegion_typed ht).hasType =
      denoteRegion J M (.let₁ ht (.br (L := [D]) (ℓ := 0) rfl (.var (i := 0) rfl))) := by
  induction ht with
  | @let₁ Γ a b A B ha hb iha ihb =>
    let ia : M.obj A ⟶ labelObj M [A] := labelInject M 0 (rfl : At [A] 0 A)
    let ib : M.obj B ⟶ labelObj M [B] := labelInject M 0 (rfl : At [B] 0 B)
    let left := (returnRegion_typed ha).hasType
    let right := (returnRegion_typed hb).hasType
    let k : J.obj (ctxObj M Γ ⊗ labelObj M [A]) ⟶ J.obj (labelObj M [B]) :=
      J.map ((ctxObj M Γ) ◁ singletonLabelPayload M A) ≫ denoteRegion J M right
    have hk : ContinuationDenotes J M (Γ := Γ) (L := [A]) (K := [B])
        (fun _ => returnRegion b) k := by
      intro j T hj
      cases j with
      | zero =>
        cases Option.some.inj hj
        have e : J.map ((𝟙 (ctxObj M Γ)) ⊗ₘ ia) ≫ k = denoteRegion J M right := by
          simp only [k, ia, MonoidalCategory.id_tensorHom, ← Category.assoc, ← J.map_comp,
            ← MonoidalCategory.whiskerLeft_comp, labelInject_payload, MonoidalCategory.whiskerLeft_id,
            J.map_id, Category.id_comp]
        exact ⟨right, e.symm ▸ denoteRegion_spec J M right⟩
      | succ j => simp [At] at hj
    have eq := denoteRegion_lsubst_noLocalBlocks J M copyCentral left
      (returnRegion_typed (.let₁ ha hb)).hasType
      (returnRegion_typed ha) (returnRegion_noBlocks a) hk
    change denoteRegion J M _ = _
    rw [eq, show denoteRegion J M left = _ from iha,
      ← RegionDenotes.eq_denote J M (boundReturn_denotes J M (rfl : At [A] 0 A) (denote_spec J M ha)),
      ← RegionDenotes.eq_denote J M (boundReturn_denotes J M (rfl : At [B] 0 B)
        (Denotes.let₁ (denote_spec J M ha) (denote_spec J M hb)))]
    have ehb : denoteRegion J M right = denote J M hb ≫ J.map ib :=
      ihb.trans (RegionDenotes.eq_denote J M
        (boundReturn_denotes J M (rfl : At [B] 0 B) (denote_spec J M hb))).symm
    unfold Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
    simp only [k, ehb, extend_postmap, Category.assoc, ← J.map_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp, labelInject_payload, MonoidalCategory.whiskerLeft_id,
      J.map_id, Category.id_comp, ib]
  | _ => rfl

section LoweredReturns

variable (copyCentral : ∀ E : V, PremonoidalCategory.IsCentral (J.map (duplicate E) ≫
    (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv))

include copyCentral

theorem denote_let₂_returnRegion_fusion {Γ : VCtx τ} {A B D : τ} {a b : Tm Φ}
    (ha : Tm.HasType Γ a (product A B)) (hb : Tm.HasType (B :: A :: Γ) b D) :
    denoteRegion J M (.let₂ ha (returnRegion_typed hb).hasType) =
      denoteRegion J M (returnRegion_typed (.let₂ ha hb)).hasType := by
  have hi : At [D] 0 D := rfl
  let body := (returnRegion_typed hb).hasType
  let normalized := Region.HasType.let₁ hb (.br hi (.var (i := 0) rfl))
  have da := denote_spec J M ha
  calc
    denoteRegion J M (.let₂ ha body) = denoteRegion J M (.let₂ ha normalized) := by
      rw [← RegionDenotes.eq_denote J M (RegionDenotes.let₂ da (denoteRegion_spec J M body)),
        ← RegionDenotes.eq_denote J M (RegionDenotes.let₂ da (denoteRegion_spec J M normalized))]
      rw [show denoteRegion J M body = denoteRegion J M normalized from
        denote_returnRegion_boundReturn J M copyCentral hb]
    _ = _ := (denote_let₂_boundReturn_fusion J M hi ha hb).trans
      (denote_returnRegion_boundReturn J M copyCentral (.let₂ ha hb)).symm

theorem denote_case_returnRegion_fusion {Γ : VCtx τ} {A B D : τ} {a l r : Tm Φ}
    (ha : Tm.HasType Γ a (coprod A B))
    (hl : Tm.HasType (A :: Γ) l D) (hr : Tm.HasType (B :: Γ) r D) :
    denoteRegion J M (.case ha (returnRegion_typed hl).hasType (returnRegion_typed hr).hasType) =
      denoteRegion J M (returnRegion_typed (.case ha hl hr)).hasType := by
  have hi : At [D] 0 D := rfl
  let left := (returnRegion_typed hl).hasType
  let right := (returnRegion_typed hr).hasType
  let leftNorm := Region.HasType.let₁ hl (.br hi (.var (i := 0) rfl))
  let rightNorm := Region.HasType.let₁ hr (.br hi (.var (i := 0) rfl))
  have da := denote_spec J M ha
  calc
    denoteRegion J M (.case ha left right) = denoteRegion J M (.case ha leftNorm rightNorm) := by
      rw [← RegionDenotes.eq_denote J M (RegionDenotes.case da (denoteRegion_spec J M left)
        (denoteRegion_spec J M right)),
        ← RegionDenotes.eq_denote J M (RegionDenotes.case da (denoteRegion_spec J M leftNorm)
          (denoteRegion_spec J M rightNorm))]
      rw [show denoteRegion J M left = denoteRegion J M leftNorm from
        denote_returnRegion_boundReturn J M copyCentral hl,
        show denoteRegion J M right = denoteRegion J M rightNorm from
          denote_returnRegion_boundReturn J M copyCentral hr]
    _ = _ := (denote_case_boundReturn_fusion J M hi ha hl hr).trans
      (denote_returnRegion_boundReturn J M copyCentral (.case ha hl hr)).symm

end LoweredReturns

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ReturnFusion
