module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.BinaryLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.ProductEta.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.PackedBody.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.RetainedLet.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Tensor.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Category.Iteration.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ProductEta.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators

/-! # Binary let on a right-associated packed input -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationBinaryLet

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open CfgEta.TypeCategory
  (singletonValueFamily seqValueBranches whiskerLeftBody whiskerLeftBody_typed
    whiskerLeftRegion whiskerLeftRegion_typed)
open Paper.RetainedLet (diagonal diagonal_typed term_subst_eq returnOnce_typed returnOnce_denotation)
open Paper.PackedBody (applyPacked applyPacked_typed)
open Paper (splitProduct product_variable_eta_context)

universe u v

open Silmaril.Isotope.LambdaSSA.Region.Paper.SingletonReification.BinaryLet

section Syntax

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {X A B D : τ} {a : Tm Φ} {p : Region Φ}

private theorem applyPackedPair_eq :
    applyPackedPair p = (Region.br 0 (.pair (.var 2) (.pair (.var 1) (.var 0)))).lsubst
      (fun _ => p.renameVars (lift (Nat.succ ∘ Nat.succ ∘ Nat.succ))) := by
  simp only [applyPackedPair, lsubst, substVars_renameVars]
  congr 1
  funext i
  cases i <;> rfl

theorem applyPackedPair_typed (hp : ValueBranches [Silmaril.product X (Silmaril.product A B)] p [D]) :
    ValueBranches [B, A, X] (applyPackedPair p) [D] := by
  rw [applyPackedPair_eq]
  have hPair : ValueBranches [B, A, X] (.br 0 (.pair (.var 2) (.pair (.var 1) (.var 0))) : Region Φ)
      [Silmaril.product X (Silmaril.product A B)] :=
    .br rfl (.pair (.var (i := 2) rfl) (.pair (.var (i := 1) rfl) (.var (i := 0) rfl)))
  have w : Ren ([] : VCtx τ) [B, A, X] (Nat.succ ∘ Nat.succ ∘ Nat.succ) := by
    intro i C hi
    simp [At] at hi
  exact hPair.lsubst (singletonValueFamily (hp.renameVars (w.lift _)))

/-- Destructuring the bound product yields the same packed-body application. -/
theorem destructure_applyPackedPair (hp : ValueBranches [Silmaril.product X (Silmaril.product A B)] p [D]) :
    Paper.Eqv [Silmaril.product A B, X]
      (.let₂ (.var 0) ((applyPackedPair p).renameVars (lift (lift Nat.succ))))
      (applyPacked p) [D] := by
  have shape : (applyPackedPair p).renameVars (lift (lift Nat.succ)) =
      (applyPacked p).substVars (splitProduct 0) := by
    simp only [applyPackedPair, applyPacked, renameVars_substVars, substVars_comp]
    congr 1
    funext i
    cases i <;> rfl
  rw [shape]
  exact product_variable_eta_context (rfl : At [Silmaril.product A B, X] 0 (Silmaril.product A B))
    (applyPacked_typed hp).hasType

/-- The extra producer comparison follows from contextual η at a product variable. -/
theorem returnPair_variable {i : Nat} (hi : At [X] i (Silmaril.product A B)) :
    Paper.Eqv [X] (returnPair (.var i : Tm Φ)) (Paper.RetainedLet.returnOnce (.var i))
      [Silmaril.product A B] := by
  have e := product_variable_eta_context hi
    (Region.HasType.br (ℓ := 0) rfl (.var hi) :
      Region.HasType [X] (.br 0 (.var i) : Region Φ) [Silmaril.product A B])
  simp only [Region.substVars, Tm.subst, splitProduct] at e
  refine e.trans (Paper.Eqv.symm (.cfgEta (.native (.letValue (.var hi) ?_))))
  exact .br rfl (.var (i := 0) rfl)

/-- The extra producer comparison follows by β for a constructor pair. -/
theorem returnPair_pair {l r : Tm Φ} (hl : Tm.BranchValue [X] l A) (hr : Tm.BranchValue [X] r B) :
    Paper.Eqv [X] (returnPair (.pair l r)) (Paper.RetainedLet.returnOnce (.pair l r))
      [Silmaril.product A B] := by
  apply Paper.Eqv.trans (s := .br 0 (.pair l r))
  · exact .productBeta (.let₂Beta hl hr
      (.br (rfl : At [Silmaril.product A B] 0 (Silmaril.product A B))
        (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))))
  · exact .symm (.cfgEta (.native (.letValue (.pair hl hr)
      (.br (rfl : At [Silmaril.product A B] 0 (Silmaril.product A B)) (.var (i := 0) rfl)))))

private def returnPairWithInput (a : Tm Φ) : Region Φ :=
  .let₂ a (.br 0 (.pair (.var 2) (.pair (.var 1) (.var 0))))

private theorem returnPairWithInput_typed (ha : Tm.HasType [X] a (Silmaril.product A B)) :
    ValueBranches [X] (returnPairWithInput a) [Silmaril.product X (Silmaril.product A B)] :=
  .let₂ ha (.br rfl (.pair (.var (i := 2) rfl) (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))))

private theorem duplicate_whisker_returnPair (ha : Tm.HasType [X] a (Silmaril.product A B)) :
    Paper.Eqv [X]
      (compLSubst (fun _ => diagonal) (fun _ => whiskerLeftRegion (returnPair a)) 0)
      (returnPairWithInput a) [Silmaril.product X (Silmaril.product A B)] := by
  let P := Silmaril.product X X
  let pairTerm := Tm.pair (.var 0) (.var 0) (Φ := Φ)
  let σ := Tm.liftSubstN 2 (Tm.singleSubst pairTerm)
  let κ := Tm.consSubst (.var 0) (Tm.singleSubst (.var 0 : Tm Φ))
  let b := whiskerLeftBody (returnPair a)
  let υ := lift (lift (lift Nat.succ))
  have hp : Tm.BranchValue [X] pairTerm P := .pair (.var (i := 0) rfl) (.var (i := 0) rfl)
  have hb : Region.HasType [X, X, X] ((b.renameVars υ).substVars σ)
      [Silmaril.product X (Silmaril.product A B)] :=
    ((whiskerLeftBody_typed X (returnPair_typed ha)).hasType.renameVars
      ((((Ren.wk ([] : VCtx τ) X).lift P).lift X).lift X)).substVars
      (((Tm.Subst.HasType.single hp.hasType).lift X).lift X)
  have hβ := Paper.Eqv.productBeta (.let₂Beta (.var (i := 0) (rfl : At [X] 0 X))
    (.var (i := 0) (rfl : At [X] 0 X)) hb)
  change Paper.Eqv [X] (.let₂ pairTerm ((b.renameVars υ).substVars σ))
    (((b.renameVars υ).substVars σ).substVars κ) [Silmaril.product X (Silmaril.product A B)] at hβ
  have ha' : ((((a.rename (lift (Nat.succ ∘ Nat.succ))).rename υ).subst σ).subst κ) = a := by
    rw [Tm.rename_comp, Tm.subst_comp, Tm.subst_rename]
    refine (term_subst_eq ha (η := Tm.var) ?_).trans (Tm.subst_var a)
    intro i C hi
    cases i with
    | zero => rfl
    | succ i => simp [At] at hi
  have eq : ((b.renameVars υ).substVars σ).substVars κ = returnPairWithInput a := by
    change Region.let₂ ((((a.rename (lift (Nat.succ ∘ Nat.succ))).rename υ).subst σ).subst κ)
      (.br 0 (.pair (.var 2) (.pair (.var 1) (.var 0)))) = _
    rw [ha']
    rfl
  rw [eq] at hβ
  exact hβ

/-- Retained evaluation of the pair-producing scrutinee gives literal binary let. -/
theorem literal_let₂ (ha : Tm.HasType [X] a (Silmaril.product A B))
    (hp : ValueBranches [Silmaril.product X (Silmaril.product A B)] p [D]) :
    Paper.Eqv [X]
      (compLSubst
        (compLSubst (fun _ => diagonal) (fun _ => whiskerLeftRegion (returnPair a)))
        (fun _ => p) 0)
      (.let₂ a (applyPackedPair p)) [D] := by
  let T := Silmaril.product X (Silmaril.product A B)
  let hprod := seqValueBranches (diagonal_typed (Φ := Φ) X)
    (whiskerLeftRegion_typed X (returnPair_typed ha))
  let hr := returnPairWithInput_typed ha
  let hk : LSubst.ValueFamily [] [T] [D] (fun _ => p) := singletonValueFamily hp
  have h := (duplicate_whisker_returnPair ha).lsubstPost hprod hr (fun _ _ hi => ((hk.liftVars X) hi).hasType)
  change Paper.Eqv [X] _ (compLSubst (fun _ => returnPairWithInput a) (fun _ => p) 0) [D] at h
  have e : compLSubst (fun _ => returnPairWithInput a) (fun _ => p) 0 =
      .let₂ a (applyPackedPair p) := by
    unfold returnPairWithInput compLSubst
    change Region.let₂ a ((Region.br 0 (.pair (.var 2) (.pair (.var 1) (.var 0)))).lsubst
      (liftLSubstVars (liftLSubstVars (liftLSubstVars (fun _ => p))))) =
      .let₂ a (applyPackedPair p)
    rw [applyPackedPair_eq]
    simp only [lsubst, liftLSubstVars, Region.renameVars_comp]
    congr 4
    funext i
    cases i <;> rfl
  rwa [e] at h

end Syntax

section Denotation

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel bind_pre_map)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite (SubstDenotes regionDenotes_subst pair_map)

universe u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {X A B D : τ} {a : Tm Φ} {p : Region Φ}
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

set_option backward.isDefEq.respectTransparency false in
omit [RegionTypingCoherent (Φ := Φ) J M] in
private theorem applyPackedPair_selected (hp : ValueBranches [Silmaril.product X (Silmaril.product A B)] p [D])
    {g : J.obj (ctxObj M [Silmaril.product X (Silmaril.product A B)]) ⟶ J.obj (labelObj M [D])}
    (dg : RegionDenotes J M hp.hasType g) :
    RegionDenotes J M (applyPackedPair_typed hp).hasType
      (J.map (((ctxPairIso M [X] A B).inv ≫ ((λ_ (M.obj X)).hom ▷
        (M.obj A ⊗ M.obj B)) ≫ (M.obj X ◁ (M.productIso A B).inv) ≫
          (M.productIso X (Silmaril.product A B)).inv) ≫
        (λ_ (M.obj (Silmaril.product X (Silmaril.product A B)))).inv) ≫ g) := by
  let P := Silmaril.product A B
  let T := Silmaril.product X P
  let pack : ctxObj M [B, A, X] ⟶ M.obj T :=
    (ctxPairIso M [X] A B).inv ≫ ((λ_ (M.obj X)).hom ▷
      (M.obj A ⊗ M.obj B)) ≫ (M.obj X ◁ (M.productIso A B).inv) ≫ (M.productIso X P).inv
  let k : ctxObj M [B, A, X] ⟶ ctxObj M [T] := pack ≫ (λ_ (M.obj T)).inv
  let fx := lookup M 2 (rfl : At [B, A, X] 2 X)
  let fa := lookup M 1 (rfl : At [B, A, X] 1 A)
  let fb := lookup M 0 (rfl : At [B, A, X] 0 B)
  have e : CartesianMonoidalCategory.lift fx
      (CartesianMonoidalCategory.lift fa fb ≫ (M.productIso A B).inv) ≫ (M.productIso X P).inv = pack := by
    unfold pack
    simp only [← Category.assoc _ _ (M.productIso X P).inv]
    congr 1
    apply CartesianMonoidalCategory.hom_ext
    · simp only [CartesianMonoidalCategory.lift_fst, Category.assoc, whiskerLeft_fst,
        whiskerRight_fst, ctxPairIso, Iso.symm_inv, associator_hom_fst_assoc, fx, lookup, ctxObj,
        CartesianMonoidalCategory.leftUnitor_hom]
    · simp only [CartesianMonoidalCategory.lift_snd, Category.assoc, whiskerLeft_snd,
        whiskerRight_snd_assoc]
      rw [← Category.assoc (ctxPairIso M [X] A B).inv]
      congr 1
      apply CartesianMonoidalCategory.hom_ext
      · simp only [CartesianMonoidalCategory.lift_fst, Category.assoc, ctxPairIso, Iso.symm_inv,
          associator_hom_snd_fst, fa, lookup, ctxObj]
      · simp only [CartesianMonoidalCategory.lift_snd, Category.assoc, ctxPairIso, Iso.symm_inv,
          associator_hom_snd_snd, fb, lookup, ctxObj]
  have d : Denotes J M
      (.pair (.var (rfl : At [B, A, X] 2 X))
        (.pair (.var (rfl : At [B, A, X] 1 A)) (.var (rfl : At [B, A, X] 0 B))) :
        Tm.HasType [B, A, X] (.pair (.var 2) (.pair (.var 1) (.var 0)) : Tm Φ) T)
      (J.map pack) := by
    have h := Denotes.pair (Denotes.var (J := J) (M := M) (Φ := Φ) (rfl : At [B, A, X] 2 X))
      (Denotes.pair (Denotes.var (rfl : At [B, A, X] 1 A)) (Denotes.var (rfl : At [B, A, X] 0 B)))
    have eq := e
    dsimp only [fx, fa, fb, P] at eq
    simpa only [pair_map, ← J.map_comp, eq] using h
  have hσ : SubstDenotes (Φ := Φ) J M (Γ := [T]) (Δ := [B, A, X])
      (Tm.consSubst (.pair (.var 2) (.pair (.var 1) (.var 0))) (Tm.var ∘
        (Nat.succ ∘ Nat.succ ∘ Nat.succ))) k := by
    intro i F hi
    cases i with
    | zero =>
      have hF : T = F := Option.some.inj hi
      subst F
      refine ⟨.pair (.var rfl) (.pair (.var rfl) (.var rfl)), ?_⟩
      change Denotes J M _ (J.map (k ≫ snd (𝟙_ V) (M.obj T)))
      have hk : k ≫ snd (𝟙_ V) (M.obj T) = pack := by
        change (pack ≫ (λ_ (M.obj T)).inv) ≫ snd (𝟙_ V) (M.obj T) = pack
        rw [← CartesianMonoidalCategory.leftUnitor_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      simpa only [hk] using d
    | succ i => simp [At] at hi
  obtain ⟨_, dt⟩ := regionDenotes_subst J M dg hσ
  exact dt

set_option backward.isDefEq.respectTransparency false in
omit [RegionTypingCoherent (Φ := Φ) J M] in
theorem literal_let₂_selected (ha : Tm.HasType [X] a (Silmaril.product A B))
    (hp : ValueBranches [Silmaril.product X (Silmaril.product A B)] p [D])
    {f : J.obj (ctxObj M [X]) ⟶ J.obj (M.obj (Silmaril.product A B))}
    {g : J.obj (ctxObj M [Silmaril.product X (Silmaril.product A B)]) ⟶ J.obj (labelObj M [D])}
    (df : Denotes J M ha f) (dg : RegionDenotes J M hp.hasType g) :
    RegionDenotes J M (.let₂ ha (applyPackedPair_typed hp).hasType)
      (extend J f ≫ J.map ((λ_ (M.obj X)).hom ▷ M.obj (Silmaril.product A B)) ≫
        J.map (M.productIso X (Silmaril.product A B)).inv ≫
        J.map (λ_ (M.obj (Silmaril.product X (Silmaril.product A B)))).inv ≫ g) := by
  have d := RegionDenotes.let₂ df (applyPackedPair_selected J M hp dg)
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, Category.assoc,
    ← J.map_comp_assoc, Iso.hom_inv_id_assoc, MonoidalCategory.id_tensorHom] at d
  simp only [ctxObj, MonoidalCategory.whisker_exchange_assoc ((λ_ (M.obj X)).hom)
    (M.productIso A B).hom, Category.id_comp, ← MonoidalCategory.whiskerLeft_comp_assoc,
    Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id] at d
  simpa only [J.map_comp_assoc] using d

set_option backward.isDefEq.respectTransparency false in
private theorem denote_applyPackedPair (hp : ValueBranches [Silmaril.product X (Silmaril.product A B)] p [D]) :
    denoteRegion J M (applyPackedPair_typed hp).hasType ≫ J.map (singletonLabelPayload M D) =
      J.map ((ctxPairIso M [X] A B).inv ≫ ((λ_ (M.obj X)).hom ▷
        (M.obj A ⊗ M.obj B)) ≫ (M.obj X ◁ (M.productIso A B).inv) ≫
          (M.productIso X (Silmaril.product A B)).inv) ≫ denoteSingletonRegion J M hp.hasType := by
  rw [← (applyPackedPair_selected J M hp (denoteRegion_spec J M hp.hasType)).eq_denote J M]
  simp only [denoteSingletonRegion, Category.assoc, J.map_comp_assoc]

variable [FreydCategory.CentralUnit J]

set_option backward.isDefEq.respectTransparency false in
theorem returnPair_denotation (ha : Tm.HasType [X] a (Silmaril.product A B)) :
    denoteSingletonRegion J M (returnPair_typed ha).hasType =
      denoteSingletonRegion J M (returnOnce_typed ha).hasType := by
  rw [returnOnce_denotation J M ha (denote_spec J M ha)]
  unfold denoteSingletonRegion
  rw [denoteRegion_let₂_br_eta J M (FreydCategory.CentralUnit.unit_central (J := J)) rfl ha]
  exact denoteSingletonRegion_br J M (denote_spec J M ha)

set_option backward.isDefEq.respectTransparency false in
theorem denote_literal_let₂ (ha : Tm.HasType [X] a (Silmaril.product A B))
    (hp : ValueBranches [Silmaril.product X (Silmaril.product A B)] p [D]) :
    denoteSingletonRegion J M (.let₂ ha (applyPackedPair_typed hp).hasType) =
      extend J (denoteSingletonRegion J M (returnPair_typed ha).hasType) ≫
        J.map (M.productIso X (Silmaril.product A B)).inv ≫ denoteSingletonRegion J M hp.hasType := by
  rw [returnPair_denotation J M ha, returnOnce_denotation J M ha (denote_spec J M ha)]
  rw [denoteSingletonRegion, ← (RegionDenotes.let₂ (denote_spec J M ha)
    (denoteRegion_spec J M (applyPackedPair_typed hp).hasType)).eq_denote J M]
  rw [← Category.assoc, ← bind_pre_map J ((λ_ (M.obj X)).inv)]
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, Category.assoc,
    denote_applyPackedPair J M hp]
  congr 1
  rw [← J.map_comp_assoc, ← J.map_comp_assoc, ← J.map_comp_assoc]
  congr 1
  simp only [Category.assoc, Iso.hom_inv_id_assoc, MonoidalCategory.id_tensorHom]
  simp only [ctxObj, MonoidalCategory.whisker_exchange_assoc ((λ_ (M.obj X)).hom)
    (M.productIso A B).hom, ← MonoidalCategory.comp_whiskerRight_assoc, Iso.inv_hom_id,
    MonoidalCategory.id_whiskerRight, Category.id_comp, ← MonoidalCategory.whiskerLeft_comp_assoc,
    Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id]

end Denotation

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SingletonReificationBinaryLet
