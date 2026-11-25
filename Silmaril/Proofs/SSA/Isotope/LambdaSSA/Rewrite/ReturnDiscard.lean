module
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ReturnFusion.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Thms

/-! # Denotation of a lowered pure return followed by discard -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ReturnDiscard

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel extend_map)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (duplicate)
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA.Region.CfgEta.TypeCategory (returnRegion returnRegion_typed)

universe u v w u₁ v₁ u₂ v₂
variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  {ε : Type w} [HasEff Φ ε] {pe : ε}

set_option backward.isDefEq.respectTransparency false in
theorem denote_pure_return_discard [FreydCategory.CentralUnit J]
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    (hInstr : ∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
    {X A : τ} {a : Tm Φ} (ha : Tm.HasType [X] a A) (hp : Tm.Pure pe a)
    (hd : Region.HasType [X] (Region.compLSubst (fun _ => returnRegion a)
      (fun _ => .br 0 (.unit : Tm Φ)) 0) [(Silmaril.unit : τ)]) :
    denoteRegion J M hd =
      denoteRegion J M (.br (Φ := Φ) (ℓ := 0) (L := [(Silmaril.unit : τ)]) (Γ := [X]) rfl .unit) := by
  let U : τ := Silmaril.unit
  let hi : At [U] 0 U := rfl
  let erase (E : V) : E ⟶ M.obj U :=
    CartesianMonoidalCategory.toUnit _ ≫ M.unitIso.inv
  have erase_natural {E F : V} (p : E ⟶ F) : p ≫ erase F = erase E := by
    apply (cancel_mono M.unitIso.hom).mp
    exact Subsingleton.elim _ _
  let k₀ : ctxObj M [X] ⊗ labelObj M [A] ⟶ labelObj M [U] :=
    erase _ ≫ labelInject M 0 hi
  have hk : ContinuationDenotes J M (Γ := [X]) (L := [A]) (K := [U])
      (fun _ => .br 0 (.unit : Tm Φ)) (J.map k₀) := by
    intro i D hD
    refine ⟨.br hi .unit, ?_⟩
    dsimp only [k₀]
    rw [← J.map_comp, ← Category.assoc, erase_natural, J.map_comp]
    exact .br Denotes.unit
  have hcopy (E : V) : PremonoidalCategory.IsCentral (J.map (duplicate E) ≫
      (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv) := by
    obtain ⟨h, e⟩ := shared E E
    exact Silmaril.Isotope.LetIter.Semantics.Categorical.duplicate_central_of_tensor_eqToIso J E h e
  obtain ⟨p, dp⟩ := hp.denotes_map J M ha hInstr
  have bindMap {R B D : V} (f : R ⟶ B) (g : R ⊗ B ⟶ D) :
      Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind J (J.map f) (J.map g) =
        J.map (CartesianMonoidalCategory.lift (𝟙 R) f ≫ g) := by
    rw [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, extend_map, J.map_comp]
  let lookup₀ := lookup M 0 (rfl : At [A, X] 0 A)
  let out₀ := lookup₀ ≫ labelInject M 0 (rfl : At [A] 0 A)
  let p₀ := CartesianMonoidalCategory.lift (𝟙 _) p ≫ out₀
  have do₀ :
      RegionDenotes J M (.br (Φ := Φ) (rfl : At [A] 0 A) (.var (rfl : At [A, X] 0 A))) (J.map out₀) := by
    rw [J.map_comp]
    exact .br (.var (i := 0) rfl)
  have dr : denoteRegion J M (returnRegion_typed ha).hasType = J.map p₀ := by
    rw [denote_returnRegion_boundReturn J M hcopy ha]
    exact (RegionDenotes.eq_denote J M (RegionDenotes.let₁ dp do₀)).symm.trans (bindMap p out₀)
  change denoteRegion J M hd = _
  rw [denoteRegion_lsubst_sharedTensor J M shared (returnRegion_typed ha).hasType hd
    (PureBranches.of_valueBranches J M (returnRegion_typed ha)) hk, dr, bindMap]
  have hfinish : RegionDenotes J M (.br (Φ := Φ) hi (.unit (Γ := [X])))
      (J.map (erase (ctxObj M [X]) ≫ labelInject M 0 hi)) := by
    rw [J.map_comp]
    exact .br Denotes.unit
  rw [← RegionDenotes.eq_denote J M hfinish]
  simp only [k₀, ← Category.assoc, erase_natural]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ReturnDiscard
