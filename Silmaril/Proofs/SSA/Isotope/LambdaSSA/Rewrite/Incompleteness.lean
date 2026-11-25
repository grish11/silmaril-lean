module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Labels
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SubstitutionObstruction

/-! # A categorical equation beyond the CFG entry theory -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend)

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

private theorem unitLetBranch_common {Γ : VCtx τ} {L : LCtx τ}
    {ℓ : Nat} (hl : At L ℓ (Silmaril.unit : τ)) :
    ∃ (hl₁ : Region.HasType (Φ := Φ) Γ (.let₁ .unit (.br ℓ (.var 0))) L)
      (hbr : Region.HasType (Φ := Φ) Γ (.br ℓ .unit) L),
      ∃ f, RegionDenotes J M hl₁ f ∧ RegionDenotes J M hbr f := by
  let A : τ := Silmaril.unit
  let E := ctxObj M Γ
  let u : E ⟶ M.obj A := CartesianMonoidalCategory.toUnit E ≫ M.unitIso.inv
  let inject : M.obj A ⟶ labelObj M L := labelInject M ℓ hl
  have hx : At (A :: Γ) 0 A := rfl
  have dv : Denotes J M (.var (Φ := Φ) hx) (J.map (CartesianMonoidalCategory.snd E (M.obj A))) :=
    Denotes.var hx
  have du : Denotes J M (.unit (Φ := Φ) (Γ := Γ)) (J.map u) := Denotes.unit
  have dlet := RegionDenotes.let₁ du (RegionDenotes.br (h := hl) dv)
  have dbr := RegionDenotes.br (h := hl) du
  have hb : extend J (J.map u) ≫ J.map (CartesianMonoidalCategory.snd E (M.obj A)) ≫ J.map inject =
      J.map u ≫ J.map inject := by
    rw [extend_map, ← Functor.map_comp_assoc, CartesianMonoidalCategory.lift_snd]
  change RegionDenotes J M (.let₁ (.unit (Φ := Φ)) (.br hl (.var hx)))
    (extend J (J.map u) ≫ J.map (CartesianMonoidalCategory.snd E (M.obj A)) ≫ J.map inject) at dlet
  rw [hb] at dlet
  exact ⟨_, _, _, dlet, dbr⟩

variable [RegionTypingCoherent (Φ := Φ) J M]

theorem unitExit_incomplete :
    ∃ (hr : Region.HasType (Φ := Φ) [(Silmaril.unit : τ)]
        (.cfg (.let₁ .unit (.br 1 (.var 0))) 1 (fun _ => .let₁ .unit (.br 1 (.var 0))))
        [Silmaril.unit])
      (hs : Region.HasType (Φ := Φ) [(Silmaril.unit : τ)] (.let₁ .unit (.br 0 (.var 0))) [Silmaril.unit]),
      (¬ Region.CfgEquiv (Φ := Φ) [(Silmaril.unit : τ)]
        (.cfg (.let₁ .unit (.br 1 (.var 0))) 1 (fun _ => .let₁ .unit (.br 1 (.var 0))))
        (.let₁ .unit (.br 0 (.var 0))) [Silmaril.unit]) ∧
      denoteRegion J M hr = denoteRegion J M hs := by
  let A : τ := Silmaril.unit
  let R : Fin 1 → τ := fun _ => A
  let blocks : Fin 1 → Region Φ := fun _ => .let₁ .unit (.br 1 (.var 0))
  have hl : At [A] 0 A := rfl
  have hb (i : Fin 1) : Region.HasType (R i :: [A]) (blocks i) (List.ofFn R ++ [A]) :=
    .let₁ .unit (.br (exitAt R hl) (.var rfl))
  obtain ⟨hl₁, hbr, f, dl₁, dbr⟩ :=
    unitLetBranch_common (Φ := Φ) J M (Γ := [A]) (exitAt R hl)
  obtain ⟨hs, hs', g, ds, ds'⟩ := unitLetBranch_common (Φ := Φ) J M (Γ := [A]) hl
  obtain ⟨c, dc⟩ := collectiveDenotes_exists_succ J M 0 [A] R [A] (fun i => denoteRegion J M (hb i))
  have d (i : Fin 1) := denoteRegion_spec J M (hb i)
  have dr := RegionDenotes.cfg hl₁ hb dl₁ d dc
  have dr' := RegionDenotes.cfg hbr hb dbr d dc
  refine ⟨.cfg R hl₁ hb, hs, unitExit_not_equiv, ?_⟩
  calc
    _ = denoteRegion J M (.cfg R hbr hb) := (dr.eq_denote J M).symm.trans (dr'.eq_denote J M)
    _ = denoteRegion J M hs' :=
      (Region.CfgEquiv.cfgBrExit R hl Tm.BranchValue.unit hb).sound J M _ _
    _ = _ := (ds'.eq_denote J M).symm.trans (ds.eq_denote J M)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
