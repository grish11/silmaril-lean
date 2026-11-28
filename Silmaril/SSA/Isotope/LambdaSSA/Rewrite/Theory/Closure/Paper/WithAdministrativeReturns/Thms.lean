module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.Native.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorCaseOperands.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithLetCase.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Roundtrip.CfgEta.Thms

/-! # Inclusions, administrative replay, and coherent soundness -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns

open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls
open Paper.Extension.Singleton (ofRegion SeedDenotes homRel)
open Silmaril.DeBruijn (lift)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w u₁ u₂ v₁ v₂
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

/-- Include the shared base at the same singleton types and representatives. -/
@[expose] def fromUnaryReturns : WithUnaryReturns.TypeCategory (τ := τ) (Φ := Φ) pe ⥤
    TypeCategory (τ := τ) (Φ := Φ) pe :=
  CategoryTheory.Quotient.lift (homRel (WithUnaryReturns.Step pe)) (projection pe) <| by
    rintro _ _ _ _ ⟨r, s, hr, hs, hf, hg, eqv⟩
    exact CategoryTheory.Quotient.sound _ ⟨r, s, hr, hs, hf, hg, eqv.mapSeed Or.inl⟩

theorem fromUnaryReturns_map_ofRegion {X Y : τ} {r : Region Φ} (hr : ValueBranches [X] r [Y]) :
    (fromUnaryReturns pe).map (ofRegion (WithUnaryReturns.Step pe) hr) = ofRegion (Step pe) hr :=
  rfl

theorem projection_comp_fromUnaryReturns :
    Paper.Extension.Singleton.projection (WithUnaryReturns.Step (τ := τ) (Φ := Φ) pe) ⋙
      fromUnaryReturns pe = projection pe :=
  CategoryTheory.Quotient.lift_spec _ _ _

theorem ofUnaryReturns (h : WithUnaryReturns.Eqv pe Γ r s L) : Eqv pe Γ r s L :=
  h.mapSeed Or.inl

theorem ofConstructorOperands (h : WithConstructorCaseOperands.Eqv Γ r s L) : Eqv pe Γ r s L :=
  h.mapSeed (fun e => .inr (.inl e))

theorem ofCaseReturns (h : WithLetCase.Eqv Γ r s L) : Eqv pe Γ r s L :=
  h.mapSeed (fun e => .inr (.inr e))

theorem includeReturnedCall (h : WithComputedCallReturns.Step Γ r s L) : Step pe Γ r s L :=
  .inl (.inl (.inr h))

theorem let₁_let₁ {A D : τ} {a b : Tm Φ} (ha : Tm.HasType Γ a A)
    (hb : Tm.HasType (A :: Γ) b D) (hr : HasType (D :: Γ) r L) :
    Eqv pe Γ (.let₁ (.let₁ a b) r) (.let₁ a (.let₁ b (r.renameVars (lift Nat.succ)))) L :=
  ofUnaryReturns pe (WithUnaryReturns.let₁_let₁ pe ha hb hr)

theorem let₁_op {a : Tm Φ} (p : Φ) (ha : Tm.HasType Γ a (instrSrc p))
    (hr : HasType (instrTrg p :: Γ) r L) :
    Eqv pe Γ (.let₁ (.op p a) r)
      (.let₁ a (.let₁ (.op p (.var 0)) (r.renameVars (lift Nat.succ)))) L :=
  ofUnaryReturns pe (WithUnaryReturns.let₁_op pe p ha hr)

theorem let₁_case {A B D : τ} {e a b : Tm Φ} (he : Tm.HasType Γ e (coprod A B))
    (ha : Tm.HasType (A :: Γ) a D) (hb : Tm.HasType (B :: Γ) b D) (hr : HasType (D :: Γ) r L) :
    Eqv pe Γ (.let₁ (.case e a b) r) (WithLetCase.distributed e a b r) L :=
  ofCaseReturns pe (WithLetCase.distribute he ha hb hr)

/-- Keep the exact representatives while packing the common ordered exits. -/
theorem Eqv.packed_eq {X : τ} (hr : ValueBranches [X] r L)
    (hs : ValueBranches [X] s L) (e : Eqv pe [X] r s L) :
    ofRegion (Step pe) hr.packExits = ofRegion (Step pe) hs.packExits :=
  (Paper.Extension.Singleton.ofRegion_eq_iff (Step pe) _ _).2
    (.lsubstPost e hr hs (fun _ _ hi => (packExits_valueFamily [X] L hi).hasType))

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
    Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)

include shared in
theorem seedDenotes : SeedDenotes (Seed := Step (τ := τ) (Φ := Φ) pe) J M :=
  fun h hr hs => h.elim (fun e => WithUnaryReturns.seedDenotes pe J M shared e hr hs)
    (fun e => e.elim (fun h => WithConstructorCaseOperands.step_denotes J M h hr hs)
      (fun h => WithLetCase.step_denotes J M h hr hs))

include shared in
theorem Eqv.sound (e : Eqv pe Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  Paper.Extension.Eqv.sound J M shared (seedDenotes pe J M shared) e hr hs

/-- Interpret the common quotient with the existing coherent Paper laws. -/
@[expose] noncomputable def denoteFunctor : TypeCategory (τ := τ) (Φ := Φ) pe ⥤ C :=
  Paper.Extension.Singleton.denoteFunctor J M shared (seedDenotes pe J M shared)

/-- The base and common quotient interpret each inherited arrow identically. -/
theorem fromUnaryReturns_comp_denoteFunctor :
    fromUnaryReturns (τ := τ) (Φ := Φ) pe ⋙ denoteFunctor pe J M shared =
      WithUnaryReturns.denoteFunctor pe J M shared := by
  apply CategoryTheory.Quotient.lift_unique'
  rw [← Functor.assoc, projection_comp_fromUnaryReturns]
  exact (Paper.Extension.Singleton.projection_comp_denoteFunctor J M shared (seedDenotes pe J M shared)).trans
    (Paper.Extension.Singleton.projection_comp_denoteFunctor J M shared
      (WithUnaryReturns.seedDenotes pe J M shared)).symm

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns
