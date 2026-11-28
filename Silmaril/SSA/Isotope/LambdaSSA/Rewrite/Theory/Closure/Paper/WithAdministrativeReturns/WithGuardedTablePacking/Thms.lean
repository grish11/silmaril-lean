module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Denotation.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.Soundness

/-! # Inclusion, the packing equation, and coherent soundness -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking

open Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (packedReadbackRep)
open Paper.Extension.Singleton (ofRegion SeedDenotes homRel)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w u₁ u₂ v₁ v₂
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

/-- Include the administrative-return quotient at the same singleton types
and representatives. -/
@[expose] def fromAdministrativeReturns :
    WithAdministrativeReturns.TypeCategory (τ := τ) (Φ := Φ) pe ⥤ TypeCategory (τ := τ) (Φ := Φ) pe :=
  CategoryTheory.Quotient.lift (homRel (WithAdministrativeReturns.Step pe)) (projection pe) <| by
    rintro _ _ _ _ ⟨r, s, hr, hs, hf, hg, eqv⟩
    exact CategoryTheory.Quotient.sound _ ⟨r, s, hr, hs, hf, hg, eqv.mapSeed Or.inl⟩

theorem fromAdministrativeReturns_map_ofRegion {X Y : τ} {r : Region Φ}
    (hr : ValueBranches [X] r [Y]) :
    (fromAdministrativeReturns pe).map (ofRegion (WithAdministrativeReturns.Step pe) hr) =
      ofRegion (Step pe) hr :=
  rfl

theorem projection_comp_fromAdministrativeReturns :
    WithAdministrativeReturns.projection (τ := τ) (Φ := Φ) pe ⋙ fromAdministrativeReturns pe =
      projection pe :=
  CategoryTheory.Quotient.lift_spec _ _ _

theorem ofAdministrativeReturns (h : WithAdministrativeReturns.Eqv pe Γ r s L) : Eqv pe Γ r s L :=
  h.mapSeed Or.inl

/-- The added equation at the written table and its packed representative. -/
theorem pack {n : Nat} (R : Fin (n + 1) → τ) {X D : τ} {e : Region Φ}
    {blocks : Fin (n + 1) → Region Φ} (he : ValueBranches [X] e (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D])) :
    Eqv pe [X] (.cfg e (n + 1) blocks) (packedReadbackRep R he hb).val [D] :=
  .extra (ValueBranches.cfg R he hb).hasType (packedReadbackRep R he hb).property.hasType
    (.inr (.table R he hb))

/-- The two literal arrows are equal in the quotient category. -/
theorem ofRegion_pack {n : Nat} (R : Fin (n + 1) → τ) {X D : τ} {e : Region Φ}
    {blocks : Fin (n + 1) → Region Φ} (he : ValueBranches [X] e (List.ofFn R ++ [D]))
    (hb : ∀ i, ValueBranches [R i, X] (blocks i) (List.ofFn R ++ [D])) :
    ofRegion (Step pe) (ValueBranches.cfg R he hb) =
      ofRegion (Step pe) (packedReadbackRep R he hb).property :=
  (Paper.Extension.Singleton.ofRegion_eq_iff (Step pe) _ _).2 (pack pe R he hb)

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
/-- The packing seed is sound by the pure state transport of the captured
table. The inherited seeds keep their proofs. -/
theorem seedDenotes : SeedDenotes (Seed := Step (τ := τ) (Φ := Φ) pe) J M :=
  fun h hr hs => h.elim (fun e => WithAdministrativeReturns.seedDenotes pe J M shared e hr hs)
    (fun e => Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.pack_denotes
      J M shared e hr hs)

include shared in
theorem Eqv.sound (e : Eqv pe Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  Paper.Extension.Eqv.sound J M shared (seedDenotes pe J M shared) e hr hs

/-- Interpret the quotient with the existing coherent Paper laws. -/
@[expose] noncomputable def denoteFunctor : TypeCategory (τ := τ) (Φ := Φ) pe ⥤ C :=
  Paper.Extension.Singleton.denoteFunctor J M shared (seedDenotes pe J M shared)

/-- The administrative-return quotient and this quotient interpret each
inherited arrow identically. -/
theorem fromAdministrativeReturns_comp_denoteFunctor :
    fromAdministrativeReturns (τ := τ) (Φ := Φ) pe ⋙ denoteFunctor pe J M shared =
      WithAdministrativeReturns.denoteFunctor pe J M shared := by
  apply CategoryTheory.Quotient.lift_unique'
  rw [← Functor.assoc, projection_comp_fromAdministrativeReturns]
  exact (Paper.Extension.Singleton.projection_comp_denoteFunctor J M shared (seedDenotes pe J M shared)).trans
    (Paper.Extension.Singleton.projection_comp_denoteFunctor J M shared
      (WithAdministrativeReturns.seedDenotes pe J M shared)).symm

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking
