module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Reflection.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Rounds.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Soundness
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Rounds

/-! # Inclusion, soundness and unrolling at every round count

## What is added

`PhaseUniform.fold`, for each `k`: uniformity of guarded feedback along the
fold of `k + 1` phases of a state, for squares that commute in default
Paper. The folds for `k = 1` and `k = 2` are the state maps of the
binary-fold and tripling seeds that the table-packing quotient already
contains. Those seeds have their own square premises.

## What is not added

Unrolling is not a seed. It is derived: default Paper turns `n + 1` rounds
into a cycle of phases (`exists_phaseCycle`), and one use of the seed
closes the cycle. `Valid → Eqv` is not a seed either.

## Status

The seed is sound in every supported model by pure uniformity. Whether its
instances for `k ≥ 3` are derivable in `WithGuardedTablePacking` is not
known: no derivation and no independence witness is given. Default Paper
and `WithGuardedTablePacking` are unchanged.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity

open Paper.Extension.Singleton (ofRegion SeedDenotes homRel)
open Paper.Extension.Singleton.Rounds
open Paper.TypeCategory (ofType iterate phaseType phaseFold)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

universe u v w u₁ u₂ v₁ v₂
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

/-- Include the table-packing quotient at the same types and representatives. -/
@[expose] def fromTablePacking :
    WithGuardedTablePacking.TypeCategory (τ := τ) (Φ := Φ) pe ⥤ TypeCategory (τ := τ) (Φ := Φ) pe :=
  CategoryTheory.Quotient.lift (homRel (WithGuardedTablePacking.Step pe)) (projection pe) <| by
    rintro _ _ _ _ ⟨r, s, hr, hs, hf, hg, eqv⟩
    exact CategoryTheory.Quotient.sound _ ⟨r, s, hr, hs, hf, hg, eqv.mapSeed Or.inl⟩

theorem fromTablePacking_map_ofRegion {X Y : τ} {r : Region Φ} (hr : ValueBranches [X] r [Y]) :
    (fromTablePacking pe).map (ofRegion (WithGuardedTablePacking.Step pe) hr) = ofRegion (Step pe) hr :=
  rfl

theorem ofTablePacking (h : WithGuardedTablePacking.Eqv pe Γ r s L) : Eqv pe Γ r s L :=
  h.mapSeed Or.inl

/-- The added equations in the quotient category. -/
theorem fold_uniform (k : Nat) {A B : τ}
    (f : ofType (Φ := Φ) (phaseType A k) ⟶ ofType B ⨿ ofType (phaseType A k))
    (g : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A)
    (square : f ≫ coprod.map (𝟙 _) (phaseFold A k) = phaseFold A k ≫ g) :
    (projection pe).map (iterate f) = (projection pe).map (phaseFold A k ≫ iterate g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.fold_uniform pe k f g square

/-- Every positive round count unrolls, at every step of the quotient. -/
theorem roundsLaw (n : Nat) : RoundsLaw (Step (τ := τ) (Φ := Φ) pe) n :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.roundsLaw pe n

theorem unrolls (n : Nat) : Unrolls (Step (τ := τ) (Φ := Φ) pe) n :=
  unrolls_of_roundsLaw _ (roundsLaw pe n)

/-- The written loop on `n + 1` rounds of a guarded step equals the written
loop on one round, for every `n`. -/
theorem unrolled_eqv (n : Nat) {A B : τ} {s : Region Φ}
    (hs : ValueBranches [A] s [Silmaril.coprod B A]) :
    Eqv pe [A] (SyntacticCategory.iterateRegion A (roundsRegion s n))
      (SyntacticCategory.iterateRegion A s) [B] :=
  Paper.Extension.Singleton.Rounds.unrolled_eqv _ (unrolls pe n) hs

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
/-- The added seed is sound by pure uniformity of the model along the
denotation of the phase fold. The inherited seeds keep their proofs. -/
theorem seedDenotes : SeedDenotes (Seed := Step (τ := τ) (Φ := Φ) pe) J M :=
  fun h hr hs => h.elim (fun e => WithGuardedTablePacking.seedDenotes pe J M shared e hr hs)
    (fun e => Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.phase_denotes J M shared e hr hs)

include shared in
theorem Eqv.sound (e : Eqv pe Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs :=
  Paper.Extension.Eqv.sound J M shared (seedDenotes pe J M shared) e hr hs

/-- Interpret the quotient with the existing coherent Paper laws. -/
@[expose] noncomputable def denoteFunctor : TypeCategory (τ := τ) (Φ := Φ) pe ⥤ C :=
  Paper.Extension.Singleton.denoteFunctor J M shared (seedDenotes pe J M shared)

/-- Every equation of this quotient is valid in every supported model. -/
theorem valid_of_eqv (e : Eqv pe Γ r s L) (hr : HasType Γ r L) (hs : HasType Γ s L) : Valid hr hs :=
  fun J _ _ M _ _ shared => e.sound pe J M shared hr hs

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity
