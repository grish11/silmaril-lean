module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Transport.Thms

/-! # The raw singleton operations respect the quotient and normalization -/

public section

universe u v w

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBranchBinding

open CategoryTheory
open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.OrderedPairSingleton
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding
open Paper.Extension.Singleton (ofType ofRegion ofRegion_eq_iff)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Seed" => Paper.WithPairReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "G" => ofType (Φ := Φ) Seed

variable {A B C : τ}

theorem normalize_guarded {r : Region Φ} (hr : ValueBranches [A] r [B]) :
    normalizeHom pe (rawClass pe hr.hasType) = ofRegion Seed hr :=
  (ofRegion_eq_iff Seed hr.hasType.bindBranchArguments hr).mpr
    (.paper (.cfgEta (.native hr.bindBranchArguments_equiv.symm)))

theorem normalizeHom_injective : Function.Injective (normalizeHom (Φ := Φ) pe (A := A) (B := B)) := by
  intro f g
  refine Quotient.inductionOn₂ f g (fun r s h => ?_)
  have e := (ofRegion_eq_iff Seed r.property.bindBranchArguments s.property.bindBranchArguments).mp h
  exact Quotient.sound ((bindBranchArguments_eqv_addBinding r.property).trans
    ((ofSeed e).trans (bindBranchArguments_eqv_addBinding s.property).symm))

theorem normalizeHom_surjective : Function.Surjective (normalizeHom (Φ := Φ) pe (A := A) (B := B)) := by
  intro f
  induction f using Quot.ind with
  | _ f =>
    obtain ⟨r, hr, rfl⟩ := Paper.TypeCategory.exists_ofRegion (τ := τ) (Φ := Φ) (A := A) (B := B) f
    exact ⟨rawClass pe hr.hasType, normalize_guarded pe hr⟩

private theorem constantValues {r : Region Φ} (hr : ValueBranches [A] r [B]) :
    LSubst.ValueFamily [] [A] [B] (fun _ => r) :=
  fun _ _ h => (List.mem_singleton.mp (List.mem_of_getElem? h)).symm ▸ hr

theorem ofRegion_bind_compRep (Step : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
    (r : Rep (Φ := Φ) A B) (s : Rep (Φ := Φ) B C) :
    ofRegion Step (composeRep r s).property.bindBranchArguments =
      ofRegion Step r.property.bindBranchArguments ≫ ofRegion Step s.property.bindBranchArguments := by
  have post := (singletonContinuation_typed s.property).liftVars A
  have comp := r.property.bindBranchArguments.normalize_lsubst post
  rw [bindBranchArguments_liftLSubstVars] at comp
  have guarded := r.property.bindBranchArguments.lsubst
    ((constantValues s.property.bindBranchArguments).liftVars A)
  rw [← CategoryTheory.Functor.map_comp, Paper.TypeCategory.ofRegion_comp _ _ guarded]
  exact (ofRegion_eq_iff Step (composeRep r s).property.bindBranchArguments guarded).mpr
    (.paper (.cfgEta (.native comp)))

theorem normalize_compRep (r : Rep (Φ := Φ) A B) (s : Rep (Φ := Φ) B C) :
    normalizeHom pe (Quotient.mk _ (composeRep r s)) =
      normalizeHom pe (Quotient.mk _ r) ≫ normalizeHom pe (Quotient.mk _ s) :=
  ofRegion_bind_compRep Seed r s

@[simp] theorem normalize_identity :
    normalizeHom pe (identity (Φ := Φ) pe A) = 𝟙 (G A) := by
  rw [identity, normalize_guarded pe (.br (ℓ := 0) rfl (.var (i := 0) rfl))]
  change (Paper.Extension.Singleton.projection Seed).map (Paper.TypeCategory.ofRegion (.br (ℓ := 0) rfl (.var (i := 0) rfl))) = _
  rw [Paper.TypeCategory.ofRegion_id, CategoryTheory.Functor.map_id]

theorem composeRep_respects {r r' : Rep (Φ := Φ) A B} {s s' : Rep (Φ := Φ) B C}
    (hr : (rawSetoid pe A B).r r r') (hs : (rawSetoid pe B C).r s s') :
    (rawSetoid pe A C).r (composeRep r s) (composeRep r' s') :=
  Quotient.exact (normalizeHom_injective pe (by
    rw [normalize_compRep, normalize_compRep, congrArg (normalizeHom pe) (Quotient.sound hr),
      congrArg (normalizeHom pe) (Quotient.sound hs)]))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.OrderedPairBranchBinding
