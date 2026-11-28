module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Branch.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Traversal.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BranchNormalization.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Guarded.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Substitution.Thms

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.BranchReplay

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.BranchReplay
open WithEntryLet (Site)
open Silmaril.DeBruijn (lift)

variable {Φ : Type v}

theorem bindAt_substVars (site : Site) (r : Region Φ) (θ : Nat → Tm Φ) :
    bindAt site (r.substVars θ) = (bindAt site r).map (·.substVars θ) :=
  Site.rewriteAt_substVars bindRoot (fun r θ => by cases r <;> rfl) site r θ

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

private theorem bindRoot_exact {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    (branch : ∀ {Γ L i A a}, At L i A → Tm.HasType Γ a A →
      Extension.Eqv Seed Γ (.br i a) (.let₁ a (.br i (.var 0))) L)
    (hr : HasType Γ r L) (hm : bindRoot r = some s) :
    HasType Γ s L ∧ Extension.Eqv Seed Γ r s L := by
  cases hr with
  | br hi ha =>
    simp only [bindRoot, Option.some.injEq] at hm
    subst s
    exact ⟨.let₁ ha (.br hi (.var rfl)), branch hi ha⟩
  | _ => simp [bindRoot] at hm

theorem bindAt_pullback (site : Site) (hr : HasType Γ r L) (θ : Nat → Tm Φ)
    (hm : bindAt site (r.substVars θ) = some s) :
    ∃ q, bindAt site r = some q ∧ s = q.substVars θ ∧
      HasType Γ q L ∧ WithBoundEntryEta.Eqv Γ r q L := by
  rw [bindAt_substVars] at hm
  obtain ⟨q, he, rfl⟩ := Option.map_eq_some_iff.mp hm
  exact ⟨q, he, rfl, Site.rewriteAt_exact bindRoot
    (bindRoot_exact (fun hi ha => WithBoundEntryEta.bindBranch hi ha)) site hr he⟩

theorem bindAt_normalized (site : Site) (hr : HasType Γ r L) (hm : bindAt site r = some s) :
    Paper.Eqv Γ r.bindBranchArguments s.bindBranchArguments L := by
  let Branch := WithProjectionReturnsAndUnitEta.WithBranchBinding.BindStep (τ := τ) (Φ := Φ)
  let EmptySeed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop := fun _ _ _ _ => False
  have bind : ∀ {Δ K i A a}, At K i A → Tm.HasType Δ a A →
      Extension.Eqv Branch Δ (.br i a) (.let₁ a (.br i (.var 0))) K :=
    fun hi ha => .extra (.br hi ha) (.let₁ ha (.br hi (.var rfl))) (.bind hi ha)
  have corrected := (Site.rewriteAt_exact bindRoot (bindRoot_exact bind) site hr hm).2
  apply Extension.Eqv.toPaper (Seed := EmptySeed) (fun h => False.elim h)
  apply corrected.bindBranchArguments_into
  intro Δ p q K h
  cases h with
  | bind hi ha =>
    exact .paper (.let₁ ha (.cfgEta (.native
      (ValueBranches.bindBranchArguments_equiv (.br hi (.var rfl))))))

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory (ofType ofRegion sumIso)

variable {A D B : τ} {a : Tm Φ}

local notation "Obj" => ofType (τ := τ) (Φ := Φ)

/-- The exact addressed equation disappears on standard Paper representatives
obtained by binding every branch argument. -/
theorem repairNormalizedTarget (site : Site) (ha : Tm.BranchValue [A] a D)
    (hr : HasType [D] r [Silmaril.coprod B D])
    (f : Obj A ⟶ Obj B ⨿ Obj A)
    (hs : HasType [A] s [Silmaril.coprod B D])
    (hm : bindAt site (r.substVars (Tm.singleSubst a ∘ lift Nat.succ)) = some s)
    (comm : f ≫ coprod.map (𝟙 (Obj B)) (ofRegion (.br (ℓ := 0) rfl ha)) =
      ofRegion hs.bindBranchArguments ≫ (sumIso B D).hom) :
    let h := ofRegion (.br (ℓ := 0) rfl ha)
    f ≫ coprod.map (𝟙 (Obj B)) h =
      h ≫ ofRegion hr.bindBranchArguments ≫ (sumIso B D).hom := by
  let θ := Tm.singleSubst a ∘ lift Nat.succ
  have typed : ∀ ⦃i T⦄, At [D] i T → Tm.BranchValue [A] (θ i) T := by
    intro i T hi
    cases i with
    | zero => cases Option.some.inj hi; exact ha
    | succ i => simp [At] at hi
  have composite := hr.bindBranchArguments.substVars typed
  have same := bindAt_normalized site (hr.substVars (fun _ _ hi => (typed hi).hasType)) hm
  rw [bindBranchArguments_substVars] at same
  have e := (Paper.TypeCategory.ofRegion_eq_iff composite hs.bindBranchArguments).2 same
  dsimp only
  rw [comm, ← Category.assoc, WithEntryLet.ofRegion_comp_constructor ha hr.bindBranchArguments composite, e]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.BranchReplay
