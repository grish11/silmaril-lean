module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Branch.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Normalization.Guarded.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.BranchReplay

/-! # Exact branch pullback and native repair after normalization -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.BranchReplay

open CategoryTheory CategoryTheory.Limits
open Silmaril.DeBruijn (lift)
open WithEntryLet (Site)
open Paper.TypeCategory (ofType ofRegion sumIso iterate)

variable {Φ : Type v}

/-- Value substitution commutes with binding a branch at the same address. -/
theorem bindAt_substVars (site : Site) (r : Region Φ) (θ : Nat → Tm Φ) :
    bindAt site (r.substVars θ) = (bindAt site r).map (·.substVars θ) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.BranchReplay.bindAt_substVars site r θ

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

/-- The same successful address exists in the exactly typed original and
gives a proof using the raw branch-binding equation. -/
theorem bindAt_pullback (site : Site) (hr : HasType Γ r L) (θ : Nat → Tm Φ)
    (hm : bindAt site (r.substVars θ) = some s) :
    ∃ q, bindAt site r = some q ∧ s = q.substVars θ ∧
      HasType Γ q L ∧ WithBoundEntryEta.Eqv Γ r q L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.BranchReplay.bindAt_pullback site hr θ hm

/-- Normalizing the branch arguments makes the addressed equation a
standard Paper equation at the original exact interface. -/
theorem bindAt_normalized (site : Site) (hr : HasType Γ r L) (hm : bindAt site r = some s) :
    Paper.Eqv Γ r.bindBranchArguments s.bindBranchArguments L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.BranchReplay.bindAt_normalized site hr hm

/-- With constructor branch arguments, the addressed move already holds
on the written endpoints in standard Paper. -/
theorem bindAt_guarded (site : Site) (hr : ValueBranches Γ r L) (hs : ValueBranches Γ s L)
    (hm : bindAt site r = some s) : Paper.Eqv Γ r s L :=
  (Paper.Eqv.cfgEta (.native hr.bindBranchArguments_equiv)).trans
    ((bindAt_normalized site hr.hasType hm).trans (.cfgEta (.native hs.bindBranchArguments_equiv.symm)))

variable {A D B : τ} {a : Tm Φ}

local notation "Obj" => ofType (τ := τ) (Φ := Φ)

/-- Transport a standard Paper square from the normalized endpoint of the
addressed move to the normalized original target. -/
theorem repairNormalizedTarget (site : Site) (ha : Tm.BranchValue [A] a D)
    (hr : HasType [D] r [Silmaril.coprod B D])
    (f : Obj A ⟶ Obj B ⨿ Obj A)
    (hs : HasType [A] s [Silmaril.coprod B D])
    (hm : bindAt site (r.substVars (Tm.singleSubst a ∘ lift Nat.succ)) = some s)
    (comm : f ≫ coprod.map (𝟙 (Obj B)) (ofRegion (.br (ℓ := 0) rfl ha)) =
      ofRegion hs.bindBranchArguments ≫ (sumIso B D).hom) :
    let h := ofRegion (.br (ℓ := 0) rfl ha)
    f ≫ coprod.map (𝟙 (Obj B)) h =
      h ≫ ofRegion hr.bindBranchArguments ≫ (sumIso B D).hom :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.BranchReplay.repairNormalizedTarget
    site ha hr f hs hm comm

/-- The repaired square gives standard Paper uniformity for the normalized
target and the constructor state map. -/
theorem uniformity_of_normalized_target (site : Site) (ha : Tm.BranchValue [A] a D)
    (hr : HasType [D] r [Silmaril.coprod B D])
    (f : Obj A ⟶ Obj B ⨿ Obj A)
    (hs : HasType [A] s [Silmaril.coprod B D])
    (hm : bindAt site (r.substVars (Tm.singleSubst a ∘ lift Nat.succ)) = some s)
    (comm : f ≫ coprod.map (𝟙 (Obj B)) (ofRegion (.br (ℓ := 0) rfl ha)) =
      ofRegion hs.bindBranchArguments ≫ (sumIso B D).hom) :
    iterate f =
      ofRegion (.br (ℓ := 0) rfl ha) ≫ iterate (ofRegion hr.bindBranchArguments ≫ (sumIso B D).hom) :=
  Paper.TypeCategory.iterate_uniformity_ofConstructorReturn ⟨a, ha, rfl⟩ f _
    (repairNormalizedTarget site ha hr f hs hm comm)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.BranchReplay
