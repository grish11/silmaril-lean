module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Replay

/-! # Binary representative repair and native constructor uniformity -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta

open CategoryTheory CategoryTheory.Limits
open Silmaril.DeBruijn (lift)
open WithEntryLet (Site)
open Paper.TypeCategory (ofType ofRegion sumIso)
open Extension.Singleton (projection projectStep iterateChosen)

variable {Φ : Type v}

/-- Both product binders can be weakened through substitution at any address. -/
theorem move₂_substVars (site : Site) (r : Region Φ) (θ : Nat → Tm Φ) :
    move₂ site (r.substVars θ) = (move₂ site r).map (·.substVars θ) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Replay.move₂_substVars site r θ

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]

/-- The existing unary address action pulls back exactly typed regions
in the once-bound η relation, including computed branch arguments. -/
theorem move₁_pullback (site : Site) {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : HasType Γ r L) (θ : Nat → Tm Φ)
    (hm : site.move (r.substVars θ) = some s) :
    ∃ q, site.move r = some q ∧ s = q.substVars θ ∧
      HasType Γ q L ∧ Eqv Γ r q L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Replay.move₁_pullback site hr θ hm

/-- A binary entry move on a substituted region comes from the same address
in the original region, with the original exact interface. -/
theorem move₂_pullback (site : Site) {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : HasType Γ r L) (θ : Nat → Tm Φ)
    (hm : move₂ site (r.substVars θ) = some s) :
    ∃ q, move₂ site r = some q ∧ s = q.substVars θ ∧
      HasType Γ q L ∧ Eqv Γ r q L :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Replay.move₂_pullback site hr θ hm

variable {A D B : τ} {a : Tm Φ} {r s : Region Φ}

local notation "Seed" => Step (τ := τ) (Φ := Φ)
local notation "Obj" => ofType (τ := τ) (Φ := Φ)

/-- Pull a witnessed binary move back across a constructor state map.
If its result closes the square in standard Paper, the replacement target
has the same once-bound η class and commutes in standard Paper. -/
theorem repairTarget (site : Site) (ha : Tm.BranchValue [A] a D)
    (hr : ValueBranches [D] r [Silmaril.coprod B D])
    (f : Obj A ⟶ Obj B ⨿ Obj A)
    (hs : ValueBranches [A] s [Silmaril.coprod B D])
    (hm : move₂ site (r.substVars (Tm.singleSubst a ∘ lift Nat.succ)) = some s)
    (comm : f ≫ coprod.map (𝟙 (Obj B)) (ofRegion (.br (ℓ := 0) rfl ha)) =
      ofRegion hs ≫ (sumIso B D).hom) :
    let h := ofRegion (.br (ℓ := 0) rfl ha)
    ∃ g : Obj D ⟶ Obj B ⨿ Obj D,
      projectStep Seed g = projectStep Seed (ofRegion hr ≫ (sumIso B D).hom) ∧
      f ≫ coprod.map (𝟙 (Obj B)) h = h ≫ g :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.Replay.repairTarget site ha hr f hs hm comm

/-- Standard Paper constructor uniformity applies to the repaired square. -/
theorem uniformity_of_target_move₂ (site : Site) (ha : Tm.BranchValue [A] a D)
    (hr : ValueBranches [D] r [Silmaril.coprod B D])
    (f : Obj A ⟶ Obj B ⨿ Obj A)
    (hs : ValueBranches [A] s [Silmaril.coprod B D])
    (hm : move₂ site (r.substVars (Tm.singleSubst a ∘ lift Nat.succ)) = some s)
    (comm : f ≫ coprod.map (𝟙 (Obj B)) (ofRegion (.br (ℓ := 0) rfl ha)) =
      ofRegion hs ≫ (sumIso B D).hom) :
    iterateChosen Seed (projectStep Seed f) =
      (projection Seed).map (ofRegion (.br (ℓ := 0) rfl ha)) ≫
        iterateChosen Seed (projectStep Seed (ofRegion hr ≫ (sumIso B D).hom)) := by
  obtain ⟨g, hg, native⟩ := repairTarget site ha hr f hs hm comm
  rw [← hg]
  exact Extension.Singleton.uniformity_of_constructor_square Seed ⟨a, ha, rfl⟩ f g native

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta
