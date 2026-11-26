module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Inverse.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Script.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.SquareReplay

/-! # Replay a forward source script and a certified target inverse -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.SquareReplay

open CategoryTheory CategoryTheory.Limits
open Silmaril.DeBruijn (lift)
open Paper.TypeCategory (ofType ofRegion sumIso)
open Paper.Extension.Singleton (projection projectStep)
open WithEntryLet (Site)
open WithBoundEntryEta.CaseReplay
open WithBoundEntryEta.ScriptReplay

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {A B C D E : τ} {a : Tm Φ}

local notation "Seed" => WithBoundEntryEta.Step (τ := τ) (Φ := Φ)
local notation "Obj" => ofType (Φ := Φ)

/-- Replace the source inside its composition frame and pull the witnessed
inverse back to a guarded target representative. The native endpoint
premise identifies only the repaired source composite with the observed
specialization. The target composite follows by constructor substitution. -/
theorem repair {moves : List Move} {source source' target p : Region Φ}
    (hs : ValueBranches [C] source [E]) (hs' : ValueBranches [C] source' [E])
    (trace : Trace [C] [E] moves source source')
    (pre : Obj A ⟶ Obj C) (post : Obj E ⟶ Obj B ⨿ Obj A)
    (ha : Tm.BranchValue [A] a D) (ht : ValueBranches [D] target [Silmaril.coprod B D])
    (site : Site) (table : CommonTableAt [D] [Silmaril.coprod B D] site target)
    (step : hoistAt site p = some (target.substVars (Tm.singleSubst a ∘ lift Nat.succ)))
    (guard : ∀ q, hoistAt site q = some target → ValueBranches [D] q [Silmaril.coprod B D])
    (hp : ValueBranches [A] p [Silmaril.coprod B D])
    (native : (pre ≫ ofRegion hs' ≫ post) ≫ coprod.map (𝟙 (Obj B)) (ofRegion (.br (ℓ := 0) rfl ha)) =
      ofRegion hp ≫ (sumIso B D).hom) :
    let f := pre ≫ ofRegion hs ≫ post
    let f' := pre ≫ ofRegion hs' ≫ post
    let g := ofRegion ht ≫ (sumIso B D).hom
    let h := ofRegion (.br (ℓ := 0) rfl ha)
    ∃ g' : Obj D ⟶ Obj B ⨿ Obj D,
      projectStep Seed f' = projectStep Seed f ∧ projectStep Seed g' = projectStep Seed g ∧
      f' ≫ coprod.map (𝟙 (Obj B)) h = h ≫ g' :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.SquareReplay.repair
    hs hs' trace pre post ha ht site table step guard hp native

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.SquareReplay
