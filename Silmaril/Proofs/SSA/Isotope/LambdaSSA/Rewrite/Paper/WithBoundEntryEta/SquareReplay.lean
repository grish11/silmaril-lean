module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Case.Inverse.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Script.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Thms

/-! # Source scripts and certified target inverses in one square -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.SquareReplay

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper
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

private theorem project_map {X Y : Paper.TypeCategory (τ := τ) Φ} {f g : X ⟶ Y ⨿ X}
    (h : (projection Seed).map f = (projection Seed).map g) :
    projectStep Seed f = projectStep Seed g := by
  unfold projectStep
  rw [h]

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
      f' ≫ coprod.map (𝟙 (Obj B)) h = h ≫ g' := by
  obtain ⟨q, hq, rfl, _, eq⟩ := inverse_pullback table _ step
  let hguard := guard q hq
  refine ⟨ofRegion hguard ≫ (sumIso B D).hom, project_map ?_, project_map ?_, ?_⟩
  · have same := (Paper.Extension.Singleton.ofRegion_eq_iff Seed hs hs').2 trace.eqv
    simp only [Functor.map_comp]
    exact congrArg (fun k => (projection Seed).map pre ≫ k ≫ (projection Seed).map post) same.symm
  · have same := (Paper.Extension.Singleton.ofRegion_eq_iff Seed ht hguard).2 eq
    simp only [Functor.map_comp]
    exact congrArg (fun k => k ≫ (projection Seed).map (sumIso B D).hom) same.symm
  · rwa [← Category.assoc (ofRegion (.br (ℓ := 0) rfl ha)) (ofRegion hguard),
      WithEntryLet.ofRegion_comp_constructor ha hguard hp]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.SquareReplay
