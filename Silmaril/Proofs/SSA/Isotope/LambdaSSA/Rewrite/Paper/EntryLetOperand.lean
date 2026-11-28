module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Traversal.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Substitution.Thms

/-! # Pulling an entry-let move back along a constructor substitution -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetOperand

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet (Site Step)
open Silmaril.DeBruijn (lift)

variable {Φ : Type v}

private theorem moveEntry_subst (r : Region Φ) (θ : Nat → Tm Φ) :
    Site.moveEntry (r.substVars θ) = (Site.moveEntry r).map (·.substVars θ) := by
  cases r with
  | cfg body n bs =>
    cases body <;> simp [Site.moveEntry, Region.substVars, substVars_renameVars,
      renameVars_substVars, Tm.liftSubst_comp_lift_succ]
  | _ => rfl

theorem move_substVars (site : Site) (r : Region Φ) (θ : Nat → Tm Φ) :
    site.move (r.substVars θ) = (site.move r).map (·.substVars θ) :=
  Site.rewriteAt_substVars Site.moveEntry moveEntry_subst site r θ

variable {τ : Type u} [TypeFormers τ] [HasTy Φ τ]

private theorem moveEntry_sound {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches Γ r L) (hm : Site.moveEntry r = some s) :
    ValueBranches Γ s L ∧ Paper.WithEntryLet.Eqv Γ r s L := by
  cases hr with
  | cfg R he hb =>
    cases he with
    | let₁ ha hd =>
      simp only [Site.moveEntry, Option.some.injEq] at hm
      subst s
      have hs := ValueBranches.let₁ ha (.cfg R hd
        (fun i => (hb i).renameVars ((Ren.wk _ _).lift (R i))))
      exact ⟨hs, .extra (ValueBranches.cfg R (.let₁ ha hd) hb).hasType hs.hasType (.seq R ha hd hb)⟩
    | _ => simp [Site.moveEntry] at hm
  | _ => simp [Site.moveEntry] at hm

theorem move_sound (site : Site) {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches Γ r L) (hm : site.move r = some s) :
    ValueBranches Γ s L ∧ Paper.WithEntryLet.Eqv Γ r s L :=
  Site.rewriteAt_guarded Site.moveEntry moveEntry_sound site hr hm

theorem move_pullback (site : Site) {Γ : VCtx τ} {L : LCtx τ}
    {r s : Region Φ} (hr : ValueBranches Γ r L) (θ : Nat → Tm Φ)
    (hm : site.move (r.substVars θ) = some s) :
    ∃ q, site.move r = some q ∧ s = q.substVars θ ∧
      ValueBranches Γ q L ∧ Paper.WithEntryLet.Eqv Γ r q L := by
  rw [move_substVars] at hm
  obtain ⟨q, he, rfl⟩ := Option.map_eq_some_iff.mp hm
  exact ⟨q, he, rfl, move_sound site hr he⟩


theorem moveAll_pullback (sites : List Site) {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}
    (hr : ValueBranches Γ r L) (θ : Nat → Tm Φ)
    (hm : Site.moveAll sites (r.substVars θ) = some s) :
    ∃ q, Site.moveAll sites r = some q ∧ s = q.substVars θ ∧
      ValueBranches Γ q L ∧ Paper.WithEntryLet.Eqv Γ r q L := by
  induction sites generalizing r s with
  | nil =>
    change some (r.substVars θ) = some s at hm
    exact ⟨r, rfl, (Option.some.inj hm).symm, hr, .paper (.refl hr.hasType)⟩
  | cons site sites ih =>
    cases he : site.move (r.substVars θ) with
    | none => simp [Site.moveAll, List.foldlM, he] at hm
    | some next =>
      obtain ⟨q, hq, hnext, htyped, eq⟩ := move_pullback site hr θ he
      have hrest : Site.moveAll sites (q.substVars θ) = some s := by
        change (site.move (r.substVars θ) >>= Site.moveAll sites) = some s at hm
        rw [he] at hm
        change Site.moveAll sites next = some s at hm
        rwa [hnext] at hm
      obtain ⟨out, hout, heq, ht, erest⟩ := ih htyped hrest
      refine ⟨out, ?_, heq, ht, .trans eq erest⟩
      change (site.move r >>= Site.moveAll sites) = some out
      rw [hq]
      exact hout

theorem move_letValue (site : Site) {Γ : VCtx τ} {L : LCtx τ} {T : τ}
    {a : Tm Φ} {body moved : Region Φ} (ha : Tm.BranchValue Γ a T)
    (hm : site.move body = some moved) (ht : HasType (T :: Γ) moved L) :
    site.move (body.substVars (Tm.singleSubst a)) = some (moved.substVars (Tm.singleSubst a)) ∧
      Paper.Eqv Γ (.let₁ a moved) (moved.substVars (Tm.singleSubst a)) L := by
  refine ⟨?_, .cfgEta (.native (.letValue ha ht))⟩
  rw [move_substVars, hm]
  rfl

theorem move_under_letValue (site : Site) {Γ : VCtx τ} {L : LCtx τ} {T : τ}
    {a : Tm Φ} {body s : Region Φ} (ha : Tm.BranchValue Γ a T)
    (hb : ValueBranches (T :: Γ) body L)
    (hm : (Site.unaryBody site).move (.let₁ a body) = some s) :
    ∃ q, site.move (body.substVars (Tm.singleSubst a)) = some q ∧
      ValueBranches Γ q L ∧ Paper.Eqv Γ s q L := by
  change (site.move body).map (Region.let₁ a) = some s at hm
  obtain ⟨moved, hmoved, rfl⟩ := Option.map_eq_some_iff.mp hm
  have hg := (move_sound site hb hmoved).1
  obtain ⟨he, eq⟩ := move_letValue site ha hmoved hg.hasType
  refine ⟨_, he, hg.substVars ?_, eq⟩
  intro i A hi
  cases i with
  | zero =>
    cases Option.some.inj hi
    exact ha
  | succ i => exact .var hi

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory (ofType ofRegion sumIso)
open Paper.Extension.Singleton (projection projectStep iterateChosen projectSquare_iff)

variable {A D B : τ} {a : Tm Φ} {r s : Region Φ}

local notation "Seed" => Step (τ := τ) (Φ := Φ)
local notation "Obj" => ofType (τ := τ) (Φ := Φ)

theorem comp_constructor {C : τ} {q : Region Φ} (ha : Tm.BranchValue [A] a D)
    (hq : ValueBranches [D] q [C])
    (ht : ValueBranches [A] (q.substVars (Tm.singleSubst a ∘ lift Nat.succ)) [C]) :
    ofRegion (.br (ℓ := 0) rfl ha) ≫ ofRegion hq = ofRegion ht := by
  have e : compLSubst (fun _ => Region.br 0 a) (fun _ => q) 0 =
      q.substVars (Tm.singleSubst a ∘ lift Nat.succ) :=
    substVars_renameVars q (lift Nat.succ) (Tm.singleSubst a)
  have hc : ValueBranches [A] (compLSubst (fun _ => Region.br 0 a) (fun _ => q) 0) [C] :=
    e.symm ▸ ht
  rw [Paper.TypeCategory.ofRegion_comp (.br rfl ha) hq hc]
  apply (Paper.TypeCategory.ofRegion_eq_iff hc ht).2
  rw [e]
  exact .refl ht.hasType

theorem projectSquare_of_native_move (site : Site) {p expanded moved : Region Φ}
    (f : Obj A ⟶ Obj B ⨿ Obj A) (g : Obj D ⟶ Obj B ⨿ Obj D) (h : Obj A ⟶ Obj D)
    (hp : ValueBranches [A] p [Silmaril.coprod B D])
    (he : ValueBranches [A] expanded [Silmaril.coprod B D])
    (expand : Paper.Eqv [A] p expanded [Silmaril.coprod B D])
    (hm : site.move expanded = some moved)
    (sourceEq : f ≫ coprod.map (𝟙 (Obj B)) h =
      ofRegion (move_sound site he hm).1 ≫ (sumIso B D).hom)
    (targetEq : h ≫ g = ofRegion hp ≫ (sumIso B D).hom) :
    projectStep Seed f ≫ coprod.map (𝟙 ((projection Seed).obj (Obj B))) ((projection Seed).map h) =
      (projection Seed).map h ≫ projectStep Seed g := by
  have eq : Paper.WithEntryLet.Eqv [A] p moved [Silmaril.coprod B D] :=
    .trans (.paper expand) (move_sound site he hm).2
  apply (projectSquare_iff Seed f g h).2
  rw [sourceEq, targetEq, Functor.map_comp, Functor.map_comp]
  exact congrArg (· ≫ (projection Seed).map (sumIso B D).hom)
    ((Paper.Extension.Singleton.ofRegion_eq_iff Seed _ _).2 eq).symm

theorem repairTargetMoves (sites : List Site) (ha : Tm.BranchValue [A] a D)
    (hr : ValueBranches [D] r [Silmaril.coprod B D])
    (f : Obj A ⟶ Obj B ⨿ Obj A)
    (hs : ValueBranches [A] s [Silmaril.coprod B D])
    (hm : Site.moveAll sites (r.substVars (Tm.singleSubst a ∘ lift Nat.succ)) = some s)
    (comm : f ≫ coprod.map (𝟙 (Obj B)) (ofRegion (.br (ℓ := 0) rfl ha)) =
      ofRegion hs ≫ (sumIso B D).hom) :
    let h := ofRegion (.br (ℓ := 0) rfl ha)
    ∃ g : Obj D ⟶ Obj B ⨿ Obj D,
      projectStep Seed g = projectStep Seed (ofRegion hr ≫ (sumIso B D).hom) ∧
      f ≫ coprod.map (𝟙 (Obj B)) h = h ≫ g := by
  obtain ⟨q, _, rfl, hq, eq⟩ := moveAll_pullback sites hr _ hm
  refine ⟨ofRegion hq ≫ (sumIso B D).hom, ?_, ?_⟩
  · have ec := (Paper.Extension.Singleton.ofRegion_eq_iff Seed hr hq).2 eq
    unfold projectStep
    simp only [Functor.map_comp]
    exact congrArg (fun k => (k ≫ (projection Seed).map (sumIso B D).hom) ≫ _) ec.symm
  · rwa [← Category.assoc, comp_constructor]

theorem uniformity_of_target_moves (sites : List Site) (ha : Tm.BranchValue [A] a D)
    (hr : ValueBranches [D] r [Silmaril.coprod B D])
    (f : Obj A ⟶ Obj B ⨿ Obj A)
    (hs : ValueBranches [A] s [Silmaril.coprod B D])
    (hm : Site.moveAll sites (r.substVars (Tm.singleSubst a ∘ lift Nat.succ)) = some s)
    (comm : f ≫ coprod.map (𝟙 (Obj B)) (ofRegion (.br (ℓ := 0) rfl ha)) =
      ofRegion hs ≫ (sumIso B D).hom) :
    iterateChosen Seed (projectStep Seed f) =
      (projection Seed).map (ofRegion (.br (ℓ := 0) rfl ha)) ≫
        iterateChosen Seed (projectStep Seed (ofRegion hr ≫ (sumIso B D).hom)) := by
  obtain ⟨g, hg, native⟩ := repairTargetMoves sites ha hr f hs hm comm
  rw [← hg]
  exact Paper.Extension.Singleton.uniformity_of_constructor_square Seed ⟨a, ha, rfl⟩ f g native

theorem repairTargetAfterLetValue (sites : List Site) (site : Site)
    (ha : Tm.BranchValue [A] a D)
    (hr : ValueBranches [D] r [Silmaril.coprod B D])
    (f : Obj A ⟶ Obj B ⨿ Obj A)
    {T : τ} {v : Tm Φ} {body : Region Φ}
    (hv : Tm.BranchValue [A] v T) (hb : ValueBranches [T, A] body [Silmaril.coprod B D])
    (hs : ValueBranches [A] s [Silmaril.coprod B D])
    (prefixMoves : Site.moveAll sites (r.substVars (Tm.singleSubst a ∘ lift Nat.succ)) =
      some (body.substVars (Tm.singleSubst v)))
    (hm : (Site.unaryBody site).move (.let₁ v body) = some s)
    (comm : f ≫ coprod.map (𝟙 (Obj B)) (ofRegion (.br (ℓ := 0) rfl ha)) =
      ofRegion hs ≫ (sumIso B D).hom) :
    let h := ofRegion (.br (ℓ := 0) rfl ha)
    ∃ g : Obj D ⟶ Obj B ⨿ Obj D,
      projectStep Seed g = projectStep Seed (ofRegion hr ≫ (sumIso B D).hom) ∧
      f ≫ coprod.map (𝟙 (Obj B)) h = h ≫ g := by
  obtain ⟨q, hq, ht, eq⟩ := move_under_letValue site hv hb hm
  apply repairTargetMoves (sites ++ [site]) ha hr f ht
  · simp only [Site.moveAll, List.foldlM_append] at prefixMoves ⊢
    rw [prefixMoves]
    change (site.move (body.substVars (Tm.singleSubst v)) >>= some) = some q
    rw [hq]
    rfl
  · rwa [← (Paper.TypeCategory.ofRegion_eq_iff hs ht).2 eq]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetOperand
