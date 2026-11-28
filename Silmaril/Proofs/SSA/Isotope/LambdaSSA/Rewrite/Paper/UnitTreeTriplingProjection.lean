module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.UnitTree.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitTreeTripling

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitTreeTriplingProjection

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory.ComponentTripling
open Paper.Extension.Singleton
open Paper.Extension.Singleton.ThreeCycle (projectStep_thenOnRepeat)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
    (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "P" => Paper.TypeCategory (τ := τ) Φ
local notation "Q" => TypeCategory Seed
local notation "J" => projection Seed
local notation "I" => Paper.TypeCategory.iterate

set_option backward.isDefEq.respectTransparency false

private theorem reset_projects_id
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L)
    (t : UnitTree) : (J).map (t.reset (τ := τ) (Φ := Φ)) = 𝟙 _ := by
  induction t with
  | empty => exact (J).map_id _
  | unit => exact unit_eta_of_include Seed includeUnit
  | sum l r hl hr =>
    let c := PreservesColimitPair.iso (J) l.obj r.obj
    apply (cancel_mono c.inv).mp
    change (J).map (coprod.map l.reset r.reset) ≫ c.inv = _
    rw [← coprodComparison_inv_map Seed, hl, hr, coprod.map_id_id, Category.comp_id, Category.id_comp]

theorem triple_step_unit_tree
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L)
    (t : UnitTree) {B : Q} (g : ofType Seed t.ty ⟶ B ⨿ ofType Seed t.ty) :
    iterateChosen Seed (ThreeCycle.triple g) = iterateChosen Seed g := by
  obtain ⟨f, hf⟩ := exists_projectStep Seed g
  let e := t.syntaxIso (τ := τ) (Φ := Φ)
  let n := t.normalize (transport e.symm f)
  let fixed := transport e n
  have native : I (thenOnRepeat fixed (thenOnRepeat fixed fixed)) = I fixed := by
    change I (thenOnRepeat (transport e n) (thenOnRepeat (transport e n) (transport e n))) = _
    rw [transport_thenOnRepeat, transport_thenOnRepeat, iterate_transport, iterate_transport]
    exact congrArg (e.hom ≫ ·) (UnitTreeTripling.iterate_normalize t (transport e.symm f))
  let r := t.reset (τ := τ) (Φ := Φ)
  let resetExact := e.hom ≫ r ≫ e.inv
  have normalizeExact : fixed = resetExact ≫ f ≫ coprod.map (𝟙 B.as) resetExact := by
    simp only [fixed, n, resetExact, r, UnitTree.normalize, transport, Iso.symm_hom, Iso.symm_inv,
      Category.assoc, coprod.map_map, Category.id_comp]
  have rId : (J).map r = 𝟙 _ := reset_projects_id Seed includeUnit t
  have exactId : (J).map resetExact = 𝟙 _ := by
    rw [show resetExact = e.hom ≫ r ≫ e.inv from rfl, Functor.map_comp, Functor.map_comp, rId,
      Category.id_comp, ← Functor.map_comp, Iso.hom_inv_id]
    exact (J).map_id _
  have proj : projectStep Seed fixed = g := by
    rw [normalizeExact]
    change (J).map (resetExact ≫ f ≫ coprod.map _ resetExact) ≫ _ = _
    rw [(J).map_comp resetExact, (J).map_comp f, exactId, Category.id_comp, Category.assoc,
      ← coprodComparison_inv_map Seed, exactId, (J).map_id, coprod.map_id_id]
    let comparison := PreservesColimitPair.iso (J) B.as (ofType Seed t.ty).as
    exact (congrArg ((J).map f ≫ ·) (Category.comp_id comparison.inv)).trans hf
  have eq := congrArg ((J).map) native
  rw [← iterateChosen_projectStep, ← iterateChosen_projectStep,
    projectStep_thenOnRepeat, projectStep_thenOnRepeat, proj] at eq
  exact eq

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.UnitTreeTriplingProjection
