module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Unit.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTripling

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTriplingProjection

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory.ComponentTripling
open Paper.Extension.Singleton
open Paper.TypeCategory (sumIso iterate_roll)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
    (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "P" => Paper.TypeCategory (τ := τ) Φ
local notation "Q" => TypeCategory Seed
local notation "J" => projection Seed
local notation "U" => (Silmaril.unit : τ)
local notation "Bit" => Silmaril.coprod U U
local notation "I" => Paper.TypeCategory.iterate

set_option backward.isDefEq.respectTransparency false

theorem project_batch {A B : P} (g h : A ⟶ B ⨿ A) :
    projectStep Seed (thenOnRepeat g h) =
      projectStep Seed g ≫ coprod.desc coprod.inl (projectStep Seed h) := by
  let c := PreservesColimitPair.iso (J) B A
  change (J).map (g ≫ coprod.desc coprod.inl h) ≫ c.inv =
    ((J).map g ≫ c.inv) ≫ coprod.desc coprod.inl ((J).map h ≫ c.inv)
  rw [Functor.map_comp, Category.assoc, Category.assoc]
  apply congrArg ((J).map g ≫ ·)
  apply (cancel_epi c.hom).1
  rw [Iso.hom_inv_id_assoc]
  have first : coprod.inl ≫ c.hom = (J).map (coprod.inl : B ⟶ B ⨿ A) :=
    inl_coprodComparison (J) B A
  have second : coprod.inr ≫ c.hom = (J).map (coprod.inr : A ⟶ B ⨿ A) :=
    inr_coprodComparison (J) B A
  apply coprod.hom_ext
  · simp only [coprod.inl_desc, ← Category.assoc]
    rw [first, ← (J).map_comp, coprod.inl_desc, ← first, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  · simp only [coprod.inr_desc, ← Category.assoc]
    rw [second, ← (J).map_comp, coprod.inr_desc]

theorem transport_batch {A D B : P} (e : A ≅ D) (g h : D ⟶ B ⨿ D) :
    thenOnRepeat (transport e g) (transport e h) = transport e (thenOnRepeat g h) := by
  have continuation : coprod.map (𝟙 B) e.inv ≫ coprod.desc coprod.inl (transport e h) =
      coprod.desc coprod.inl h ≫ coprod.map (𝟙 B) e.inv := by
    apply coprod.hom_ext
    · simp
    · simp [transport]
  simp only [transport, Category.assoc]
  rw [show e.hom ≫ h ≫ coprod.map (𝟙 B) e.inv = transport e h from rfl, continuation]

theorem iterate_transport {A D B : P} (e : A ≅ D) (f : D ⟶ B ⨿ D) :
    I (transport e f) = e.hom ≫ I f := by
  rw [transport, iterate_roll, Category.assoc, coprod.map_map, Category.id_comp,
    Iso.inv_hom_id, coprod.map_id_id, Category.comp_id]

theorem triple_step_bit
    (includeUnit : ∀ {Γ L r s}, Paper.WithUnitEta.Step Γ r s L → Seed Γ r s L)
    {B : Q} (g : ofType Seed Bit ⟶ B ⨿ ofType Seed Bit) :
    iterateChosen Seed (ThreeCycle.triple g) = iterateChosen Seed g := by
  obtain ⟨f, hf⟩ := exists_projectStep Seed g
  let e := sumIso (Φ := Φ) U U
  let n := normalize (transport e.symm f)
  let fixed := transport e n
  have native : I (thenOnRepeat fixed (thenOnRepeat fixed fixed)) = I fixed := by
    change I (thenOnRepeat (transport e n) (thenOnRepeat (transport e n) (transport e n))) = _
    rw [transport_batch, transport_batch, iterate_transport, iterate_transport]
    exact congrArg (e.hom ≫ ·)
      (ComponentTripling.iterate_normalize (transport e.symm f))
  let r := resetPayloads (τ := τ) (Φ := Φ)
  let resetExact := e.hom ≫ r ≫ e.inv
  have normalizeExact : fixed = resetExact ≫ f ≫ coprod.map (𝟙 B.as) resetExact := by
    simp only [fixed, n, resetExact, r, normalize, transport, Iso.symm_hom, Iso.symm_inv,
      Category.assoc, coprod.map_map, Category.id_comp]
  have unitId := unit_eta_of_include Seed includeUnit
  let c := PreservesColimitPair.iso (J) (Paper.TypeCategory.ofType U) (Paper.TypeCategory.ofType U)
  have rId : (J).map r = 𝟙 _ := by
    apply (cancel_mono c.inv).mp
    change (J).map (coprod.map Paper.TypeCategory.UnitThreeCycle.reset Paper.TypeCategory.UnitThreeCycle.reset) ≫ c.inv = _
    rw [← coprodComparison_inv_map Seed, unitId, coprod.map_id_id, Category.comp_id, Category.id_comp]
  have exactId : (J).map resetExact = 𝟙 _ := by
    rw [show resetExact = e.hom ≫ r ≫ e.inv from rfl, Functor.map_comp, Functor.map_comp, rId,
      Category.id_comp, ← Functor.map_comp, Iso.hom_inv_id]
    exact (J).map_id _
  have proj : projectStep Seed fixed = g := by
    rw [normalizeExact]
    change (J).map (resetExact ≫ f ≫ coprod.map _ resetExact) ≫ _ = _
    rw [(J).map_comp resetExact, (J).map_comp f, exactId, Category.id_comp, Category.assoc,
      ← coprodComparison_inv_map Seed, exactId, (J).map_id, coprod.map_id_id]
    let comparison := PreservesColimitPair.iso (J) B.as (ofType Seed Bit).as
    exact (congrArg ((J).map f ≫ ·) (Category.comp_id comparison.inv)).trans hf
  have eq := congrArg ((J).map) native
  rw [← iterateChosen_projectStep, ← iterateChosen_projectStep, project_batch, project_batch, proj] at eq
  exact eq

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ComponentTriplingProjection
