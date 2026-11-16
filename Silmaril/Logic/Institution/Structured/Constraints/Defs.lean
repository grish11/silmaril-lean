module

public import Silmaril.Logic.Institution.Structured.Theories.Liberality
public import Mathlib.CategoryTheory.Yoneda

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace Silmaril.Logic.Institution.Structured.Constraints
open CategoryTheory Silmaril.Logic.Institution
universe u v w x

/-- A model is the free extension of its own reduct when every map out of its
reduct lifts uniquely. This is the universal-arrow formulation and needs no
chosen global left adjoint. -/
def FreeAt {C : Type u} [Category.{v} C] {D : Type w} [Category.{x} D]
    (R : C ⥤ D) (M : C) : Prop :=
  ∀ N : C, Function.Bijective (fun f : M ⟶ N => R.map f)

/-- The pointwise universal condition is exactly the paper's invertible-counit
condition whenever a left adjoint has been chosen (Definition 4.14). -/
theorem freeAt_iff_counit_isIso {C : Type u} [Category.{v} C]
    {D : Type w} [Category.{x} D] {L : D ⥤ C} {R : C ⥤ D}
    (adj : L ⊣ R) (M : C) : FreeAt R M ↔ IsIso (adj.counit.app M) := by
  rw [isIso_iff_coyoneda_map_bijective]
  have hmap (N : C) : (fun f : M ⟶ N => R.map f) =
      (adj.homEquiv (R.obj M) N) ∘ (fun f : M ⟶ N => adj.counit.app M ≫ f) := by
    funext f
    simp only [Function.comp_apply, Adjunction.homEquiv_unit, Functor.map_comp,
      ← Category.assoc, adj.right_triangle_components, Category.id_comp]
  constructor
  · intro h N
    change Function.Bijective (fun f : M ⟶ N => adj.counit.app M ≫ f)
    have heq : (fun f : M ⟶ N => adj.counit.app M ≫ f) =
        (adj.homEquiv (R.obj M) N).symm ∘ (fun f : M ⟶ N => R.map f) := by
      funext f
      apply (adj.homEquiv (R.obj M) N).injective
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using (congrFun (hmap N) f).symm
    rw [heq]
    exact (adj.homEquiv (R.obj M) N).symm.bijective.comp (h N)
  · intro h N
    rw [hmap]
    exact (adj.homEquiv (R.obj M) N).bijective.comp (h N)

/-- When the reduct context has a unique map to every reduced model, free
extension is exactly initial-model semantics (the unparameterized-module
special case discussed after Definition 4.14). -/
theorem freeAt_iff_initial {C : Type u} [Category.{v} C]
    {D : Type w} [Category.{x} D] (R : C ⥤ D) (M : C)
    (hUnique : ∀ N : C, Unique (R.obj M ⟶ R.obj N)) :
    FreeAt R M ↔ Nonempty (CategoryTheory.Limits.IsInitial M) := by
  classical
  constructor
  · intro h
    refine ⟨CategoryTheory.Limits.IsInitial.ofUniqueHom
      (fun N => Classical.choose ((h N).2 (hUnique N).default)) ?_⟩
    intro N f
    apply (h N).1
    exact (hUnique N).uniq _ |>.trans ((hUnique N).uniq _).symm
  · rintro ⟨hM⟩ N
    constructor
    · intro f g _
      exact hM.hom_ext _ _
    · intro f
      exact ⟨hM.to N, (hUnique N).uniq _ |>.trans ((hUnique N).uniq f).symm⟩

end Silmaril.Logic.Institution.Structured.Constraints
