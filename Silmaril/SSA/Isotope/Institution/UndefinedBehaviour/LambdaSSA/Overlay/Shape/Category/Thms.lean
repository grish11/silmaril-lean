module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Defs
public import Mathlib.CategoryTheory.Functor.Basic
import Silmaril.Proofs.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Laws

/-! # Category of shaped stateful observations -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category

universe v w x

variable {α : Type w} {σ : Type x} {κ : Type v} {atomType : α → κ → Prop}
  {X Y : Interface α σ atomType}

open CategoryTheory

noncomputable instance : Category (Interface α σ atomType) where
  Hom := Arrow
  id X := ⟨fun i a s => ↑({Outcome.ret i a.val s} : Set (Outcome X.labels.length α σ)),
    by exact Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.id_typed⟩
  comp f g := ⟨fun i a s => (f.run i a s).bind g.total,
    by exact Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.comp_typed f g⟩
  id_comp := by exact Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.identity_compose
  comp_id := by exact Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.compose_identity
  assoc := by exact Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.compose_assoc

theorem arrow_ext {f g : Arrow X Y} (h : ∀ i a s, f.run i a s = g.run i a s) : f = g :=
  Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.Category.arrow_ext h

@[simp] theorem id_run (i : Fin X.labels.length) (a : X.Payload i) (s : σ) :
    (𝟙 X : Arrow X X).run i a s = ↑({Outcome.ret i a.val s} : Set (Outcome X.labels.length α σ)) :=
  rfl

theorem comp_run {Z : Interface α σ atomType} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : Fin X.labels.length) (a : X.Payload i) (s : σ) :
    (f ≫ g : Arrow X Z).run i a s = ((f : Arrow X Y).run i a s).bind (g : Arrow Y Z).total :=
  rfl

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
