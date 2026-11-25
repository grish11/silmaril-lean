module

public import Silmaril.Semantics.RuntimeWires.Sliced.Interpretation

public section

namespace Silmaril.RuntimeWires.Proofs.Sliced

open CategoryTheory Silmaril.RuntimeWires.Sliced
open scoped MonoidalCategory

universe u v

variable {O : Type u} {S : Signature.{u,v} O} (E : Diagram.Equations S)

local notation "Obj" => (Diagram.Presented.mk (S := S) (E := E))

theorem denote_pass (W : List O) {A B : List O} (r : Row S A B) :
    (Row.pass W r).denote E = (𝟙 (Obj W)) ⊗ₘ r.denote E := by
  induction W with
  | nil =>
    symm
    refine Quotient.inductionOn (r.denote E) fun f => ?_
    exact Quotient.sound (Diagram.Congruence.tensor_unit_left f)
  | cons x W ih =>
    change (𝟙 (Obj [x])) ⊗ₘ (Row.pass W r).denote E =
      (𝟙 (Obj (x :: W))) ⊗ₘ r.denote E
    rw [ih]
    have assoc :
        ((𝟙 (Obj [x])) ⊗ₘ (𝟙 (Obj W))) ⊗ₘ r.denote E =
          (𝟙 (Obj [x])) ⊗ₘ ((𝟙 (Obj W)) ⊗ₘ r.denote E) := by
      refine Quotient.inductionOn (r.denote E) fun f => ?_
      exact Quotient.sound (Diagram.Congruence.tensor_assoc (.id [x]) (.id W) f)
    rw [MonoidalCategory.id_tensorHom_id] at assoc
    exact assoc.symm

theorem denote_straight (W : List O) : (Row.straight (S := S) W).denote E = 𝟙 (Obj W) := by
  induction W with
  | nil => rfl
  | cons x W ih =>
    change (𝟙 (Obj [x])) ⊗ₘ (Row.straight W).denote E = 𝟙 (Obj (x :: W))
    rw [ih]
    exact MonoidalCategory.id_tensorHom_id _ _

private theorem interchange_upper {C : Type*} [Category* C] [MonoidalCategory C]
    {X Y A M B : C} (f : X ⟶ Y) (p : A ⟶ M) (q : M ⟶ B) :
    f ⊗ₘ (p ≫ q) = (f ⊗ₘ p) ≫ ((𝟙 Y) ⊗ₘ q) :=
  (congrArg (· ⊗ₘ (p ≫ q)) (Category.comp_id f).symm).trans
    (MonoidalCategory.tensorHom_comp_tensorHom f p (𝟙 Y) q).symm

private theorem interchange_lower {C : Type*} [Category* C] [MonoidalCategory C]
    {X Y A M B : C} (f : X ⟶ Y) (p : A ⟶ M) (q : M ⟶ B) :
    f ⊗ₘ (p ≫ q) = ((𝟙 X) ⊗ₘ p) ≫ (f ⊗ₘ q) :=
  (congrArg (· ⊗ₘ (p ≫ q)) (Category.id_comp f).symm).trans
    (MonoidalCategory.tensorHom_comp_tensorHom (𝟙 X) p f q).symm

theorem denote_split {A M B : List O} {r : Row S A B} {p : Row S A M} {q : Row S M B}
    (h : Row.Split S r p q) : r.denote E = p.denote E ≫ q.denote E := by
  induction h with
  | empty => exact (Category.id_comp _).symm
  | @wire x _ _ _ _ p q h ih =>
    simp only [Row.denote, ih]
    exact interchange_lower (𝟙 (Obj [x])) (p.denote E) (q.denote E)
  | @upper e _ _ _ _ p q h ih =>
    simp only [Row.denote, denote_pass, ih]
    exact interchange_upper (Diagram.Presented.ofTerm (A := Obj (S.source e))
      (B := Obj (S.target e)) (.gen e)) (p.denote E) (q.denote E)
  | @lower e _ _ _ _ p q h ih =>
    simp only [Row.denote, denote_pass, ih]
    exact interchange_lower (Diagram.Presented.ofTerm (A := Obj (S.source e))
      (B := Obj (S.target e)) (.gen e)) (p.denote E) (q.denote E)

theorem denote_move {A B : List O} {p q : Sheet S A B} (h : Sheet.Move S p q) :
    p.denote E = q.denote E := by
  induction h with
  | split h tail =>
    simp only [Sheet.denote, denote_split E h, Category.assoc]
  | straight tail =>
    simp only [Sheet.denote, denote_straight, Category.id_comp]
  | under r h ih =>
    simp only [Sheet.denote, ih]

theorem denote_seam {A B : List O} {p q : Sheet S A B} (h : Sheet.SeamEquivalent p q) :
    p.denote E = q.denote E := by
  induction h with
  | rel _ _ h => exact denote_move E h
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end Silmaril.RuntimeWires.Proofs.Sliced
