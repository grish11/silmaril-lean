module

public import Silmaril.Semantics.RuntimeWires.Nullary.Defs

public section

namespace Silmaril.RuntimeWires.Nullary.Proofs

open Silmaril.RuntimeWires
open Silmaril.RuntimeWires.Presentation
open CategoryTheory

abbrev Term := Diagram (signature signatureWithScalar)
abbrev Equation : Diagram.Equations (signature signatureWithScalar) := fun f g =>
  Diagram.Congruence (Relations signatureWithScalar) f g

private def each : (A : List (Wire signatureWithScalar.Obj)) → Term A A
  | [] => .id []
  | none :: A => .tensor generator (each A)
  | some x :: _ => x.elim

private theorem each_append (A B : List (Wire signatureWithScalar.Obj)) :
    Equation (each (A ++ B)) (.tensor (each A) (each B)) := by
  induction A with
  | nil => exact (Diagram.Congruence.tensor_unit_left (each B)).symm
  | cons a A ih =>
    cases a with
    | none =>
      exact (Diagram.Congruence.tensor (.refl generator) ih).trans
        (Diagram.Congruence.tensor_assoc generator (each A) (each B)).symm
    | some x => exact x.elim

private theorem each_commutes {A B : List (Wire signatureWithScalar.Obj)} (f : Term A B) :
    Equation (.comp (each A) f) (.comp f (each B)) := by
  induction f with
  | id A => exact (Diagram.Congruence.comp_id (each A)).trans (Diagram.Congruence.id_comp (each A)).symm
  | gen e =>
    cases e with
    | pure x => exact x.elim
    | moveLeft x => exact x.elim
    | moveRight x => exact x.elim
    | effect x =>
      cases x
      have h : Equation (each [none]) generator := .tensor_unit_right generator
      exact (Diagram.Congruence.comp h (.refl generator)).trans (.comp (.refl generator) h.symm)
  | comp f g ihf ihg =>
    exact (Diagram.Congruence.comp_assoc _ f g).symm.trans
      ((Diagram.Congruence.comp ihf (.refl g)).trans
        ((Diagram.Congruence.comp_assoc f _ g).trans
          ((Diagram.Congruence.comp (.refl f) ihg).trans (Diagram.Congruence.comp_assoc f g _).symm)))
  | @tensor A B C D f g ihf ihg =>
    exact (Diagram.Congruence.comp (each_append A C) (.refl _)).trans
      ((Diagram.Congruence.tensor_comp _ f _ g).symm.trans
        ((Diagram.Congruence.tensor ihf ihg).trans
          ((Diagram.Congruence.tensor_comp f _ g _).trans (.comp (.refl _) (each_append B D).symm))))

private def degree {A B : List (Wire signatureWithScalar.Obj)} : Term A B → Nat
  | .id _ => 0
  | .gen _ => 1
  | .comp f g | .tensor f g => degree f + degree g

private theorem degree_reindex {A B C D : List (Wire signatureWithScalar.Obj)} (h : A = C) (k : B = D) (f : Term A B) :
    degree (Diagram.reindex h k f) = degree f := by
  cases h
  cases k
  rfl

private theorem degree_congr {A B : List (Wire signatureWithScalar.Obj)} {f g : Term A B}
    (h : Equation f g) : degree f = degree g := by
  induction h with
  | equation h =>
    cases h with
    | cancelRight x | cancelLeft x => exact x.elim
    | pureRight e | pureLeft e => exact e.elim
  | refl => rfl
  | symm _ h => exact h.symm
  | trans _ _ h k => exact h.trans k
  | comp _ _ h k | tensor _ _ h k => exact congrArg₂ (· + ·) h k
  | id_comp | comp_id | comp_assoc | tensor_id | tensor_comp
    | tensor_unit_left | tensor_unit_right | tensor_assoc =>
    simp [degree, degree_reindex, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private def oneWire : Runtime signatureWithScalar := runtime signatureWithScalar

private def scalar : oneWire ⟶ oneWire := Diagram.Presented.ofTerm generator

private theorem scalar_ne_id : scalar ≠ 𝟙 oneWire := by
  intro h
  have he : Equation generator (.id [none]) := Quotient.exact h
  exact Nat.noConfusion (degree_congr he)

private theorem scalar_commutes (f : oneWire ⟶ oneWire) : scalar ≫ f = f ≫ scalar :=
  Quotient.inductionOn f fun f =>
    Quotient.sound <| by
      have h : Equation (each [none]) generator := .tensor_unit_right generator
      exact (Diagram.Congruence.comp h.symm (.refl f)).trans ((each_commutes f).trans (.comp (.refl f) h))

open Computations
open scoped MonoidalCategory

private theorem sole_object (A : Computations signatureWithScalar) : A = unitWord := by
  cases A with
  | mk A =>
    cases A with
    | nil => rfl
    | cons x _ => exact x.elim

private theorem right_unit (f : unitWord ⟶ unitWord) :
    (Computations.whiskerRight unitWord).map f = f := by
  change oneWire ⟶ oneWire at f
  change (splitRight unitWord unitWord).hom ≫
    ((show oneWire ⟶ oneWire from f) ▷ (𝟙_ (Runtime signatureWithScalar))) ≫
    (splitRight unitWord unitWord).inv = f
  have hh : (splitRight unitWord unitWord).hom = (ρ_ oneWire).inv := by
    change 𝟙 oneWire ≫ 𝟙 oneWire = 𝟙 oneWire
    simp
  have hi : (splitRight unitWord unitWord).inv = (ρ_ oneWire).hom := by
    change 𝟙 oneWire ≫ 𝟙 oneWire = 𝟙 oneWire
    simp
  calc
    _ = (ρ_ oneWire).inv ≫ (f ▷ 𝟙_ (Runtime signatureWithScalar)) ≫ (ρ_ oneWire).hom :=
      congrArg₂ (fun l r => l ≫ (f ▷ 𝟙_ (Runtime signatureWithScalar)) ≫ r) hh hi
    _ = (ρ_ oneWire).inv ≫ (ρ_ oneWire).hom ≫ f :=
      congrArg (fun t => (ρ_ oneWire).inv ≫ t) (MonoidalCategory.rightUnitor_naturality f)
    _ = f := by simp

private theorem left_unit (f : unitWord ⟶ unitWord) :
    (Computations.whiskerLeft unitWord).map f = f := by
  change oneWire ⟶ oneWire at f
  change (splitLeft unitWord unitWord).hom ≫
    ((𝟙_ (Runtime signatureWithScalar)) ◁ (show oneWire ⟶ oneWire from f)) ≫
    (splitLeft unitWord unitWord).inv = f
  have rightHom : (splitRight unitWord unitWord).hom = 𝟙 oneWire := by
    change 𝟙 oneWire ≫ 𝟙 oneWire = 𝟙 oneWire
    simp
  have rightInv : (splitRight unitWord unitWord).inv = 𝟙 oneWire := by
    change 𝟙 oneWire ≫ 𝟙 oneWire = 𝟙 oneWire
    simp
  have crossHom : (crossingWord (G := signatureWithScalar) []).hom = 𝟙 oneWire := by
    change 𝟙 oneWire ≫ 𝟙 oneWire = 𝟙 oneWire
    simp
  have crossInv : (crossingWord (G := signatureWithScalar) []).inv = 𝟙 oneWire := by
    change 𝟙 oneWire ≫ 𝟙 oneWire = 𝟙 oneWire
    simp
  have hh : (splitLeft unitWord unitWord).hom = (λ_ oneWire).inv := by
    change (splitRight unitWord unitWord).hom ≫
      ((crossingWord (G := signatureWithScalar) []).hom ⊗ₘ 𝟙 (𝟙_ (Runtime signatureWithScalar))) ≫ 𝟙 oneWire = 𝟙 oneWire
    have ht := congrArg (fun t : oneWire ⟶ oneWire => t ⊗ₘ 𝟙 (𝟙_ (Runtime signatureWithScalar))) crossHom
    rw [MonoidalCategory.id_tensorHom_id] at ht
    calc
      _ = 𝟙 oneWire ≫ 𝟙 oneWire ≫ 𝟙 oneWire :=
        congrArg₂ (fun (l t : oneWire ⟶ oneWire) => l ≫ t ≫ 𝟙 oneWire) rightHom ht
      _ = 𝟙 oneWire := by simp
  have hi : (splitLeft unitWord unitWord).inv = (λ_ oneWire).hom := by
    change (𝟙 oneWire ≫ ((crossingWord (G := signatureWithScalar) []).inv ⊗ₘ 𝟙 (𝟙_ (Runtime signatureWithScalar)))) ≫
      (splitRight unitWord unitWord).inv = 𝟙 oneWire
    have ht := congrArg (fun t : oneWire ⟶ oneWire => t ⊗ₘ 𝟙 (𝟙_ (Runtime signatureWithScalar))) crossInv
    rw [MonoidalCategory.id_tensorHom_id] at ht
    calc
      _ = (𝟙 oneWire ≫ 𝟙 oneWire) ≫ 𝟙 oneWire :=
        congrArg₂ (fun (t r : oneWire ⟶ oneWire) => (𝟙 oneWire ≫ t) ≫ r) ht rightInv
      _ = 𝟙 oneWire := by simp
  calc
    _ = (λ_ oneWire).inv ≫ ((𝟙_ (Runtime signatureWithScalar)) ◁ f) ≫ (λ_ oneWire).hom :=
      congrArg₂ (fun l r => l ≫ ((𝟙_ (Runtime signatureWithScalar)) ◁ f) ≫ r) hh hi
    _ = (λ_ oneWire).inv ≫ (λ_ oneWire).hom ≫ f :=
      congrArg (fun t => (λ_ oneWire).inv ≫ t) (MonoidalCategory.leftUnitor_naturality f)
    _ = f := by simp

theorem scalar_ne_identity : effectfulScalar ≠ 𝟙 unitWord := scalar_ne_id

/-- Both sequential tensors with the nullary generator agree in the paper's whiskerings. -/
theorem scalar_exchanges :
    ∀ {A B : Computations signatureWithScalar} (f : A ⟶ B),
      ((Computations.whiskerRight A).map effectfulScalar ≫ (Computations.whiskerLeft unitWord).map f =
        (Computations.whiskerLeft unitWord).map f ≫ (Computations.whiskerRight B).map effectfulScalar) ∧
      ((Computations.whiskerRight unitWord).map f ≫ (Computations.whiskerLeft B).map effectfulScalar =
        (Computations.whiskerLeft A).map effectfulScalar ≫ (Computations.whiskerRight unitWord).map f) := by
  intro A B f
  have hA := sole_object A
  have hB := sole_object B
  subst A
  subst B
  rw [right_unit, left_unit, right_unit, left_unit]
  exact ⟨scalar_commutes f, (scalar_commutes f).symm⟩

end Silmaril.RuntimeWires.Nullary.Proofs
