module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Finite.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetFoldCoordinates

/-! # Constructor returns cannot present the doubled-state fold of an inhabited sum -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet.FoldCoordinates

open CategoryTheory CategoryTheory.Limits
open Semantics.Interaction.Typed (AtomValues)
open Paper.Extension.Singleton (projection)

variable {κ : Type u} [AtomValues κ] {Φ : Type v} [HasTy Φ (Ty κ)]

local notation "S" => Paper.WithEntryLet.Step (τ := Ty κ) (Φ := Φ)
local notation "P" => Paper.TypeCategory.ofType (Φ := Φ)
local notation "J" => projection S
local notation "Q" => Paper.Extension.Singleton.ofType S
local notation "CofanQ" => Paper.Extension.Singleton.sumCofan S
local notation "Val" => Ty.denote (AtomValues.carrier (κ := κ))
local infixr:65 " ⊕ₜ " => Silmaril.coprod

/-- Two sections of the same branch-value return to a sum with inhabited
summands agree in the EntryLet quotient. The input type of the return is
arbitrary. -/
theorem constructor_sections_eq {A B R : Ty κ} (a : Val A) (b : Val B)
    (p : P R ⟶ P (Silmaril.coprod A B)) (hp : Paper.TypeCategory.ConstructorReturn p)
    (left right : Q (Silmaril.coprod A B) ⟶ Q R)
    (hl : left ≫ (J).map p = 𝟙 _) (hr : right ≫ (J).map p = 𝟙 _) : left = right :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetFoldCoordinates.constructor_sections_eq
    a b p hp left right hl hr

/-- There is no constructor return that erases the tags after a change of
coordinates admitting a left inverse. The two tag equations and the round
trip may all hold in the EntryLet quotient. -/
theorem no_projected_coordinates {A B R : Ty κ} (a : Val A) (b : Val B)
    (p : P R ⟶ P (A ⊕ₜ B)) (hp : Paper.TypeCategory.ConstructorReturn p)
    (encode : Q ((A ⊕ₜ B) ⊕ₜ (A ⊕ₜ B)) ⟶ Q R)
    (decode : Q R ⟶ Q ((A ⊕ₜ B) ⊕ₜ (A ⊕ₜ B)))
    (faithful : encode ≫ decode = 𝟙 _)
    (hl : (CofanQ (A ⊕ₜ B) (A ⊕ₜ B)).inl ≫ encode ≫ (J).map p = 𝟙 _)
    (hr : (CofanQ (A ⊕ₜ B) (A ⊕ₜ B)).inr ≫ encode ≫ (J).map p = 𝟙 _) : False :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetFoldCoordinates.no_projected_coordinates
    a b p hp encode decode faithful hl hr

/-- The same obstruction applies to the chosen coproduct fold in a
commuting square of the form used by `Alternating.fold_iff_double`. -/
theorem no_chosen_coordinates {A B R : Ty κ} (a : Val A) (b : Val B)
    (p : P R ⟶ P (A ⊕ₜ B)) (hp : Paper.TypeCategory.ConstructorReturn p)
    (encode : Q (A ⊕ₜ B) ⨿ Q (A ⊕ₜ B) ⟶ Q R)
    (decode : Q R ⟶ Q (A ⊕ₜ B) ⨿ Q (A ⊕ₜ B))
    (faithful : encode ≫ decode = 𝟙 _)
    (fold : encode ≫ (J).map p = coprod.desc (𝟙 (Q (A ⊕ₜ B))) (𝟙 (Q (A ⊕ₜ B)))) : False :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetFoldCoordinates.no_chosen_coordinates
    a b p hp encode decode faithful fold

/-- The candidate native compositions include the round trip and the state
map comparison. They project to the contradictory EntryLet equations. -/
theorem no_native_coordinates {A B R : Ty κ} (a : Val A) (b : Val B)
    (p : P R ⟶ P (A ⊕ₜ B)) (hp : Paper.TypeCategory.ConstructorReturn p)
    (encode : P ((A ⊕ₜ B) ⊕ₜ (A ⊕ₜ B)) ⟶ P R)
    (decode : P R ⟶ P ((A ⊕ₜ B) ⊕ₜ (A ⊕ₜ B)))
    (faithful : encode ≫ decode = 𝟙 _)
    (fold : encode ≫ p = (Paper.TypeCategory.sumIso (Φ := Φ) (A ⊕ₜ B) (A ⊕ₜ B)).hom ≫
      coprod.desc (𝟙 (P (A ⊕ₜ B))) (𝟙 (P (A ⊕ₜ B)))) : False :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetFoldCoordinates.no_native_coordinates
    a b p hp encode decode faithful fold

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet.FoldCoordinates
