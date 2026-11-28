module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Coproducts.Finite.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Erasure.Thms
public import Silmaril.Semantics.Calco2019.Maybe.Types.Thms

/-! # No constructor changes coordinates for the fold of an inhabited sum -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetFoldCoordinates

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open Semantics.Interaction.Typed (AtomValues typeModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics (InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Paper.TypeCategory (ofType ofRegion ofRegion_comp ofRegion_id)
open Paper.Extension.Singleton (projection)

variable {κ : Type u} [AtomValues κ] {Φ : Type v} [HasTy Φ (Ty κ)]

local notation "S" => Paper.WithEntryLet.Step (τ := Ty κ) (Φ := Φ)
local notation "P" => Paper.TypeCategory.ofType (Φ := Φ)
local notation "J" => projection S
local notation "Q" => Paper.Extension.Singleton.ofType S
local notation "CofanQ" => Paper.Extension.Singleton.sumCofan S
local notation "CofanP" => Paper.TypeCategory.sumCofan (Φ := Φ)
local notation "Val" => Ty.denote (AtomValues.carrier (κ := κ))

attribute [local instance] typeModel

set_option hygiene false in
set_option quotPrecheck false in
local notation "Maybe" => (Silmaril.Calco2019.Maybe.Types.Model : Type u → Type u)
local notation "M" => ofMonadicTypeModel (τ := Ty κ)
local notation "K" => typeJ (m := Maybe)

local instance : HasEff Φ Bool where
  eff _ := true

local instance : InstructionModel Φ (Ty κ) Bool Maybe where
  denote _ _ := .inr PUnit.unit
  denotePure _ h := by cases h
  denote_pure _ h := by cases h

local instance : Silmaril.Isotope.LetIter.Semantics.Categorical.InstructionModel K M Φ :=
  ofMonadicInstructionModel (ε := Bool)

local instance : RegionTypingCoherent (Φ := Φ) K M :=
  Semantics.Erasure.regionTypingCoherent (κ := κ) (Φ := Φ) (m := Maybe)
    (fun _ _ => .inr PUnit.unit) (.inr PUnit.unit) (.inr PUnit.unit)
    (fun _ _ => rfl)

private noncomputable abbrev eval :=
  Paper.WithEntryLet.denoteFunctor (Φ := Φ) K M (fun _ _ => ⟨rfl, rfl⟩)

set_option backward.isDefEq.respectTransparency false

private theorem inl_value (A B : Ty κ) (a : Val A) :
    ((eval (κ := κ) (Φ := Φ)).map (CofanQ A B).inl).of a = (Sum.inl (Sum.inl a) : Maybe (Val (Silmaril.coprod A B))) := by
  change ((eval (κ := κ) (Φ := Φ)).map ((J).map (CofanP A B).inl)).of a = _
  rw [Paper.TypeCategory.sumCofan_inl, Paper.WithEntryLet.denoteFunctor_map_ofRegion,
    denoteSingletonRegion_br K M (.inl (.var (i := 0) rfl))]
  simp only [lookup, ← Functor.map_comp]
  change ((K).map (coprod.inl ≫ (Types.binaryCoproductIso (Val A) (Val B)).hom)).of a = _
  rw [Types.binaryCoproductIso_inl_comp_hom]
  rfl

private theorem inr_value (A B : Ty κ) (b : Val B) :
    ((eval (κ := κ) (Φ := Φ)).map (CofanQ A B).inr).of b = (Sum.inl (Sum.inr b) : Maybe (Val (Silmaril.coprod A B))) := by
  change ((eval (κ := κ) (Φ := Φ)).map ((J).map (CofanP A B).inr)).of b = _
  rw [Paper.TypeCategory.sumCofan_inr, Paper.WithEntryLet.denoteFunctor_map_ofRegion,
    denoteSingletonRegion_br K M (.inr (.var (i := 0) rfl))]
  simp only [lookup, ← Functor.map_comp]
  change ((K).map (coprod.inr ≫ (Types.binaryCoproductIso (Val A) (Val B)).hom)).of b = _
  rw [Types.binaryCoproductIso_inr_comp_hom]
  rfl

private theorem no_inl_section {A B : Ty κ} (b : Val B)
    (h : Q (Silmaril.coprod A B) ⟶ Q A) :
    h ≫ (CofanQ A B).inl ≠ 𝟙 (Q (Silmaril.coprod A B)) := by
  intro eq
  let F := eval (κ := κ) (Φ := Φ)
  have obs := congrArg (fun (k : Q (Silmaril.coprod A B) ⟶ Q (Silmaril.coprod A B)) => (F.map k).of (Sum.inr b)) eq
  rw [F.map_comp, F.map_id] at obs
  have comp := congrFun (Kleisli.Type.comp_of_eq_kleisliRight Maybe
    (F.map h) (F.map (CofanQ A B).inl)) (Sum.inr b)
  have obs := comp.symm.trans obs
  change ((F.map h).of (Sum.inr b)).elim (fun a => (F.map (CofanQ A B).inl).of a)
    Sum.inr = Sum.inl (Sum.inr b) at obs
  generalize (F.map h).of (Sum.inr b) = result at obs
  cases result with
  | inl a =>
    change (F.map (CofanQ A B).inl).of a = _ at obs
    cases Sum.inl.inj ((inl_value (Φ := Φ) A B a).symm.trans obs)
  | inr err => cases obs

private theorem no_inr_section {A B : Ty κ} (a : Val A)
    (h : Q (Silmaril.coprod A B) ⟶ Q B) :
    h ≫ (CofanQ A B).inr ≠ 𝟙 (Q (Silmaril.coprod A B)) := by
  intro eq
  let F := eval (κ := κ) (Φ := Φ)
  have obs := congrArg (fun (k : Q (Silmaril.coprod A B) ⟶ Q (Silmaril.coprod A B)) => (F.map k).of (Sum.inl a)) eq
  rw [F.map_comp, F.map_id] at obs
  have comp := congrFun (Kleisli.Type.comp_of_eq_kleisliRight Maybe
    (F.map h) (F.map (CofanQ A B).inr)) (Sum.inl a)
  have obs := comp.symm.trans obs
  change ((F.map h).of (Sum.inl a)).elim (fun b => (F.map (CofanQ A B).inr).of b)
    Sum.inr = Sum.inl (Sum.inl a) at obs
  generalize (F.map h).of (Sum.inl a) = result at obs
  cases result with
  | inl b =>
    change (F.map (CofanQ A B).inr).of b = _ at obs
    cases Sum.inl.inj ((inr_value (Φ := Φ) A B b).symm.trans obs)
  | inr err => cases obs

private theorem tags_ne {D : Ty κ} (x : Val D) : (CofanQ D D).inl ≠ (CofanQ D D).inr := by
  intro e
  have obs := congrArg (fun f => ((eval (κ := κ) (Φ := Φ)).map f).of x) e
  cases Sum.inl.inj ((inl_value (Φ := Φ) D D x).symm.trans
    (obs.trans (inr_value (Φ := Φ) D D x)))

omit [AtomValues κ] in
private theorem branch_inl {R A B : Ty κ} {a : Tm Φ} (ha : Tm.BranchValue [R] a A) :
    ofRegion (.br (ℓ := 0) rfl ha) ≫ (CofanP A B).inl =
      ofRegion (.br (ℓ := 0) rfl (.inl ha)) := by
  rw [Paper.TypeCategory.sumCofan_inl]
  exact ofRegion_comp _ _ (.br (ℓ := 0) rfl (.inl ha))

omit [AtomValues κ] in
private theorem branch_inr {R A B : Ty κ} {a : Tm Φ} (ha : Tm.BranchValue [R] a B) :
    ofRegion (.br (ℓ := 0) rfl ha) ≫ (CofanP A B).inr =
      ofRegion (.br (ℓ := 0) rfl (.inr ha)) := by
  rw [Paper.TypeCategory.sumCofan_inr]
  exact ofRegion_comp _ _ (.br (ℓ := 0) rfl (.inr ha))

/-- All sections of the same constructor return to a nondegenerate sum agree
after projection. The replacement input type is arbitrary. -/
theorem constructor_sections_eq {A B R : Ty κ} (a : Val A) (b : Val B)
    (p : P R ⟶ P (Silmaril.coprod A B)) (hp : Paper.TypeCategory.ConstructorReturn p)
    (left right : Q (Silmaril.coprod A B) ⟶ Q R)
    (hl : left ≫ (J).map p = 𝟙 _) (hr : right ≫ (J).map p = 𝟙 _) : left = right := by
  obtain ⟨_, ht, rfl⟩ := hp
  cases ht with
  | var hi =>
    rename_i i
    cases i with
    | zero =>
      cases Option.some.inj hi
      rw [ofRegion_id, (J).map_id, Category.comp_id] at hl hr
      exact hl.trans hr.symm
    | succ i => simp [At] at hi
  | inl ht =>
    rw [← branch_inl ht, (J).map_comp, ← Category.assoc] at hl
    exact (no_inl_section b _ hl).elim
  | inr ht =>
    rw [← branch_inr ht, (J).map_comp, ← Category.assoc] at hl
    exact (no_inr_section a _ hl).elim

local infixr:65 " ⊕ₜ " => Silmaril.coprod

theorem no_projected_coordinates {A B R : Ty κ} (a : Val A) (b : Val B)
    (p : P R ⟶ P (A ⊕ₜ B)) (hp : Paper.TypeCategory.ConstructorReturn p)
    (encode : Q ((A ⊕ₜ B) ⊕ₜ (A ⊕ₜ B)) ⟶ Q R)
    (decode : Q R ⟶ Q ((A ⊕ₜ B) ⊕ₜ (A ⊕ₜ B)))
    (faithful : encode ≫ decode = 𝟙 _)
    (hl : (CofanQ (A ⊕ₜ B) (A ⊕ₜ B)).inl ≫ encode ≫ (J).map p = 𝟙 _)
    (hr : (CofanQ (A ⊕ₜ B) (A ⊕ₜ B)).inr ≫ encode ≫ (J).map p = 𝟙 _) : False := by
  have eq := constructor_sections_eq a b p hp
    ((CofanQ (A ⊕ₜ B) (A ⊕ₜ B)).inl ≫ encode) ((CofanQ (A ⊕ₜ B) (A ⊕ₜ B)).inr ≫ encode)
    (by rw [Category.assoc]; exact hl) (by rw [Category.assoc]; exact hr)
  have result := congrArg (· ≫ decode) eq
  simp only [Category.assoc, faithful] at result
  apply tags_ne (Φ := Φ) (D := A ⊕ₜ B) (.inl a)
  exact (Category.comp_id (CofanQ (A ⊕ₜ B) (A ⊕ₜ B)).inl).symm.trans
    (result.trans (Category.comp_id (CofanQ (A ⊕ₜ B) (A ⊕ₜ B)).inr))

theorem no_chosen_coordinates {A B R : Ty κ} (a : Val A) (b : Val B)
    (p : P R ⟶ P (A ⊕ₜ B)) (hp : Paper.TypeCategory.ConstructorReturn p)
    (encode : Q (A ⊕ₜ B) ⨿ Q (A ⊕ₜ B) ⟶ Q R)
    (decode : Q R ⟶ Q (A ⊕ₜ B) ⨿ Q (A ⊕ₜ B))
    (faithful : encode ≫ decode = 𝟙 _)
    (fold : encode ≫ (J).map p = coprod.desc (𝟙 (Q (A ⊕ₜ B))) (𝟙 (Q (A ⊕ₜ B)))) : False := by
  let c := Paper.Extension.Singleton.sumIso S (A ⊕ₜ B) (A ⊕ₜ B)
  have leftFold : coprod.inl ≫ encode ≫ (J).map p = 𝟙 _ := by rw [fold, coprod.inl_desc]
  have rightFold : coprod.inr ≫ encode ≫ (J).map p = 𝟙 _ := by rw [fold, coprod.inr_desc]
  refine no_projected_coordinates a b p hp (c.hom ≫ encode) (decode ≫ c.inv) ?_ ?_ ?_
  · rw [Category.assoc, ← Category.assoc encode decode, faithful,
      Category.id_comp, Iso.hom_inv_id]
  · rw [Category.assoc, ← Category.assoc, show (CofanQ (A ⊕ₜ B) (A ⊕ₜ B)).inl ≫ c.hom =
        coprod.inl from Paper.Extension.Singleton.sumCofan_inl_sumIso_hom S _ _, leftFold]
  · rw [Category.assoc, ← Category.assoc, show (CofanQ (A ⊕ₜ B) (A ⊕ₜ B)).inr ≫ c.hom =
        coprod.inr from Paper.Extension.Singleton.sumCofan_inr_sumIso_hom S _ _, rightFold]

theorem no_native_coordinates {A B R : Ty κ} (a : Val A) (b : Val B)
    (p : P R ⟶ P (A ⊕ₜ B)) (hp : Paper.TypeCategory.ConstructorReturn p)
    (encode : P ((A ⊕ₜ B) ⊕ₜ (A ⊕ₜ B)) ⟶ P R)
    (decode : P R ⟶ P ((A ⊕ₜ B) ⊕ₜ (A ⊕ₜ B)))
    (faithful : encode ≫ decode = 𝟙 _)
    (fold : encode ≫ p = (Paper.TypeCategory.sumIso (Φ := Φ) (A ⊕ₜ B) (A ⊕ₜ B)).hom ≫
      coprod.desc (𝟙 (P (A ⊕ₜ B))) (𝟙 (P (A ⊕ₜ B)))) : False := by
  refine no_projected_coordinates a b p hp ((J).map encode) ((J).map decode) ?_ ?_ ?_
  · rw [← (J).map_comp, faithful, (J).map_id]
  · change (J).map (CofanP (A ⊕ₜ B) (A ⊕ₜ B)).inl ≫ (J).map encode ≫ (J).map p = _
    rw [← (J).map_comp, ← (J).map_comp, fold, ← Category.assoc,
      Paper.TypeCategory.sumCofan_inl_sumIso_hom, coprod.inl_desc, (J).map_id]
  · change (J).map (CofanP (A ⊕ₜ B) (A ⊕ₜ B)).inr ≫ (J).map encode ≫ (J).map p = _
    rw [← (J).map_comp, ← (J).map_comp, fold, ← Category.assoc,
      Paper.TypeCategory.sumCofan_inr_sumIso_hom, coprod.inr_desc, (J).map_id]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetFoldCoordinates
