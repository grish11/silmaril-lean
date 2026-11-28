module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable.Transport
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Routes.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Packing.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Labels.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LambdaSSA.Region (ValueBranches packedExitType packedExitArg)
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback
  (carryExit carryExit_typed)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CartesianMonoidalCategory (fst snd lift)
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical.SingletonDispatcher (labelInject_payload)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend)
open Silmaril.Isotope.LetIter.Semantics.Categorical
  (TypeModel InstructionModel extend_postmap pair_maps_eq_map_lift)

universe u v u₁ u₂ v₁ v₂
variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type v} [HasTy Φ τ] [InstructionModel J M Φ]

local notation "×ₛ" => Silmaril.product
local notation "⊕ₛ" => Silmaril.coprod
local notation "E" => ctxObj M
local notation "Labels" => labelObj M

omit [SymmetricCategory V] [DistributiveTensor V] in
@[reassoc] private theorem labelInject_payload' (A : τ) :
    labelInject M 0 (L := [A]) (A := A) rfl ≫ singletonLabelPayload M A = 𝟙 _ :=
  labelInject_payload M A

section Value

variable {n : Nat} (R : Fin n → τ) (D : τ)

noncomputable def capturedStateIso (X : τ) (L : LCtx τ) :
    E [X] ⊗ Labels L ≅ M.obj (×ₛ X (packedExitType L)) :=
  (MonoidalCategory.tensorLeft (E [X])).mapIso (packLabelIso M L) ≪≫
    (MonoidalCategory.tensorRight (M.obj (packedExitType L))).mapIso (λ_ (M.obj X)) ≪≫
    (M.productIso X (packedExitType L)).symm

noncomputable def rowInputIso (X A : τ) :
    E [X] ⊗ M.obj A ≅ M.obj (×ₛ X A) :=
  (MonoidalCategory.tensorRight (M.obj A)).mapIso (λ_ (M.obj X)) ≪≫ (M.productIso X A).symm

noncomputable def packCapture {K : V} {X : τ} (p : K ⟶ M.obj X) (L : LCtx τ) :
    K ⊗ Labels L ⟶ M.obj (×ₛ X (packedExitType L)) :=
  (p ⊗ₘ packLabel M L) ≫ (M.productIso X (packedExitType L)).inv


noncomputable def encodeExit (P : τ) : Labels [D] ⨿ M.obj P ⟶ Labels [⊕ₛ D P] :=
  coprod.map (singletonLabelPayload M D) (𝟙 _) ≫ (M.coprodIso D P).inv ≫ labelInject M 0 rfl

noncomputable def decodeExit (P : τ) : Labels [⊕ₛ D P] ⟶ Labels [D] ⨿ M.obj P :=
  singletonLabelPayload M (⊕ₛ D P) ≫ (M.coprodIso D P).hom ≫ coprod.map (labelInject M 0 rfl) (𝟙 _)

omit [SymmetricCategory V] [DistributiveTensor V] in
@[reassoc (attr := simp)] theorem encodeExit_decodeExit (P : τ) :
    encodeExit M D P ≫ decodeExit M D P = 𝟙 _ := by
  simp only [encodeExit, decodeExit, Category.assoc, labelInject_payload'_assoc, Iso.inv_hom_id_assoc,
    coprod.map_map, Category.comp_id, SingletonDispatcher.payload_labelInject, coprod.map_id_id]

omit [SymmetricCategory V] [DistributiveTensor V] in
@[reassoc] private theorem encodeExit_inr (P : τ) :
    (coprod.inr : M.obj P ⟶ Labels [D] ⨿ M.obj P) ≫ encodeExit M D P =
      coprod.inr ≫ (M.coprodIso D P).inv ≫ labelInject M 0 rfl := by
  simp [encodeExit]

end Value

set_option backward.isDefEq.respectTransparency false

omit [TypeFormers τ] in
private theorem label_cases {n : Nat} (R : Fin n → τ) {D A : τ} {i : Nat}
    (hi : At (List.ofFn R ++ [D]) i A) :
    (∃ j : Fin n, i = j ∧ A = R j) ∨ (i = n ∧ A = D) := by
  by_cases h : i < n
  · let j : Fin n := ⟨i, h⟩
    have t : (List.ofFn R ++ [D])[i]? = some (R j) := by
      simp [List.getElem?_append_left, h, j]
    exact .inl ⟨j, rfl, Option.some.inj (hi.symm.trans t)⟩
  · have j : i = n := by
      have hi' := (List.getElem?_eq_some_iff.mp hi).1
      simp at hi'
      omega
    subst i
    exact .inr ⟨rfl, Option.some.inj (by simpa [List.getElem?_append_right] using hi.symm)⟩

omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem packCapture_leg {K : V} {X A : τ} (p : K ⟶ M.obj X)
    {L : LCtx τ} {i : Nat} (hi : At L i A) :
    (K ◁ labelInject M i hi) ≫ packCapture M p L =
      lift (fst K (M.obj A) ≫ p) (snd K (M.obj A) ≫ packedLabelInject M i hi) ≫
        (M.productIso X (packedExitType L)).inv := by
  unfold packCapture
  rw [← Category.assoc]
  have h : (K ◁ labelInject M i hi) ≫ (p ⊗ₘ packLabel M L) =
      lift (fst K (M.obj A) ≫ p) (snd K (M.obj A) ≫ packedLabelInject M i hi) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [Category.assoc, CartesianMonoidalCategory.whiskerLeft_fst_assoc]
    · simp [Category.assoc, labelInject_packLabel]
  rw [h]

private theorem carryContinuation {n : Nat} (R : Fin n → τ) {Γ : VCtx τ} {X D : τ}
    {k : Nat} (hx : At Γ k X) :
    let L := List.ofFn R
    let P := ×ₛ X (packedExitType L)
    ContinuationDenotes J M (carryExit k n : Nat → Region Φ)
      (J.map ((E Γ ◁ labelAppendSplit M L [D]) ≫
        carryRoute (packCapture M (lookup M k hx) L) ≫ encodeExit M D P)) := by
  dsimp only
  intro i A hi
  let L := List.ofFn R
  let P := ×ₛ X (packedExitType L)
  let σ := labelAppendSplit M L [D]
  let q := packCapture M (lookup M k hx) L
  have hmap (j : Nat) {A : τ} (h : At (L ++ [D]) j A) :
      J.map ((𝟙 (E Γ)) ⊗ₘ labelInject M j h) ≫
        J.map ((E Γ ◁ σ) ≫ carryRoute q ≫ encodeExit M D P) =
      J.map ((E Γ ◁ (labelInject M j h ≫ σ)) ≫ carryRoute q ≫ encodeExit M D P) := by
    simp only [MonoidalCategory.id_tensorHom, MonoidalCategory.whiskerLeft_comp, J.map_comp, Category.assoc]
  rw [hmap]
  rcases label_cases R hi with ⟨j, hij, hA⟩ | ⟨hin, hA⟩
  · subst i
    subst A
    have hj : At L j (R j) := by simp [L, At]
    let va := Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (Γ := R j :: Γ) (A := R j) rfl
    let vx := Denotes.var (J := J) (M := M) (Φ := Φ) (i := k+1) (Γ := R j :: Γ) (A := X) hx
    obtain ⟨hjty, dj⟩ := va.packedExitArg J M hj
    have dp := Denotes.pair vx dj
    have dr := RegionDenotes.br (h := (rfl : At [⊕ₛ D P] 0 (⊕ₛ D P)))
      (Denotes.inr (A := D) dp)
    rw [labelAppendSplit_local M R [D] j hi hj, MonoidalCategory.whiskerLeft_comp,
      Category.assoc, carryRoute_inr_assoc]
    rw [← Category.assoc, packCapture_leg M _ hj]
    simp only [carryExit, ite_eq_left j.isLt]
    refine ⟨.br rfl (.inr (.pair (.var hx) hjty)), ?_⟩
    simp only [← J.map_comp, pair_maps_eq_map_lift] at dr
    simp only [Category.assoc, J.map_comp]
    rw [← J.map_comp (coprod.inr : M.obj P ⟶ Labels [D] ⨿ M.obj P) (encodeExit M D P),
      encodeExit_inr M D P]
    simpa only [lookup, Category.assoc, J.map_comp] using dr
  · subst i
    subst A
    have hd := labelAppendSplit_exit M R [D] (rfl : At [D] 0 D)
      (by simpa using hi : At (List.ofFn R ++ [D]) (n + 0) D)
    simp only [Nat.add_zero] at hd
    rw [hd, MonoidalCategory.whiskerLeft_comp, Category.assoc, carryRoute_inl_assoc]
    let va := Denotes.var (J := J) (M := M) (Φ := Φ) (i := 0) (Γ := D :: Γ) (A := D) rfl
    have dr := RegionDenotes.br (h := (rfl : At [⊕ₛ D P] 0 (⊕ₛ D P))) (Denotes.inl (B := P) va)
    simp only [carryExit, ite_eq_right (Nat.lt_irrefl n)]
    refine ⟨.br rfl (.inl (.var rfl)), ?_⟩
    simpa only [lookup, encodeExit,
      Category.assoc, J.map_comp, coprod.inl_map_assoc, CartesianMonoidalCategory.whiskerLeft_snd_assoc,
      labelInject_payload'_assoc, Category.comp_id] using dr

variable [FreydCategory.CentralUnit J] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ U W : V, ∃ h : J.obj U ⊗ J.obj W = J.obj (U ⊗ W),
    Functor.StrongPremonoidal.tensorIso (J := J) U W = eqToIso h)

include shared in
theorem denote_carry {n : Nat} (R : Fin n → τ) {Γ : VCtx τ} {X D : τ}
    {k : Nat} (hx : At Γ k X) {r : Region Φ}
    (hr : ValueBranches Γ r (List.ofFn R ++ [D])) :
    let L := List.ofFn R
    let P := ×ₛ X (packedExitType L)
    let ht := hr.lsubst (carryExit_typed (Φ := Φ) L hx)
    denoteRegion J M ht.hasType ≫ J.map (decodeExit M D P) =
      extend J (denoteRegion J M hr.hasType ≫ J.map (labelAppendSplit M L [D])) ≫
        J.map (carryRoute (packCapture M (lookup M k hx) L)) := by
  dsimp only
  have hc := carryContinuation J M (Φ := Φ) R (D := D) hx
  have ht := (hr.lsubst (carryExit_typed (Φ := Φ) (List.ofFn R) hx)).hasType
  have hc' : ContinuationDenotes J M (carryExit k (List.ofFn R).length : Nat → Region Φ)
      (J.map ((E Γ ◁ labelAppendSplit M (List.ofFn R) [D]) ≫
        carryRoute (packCapture M (lookup M k hx) (List.ofFn R)) ≫
          encodeExit M D (×ₛ X (packedExitType (List.ofFn R))))) := by
    simpa only [List.length_ofFn] using hc
  rw [denoteRegion_lsubst_sharedTensor J M shared hr.hasType ht
    (PureBranches.of_valueBranches J M hr) hc']
  rw [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, Category.assoc, ← J.map_comp]
  simp only [Category.assoc, encodeExit_decodeExit, Category.comp_id, J.map_comp, extend_postmap]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable
