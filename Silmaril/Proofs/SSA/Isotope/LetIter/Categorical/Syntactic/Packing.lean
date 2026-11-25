module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Syntactic.Packing.Defs
public import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Iteration.Defs
import Silmaril.SSA.Isotope.Bridge.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms
import Silmaril.SSA.Thesis.SyntacticCategory.Packing.Iteration.Thms

public section

universe u

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.PackingProofs

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory CartesianMonoidalCategory
open Silmaril.Thesis.LambdaIter (Sig)
open Silmaril.Thesis.LambdaIter.Syn (mk)
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)
open Silmaril.Thesis.LambdaIter.LocallyNameless (HasType)
open Silmaril.Thesis.LambdaIter.Syn.SynCat

open ProofRelevant.Semantics.Categorical (caseWithContext contextualLoop extend retainLeft splitMapCoprod)
local notation "pairArrow" => ProofRelevant.Semantics.Categorical.pair
local notation "bindArrow" => ProofRelevant.Semantics.Categorical.bind

variable {τ Φ ε : Type u} [TypeFormers τ] [HasTy Φ τ] [HasEff Φ ε]

theorem packedNative_let1 (pe : ε) {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n}
    {s : Tm Empty Φ (n + 1)} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A)
    (e : Derivation Φ (Ctx.nil : Ctx Empty τ) (.snoc β A) s B) :
    packedNative pe (.let₁ d e) =
      bindArrow (values (signature (τ := τ) (Φ := Φ) pe)) (packedNative pe d) (packedNative pe e) := by
  let J := values (signature (τ := τ) (Φ := Φ) pe)
  unfold packedNative
  change J.map (packedEnvIso (Φ := Φ) pe β).inv ≫
      bindArrow J (denoteInSyntax pe d)
        (J.map (envSnocIso (typeModel (Φ := Φ) pe) (Ctx.nil : Ctx Empty τ) β A).hom ≫
          denoteInSyntax pe e) = _
  rw [← bind_pre_map, ← Category.assoc, ← Functor.map_comp, packedEnvInv_snoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem bind_values {S : Sig.{u}} {X A B : ValueCat S}
    (f : X.obj ⟶ A.obj) (g : (X ⊗ A).obj ⟶ B.obj) :
    bindArrow (values S) f g = pairArrows (𝟙 X.obj) f ≫ g := by
  unfold ProofRelevant.Semantics.Categorical.bind ProofRelevant.Semantics.Categorical.extend
    ProofRelevant.Semantics.Categorical.duplicate
  have hmap : (values S).map (CartesianMonoidalCategory.lift (𝟙 X) (𝟙 X)) =
      pairArrows (𝟙 X.obj) (𝟙 X.obj) := valueLift_hom (𝟙 X) (𝟙 X)
  have hi : (Functor.StrongPremonoidal.tensorIso (J := values S) X X).inv = 𝟙 _ := by rfl
  have hh : (Functor.StrongPremonoidal.tensorIso (J := values S) X A).hom = 𝟙 _ := by rfl
  rw [hmap, hi, hh]
  change (pairArrows (𝟙 X.obj) (𝟙 X.obj) ≫ 𝟙 _ ≫
    leftTensor (𝟙 X.obj) f ≫ 𝟙 _) ≫ g = _
  simp only [Category.id_comp, Category.comp_id, leftTensor, id_whiskerRight, Category.assoc]
  change pairArrows (𝟙 X.obj) (𝟙 X.obj) ≫ tensorLeft X.obj f ≫ g = _
  rw [← Category.assoc, tensorLeft_pair (isPureMor_id _) (isPureMor_id _), Category.id_comp]

local instance : Thesis.LambdaIter.TypeFormers τ := Bridge.thesisTypeFormers τ
local instance : Thesis.LambdaIter.HasTy Φ τ := Bridge.thesisHasTy Φ τ

private theorem fst_transport {V : Type u} [Category* V] [CartesianMonoidalCategory V]
    {X Y : V} (e : X = Y) (A : V) :
    eqToHom (congrArg (fun Z => Z ⊗ A) e).symm ≫ CartesianMonoidalCategory.fst X A =
      CartesianMonoidalCategory.fst Y A ≫ eqToHom e.symm := by
  subst Y
  simp

private theorem snd_transport {V : Type u} [Category* V] [CartesianMonoidalCategory V]
    {X Y : V} (e : X = Y) (A : V) :
    eqToHom (congrArg (fun Z => Z ⊗ A) e).symm ≫ CartesianMonoidalCategory.snd X A =
      CartesianMonoidalCategory.snd Y A := by
  subst Y
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem packedBoundLookup (pe : ε) {n : Nat} (β : BoundCtx τ n) (i : Fin n) :
    let S := signature (τ := τ) (Φ := Φ) pe
    (values S).map (eqToHom (boundObj_eq (Φ := Φ) pe β).symm ≫
        boundLookup (typeModel (Φ := Φ) pe) i) ≫
      eqToHom (congrArg (fun A : τ => of (S := S) A) (Bridge.BoundCtx.get_toThesis β i).symm) =
      packedArrow (S := S) (HasType.bv (β := Bridge.BoundCtx.toThesis β) (ι := i)) := by
  let S := signature (τ := τ) (Φ := Φ) pe
  let J := values S
  let M := typeModel (τ := τ) (Φ := Φ) pe
  induction β with
  | nil => exact i.elim0
  | snoc β A ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · refine Eq.trans ?_ (packedArrow_bv_zero (S := S) (Bridge.BoundCtx.toThesis β) A).symm
      let E := boundObj_eq (Φ := Φ) pe β
      let Y := valueObj (Φ := Φ) pe A
      change J.map (eqToHom (congrArg (fun Z => Z ⊗ Y) E).symm ≫
        CartesianMonoidalCategory.snd (boundObj M β) Y) ≫ 𝟙 _ =
          J.map (CartesianMonoidalCategory.snd _ Y)
      rw [Category.comp_id]
      exact congrArg J.map (snd_transport E Y)
    · refine Eq.trans ?_ (packedArrow_bv_succ (S := S) (Bridge.BoundCtx.toThesis β) A j).symm
      let E := boundObj_eq (Φ := Φ) pe β
      let Y := valueObj (Φ := Φ) pe A
      let resultCast := eqToHom (congrArg (fun A : τ => J.obj (M.obj A))
        (Bridge.BoundCtx.get_toThesis β j).symm)
      change J.map (eqToHom (congrArg (fun Z => Z ⊗ Y) E).symm ≫
        (CartesianMonoidalCategory.fst (boundObj M β) Y ≫ boundLookup M j)) ≫ resultCast = _
      have moveProjection :
          eqToHom (congrArg (fun Z => Z ⊗ Y) E).symm ≫
              (CartesianMonoidalCategory.fst (boundObj M β) Y ≫ boundLookup M j) =
            CartesianMonoidalCategory.fst _ Y ≫ (eqToHom E.symm ≫ boundLookup M j) := by
        rw [← Category.assoc, fst_transport E Y, Category.assoc]
      calc
        _ = J.map (CartesianMonoidalCategory.fst _ Y ≫ (eqToHom E.symm ≫ boundLookup M j)) ≫
            resultCast := congrArg (fun f => J.map f ≫ resultCast) moveProjection
        _ = J.map (CartesianMonoidalCategory.fst _ Y) ≫
            (J.map (eqToHom E.symm ≫ boundLookup M j) ≫ resultCast) := by
          rw [J.map_comp, Category.assoc]
        _ = _ := congrArg (fun f => J.map (CartesianMonoidalCategory.fst _ Y) ≫ f) (ih j)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem packedNative_bv_eq_packedArrow (pe : ε)
    {n : Nat} {β : BoundCtx τ n} (i : Fin n)
    (h : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (.bv i) (β.get i)) :
    packedNative pe (Derivation.bv (Φ := Φ) (Γ := (Ctx.nil : Ctx Empty τ)) (ι := i) (β := β)) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) h := by
  let S := signature (τ := τ) (Φ := Φ) pe
  let J := values S
  let M := typeModel (τ := τ) (Φ := Φ) pe
  change J.map (packedEnvIso (Φ := Φ) pe β).inv ≫
    J.map (boundVar M (Γ := (Ctx.nil : Ctx Empty τ)) (β := β) i) = _
  rw [← J.map_comp, packedEnvInv_boundVar]
  have castPacked : ∀ {A : τ} (e : (Bridge.BoundCtx.toThesis β).get i = A)
      (k : HasType S.Instr .nil (Bridge.BoundCtx.toThesis β) (.bv i) A),
      packedArrow (S := S) (HasType.bv (ι := i)) ≫ eqToHom (congrArg (of (S := S)) e) =
        packedArrow (S := S) k := by
    intro A e k
    subst A
    rw [eqToHom_refl, Category.comp_id]
    rfl
  have e := Bridge.BoundCtx.get_toThesis β i
  rw [← castPacked e h, ← packedBoundLookup pe β i]
  simp
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem packedNative_unit_eq_packedArrow (pe : ε) {n : Nat} {β : BoundCtx τ n}
    (h : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) .unit (Silmaril.unit : τ)) :
    packedNative pe (Derivation.unit (Φ := Φ) (Γ := (Ctx.nil : Ctx Empty τ)) (β := β)) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) h := by
  cases h
  let _ := Bridge.thesisHasEff Φ ε
  let S := signature (τ := τ) (Φ := Φ) pe
  let J := values S
  let X := valueObj (τ := τ) (Φ := Φ) pe (packType (S := S) (Bridge.BoundCtx.toThesis β))
  let toUnit : X ⟶ 𝟙_ (ValueCat S) :=
    ⟨mk (S := S) HasType.unit, ⟨.unit, .unit, .unit, rfl⟩⟩
  change J.map (packedEnvIso (Φ := Φ) pe β).inv ≫
    J.map (CartesianMonoidalCategory.toUnit _ ≫ (typeModel (Φ := Φ) pe).unitIso.inv) = J.map toUnit
  rw [← J.map_comp]
  exact congrArg J.map (CartesianMonoidalCategory.toUnit_unique _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem packedNative_let1_eq_packedArrow (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {s : Tm Empty Φ (n + 1)} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A)
    (e : Derivation Φ (Ctx.nil : Ctx Empty τ) (.snoc β A) s B)
    (ha : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) A)
    (hb : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (.snoc (Bridge.BoundCtx.toThesis β) A) (Bridge.toThesis s) B)
    (ih₁ : packedNative pe d = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) ha)
    (ih₂ : packedNative pe e = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) hb) :
    packedNative pe (.let₁ d e) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) (.let₁ ha hb) := by
  rw [packedNative_let1, ih₁, ih₂, packedArrow_let1]
  let S := signature (τ := τ) (Φ := Φ) pe
  let X := valueObj (τ := τ) (Φ := Φ) pe (packType (S := S) (Bridge.BoundCtx.toThesis β))
  let Y := valueObj (τ := τ) (Φ := Φ) pe A
  let Z := valueObj (τ := τ) (Φ := Φ) pe B
  exact @bind_values S X Y Z (packedArrow ha) (packedArrow hb)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem packedNative_inl (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A) :
    packedNative pe (Derivation.inl (B := B) d) =
      packedNative pe d ≫ injl (of (S := signature (τ := τ) (Φ := Φ) pe) A) (of B) := by
  let S := signature (τ := τ) (Φ := Φ) pe
  let J := values S
  let M := typeModel (τ := τ) (Φ := Φ) pe
  let comparison := M.coprodIso A B
  have injection : coprod.inl ≫ comparison.inv =
      (valueCofan (valueObj (Φ := Φ) pe A) (valueObj pe B)).inl := by
    rw [← valueInl_coprodIso pe A B, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  calc
    _ = packedNative pe d ≫ J.map (coprod.inl ≫ comparison.inv) :=
      (Category.assoc _ _ _).symm
    _ = packedNative pe d ≫ injl (of (S := S) A) (of B) :=
      congrArg (fun f => packedNative pe d ≫ J.map f) injection

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem packedNative_inl_eq_packedArrow (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A)
    (h : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) A)
    (ih : packedNative pe d = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) h) :
    packedNative pe (Derivation.inl (B := B) d) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) (HasType.inl (B := B) h) := by
  rw [packedNative_inl pe d, packedArrow_inl h, ih]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem packedNative_inr (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t B) :
    packedNative pe (Derivation.inr (A := A) d) =
      packedNative pe d ≫ injr (of (S := signature (τ := τ) (Φ := Φ) pe) A) (of B) := by
  let S := signature (τ := τ) (Φ := Φ) pe
  let J := values S
  let M := typeModel (τ := τ) (Φ := Φ) pe
  let comparison := M.coprodIso A B
  have injection : coprod.inr ≫ comparison.inv =
      (valueCofan (valueObj (Φ := Φ) pe A) (valueObj pe B)).inr := by
    rw [← valueInr_coprodIso pe A B, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  calc
    _ = packedNative pe d ≫ J.map (coprod.inr ≫ comparison.inv) :=
      (Category.assoc _ _ _).symm
    _ = packedNative pe d ≫ injr (of (S := S) A) (of B) :=
      congrArg (fun f => packedNative pe d ≫ J.map f) injection

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem packedNative_inr_eq_packedArrow (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t B)
    (h : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) B)
    (ih : packedNative pe d = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) h) :
    packedNative pe (Derivation.inr (A := A) d) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) (HasType.inr (A := A) h) := by
  rw [packedNative_inr pe d, packedArrow_inr h, ih]

private theorem retainLeft_values {S : Sig.{u}} {R A B : ValueCat S}
    (f : A.obj ⟶ B.obj) :
    retainLeft (values S) (R := R) f = tensorLeft R.obj f := by
  change 𝟙 _ ≫ leftTensor (𝟙 R.obj) f ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id, leftTensor, id_whiskerRight]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem bind_pair_pure_left {S : Sig.{u}} {X A B : ValueCat S}
    (p : X ⟶ A) (g : X.obj ⟶ B.obj) :
    bindArrow (values S) g ((values S).map (p ▷ B)) = pairArrows p.hom g := by
  let J := values S
  have retain : extend J g = J.map (lift (𝟙 X) (𝟙 X)) ≫ retainLeft J (R := X) g := by
    rw [← extend_map J (𝟙 X)]
    calc
      _ = extend J (𝟙 (J.obj X) ≫ g) := congrArg (extend J) (Category.id_comp g).symm
      _ = extend J (𝟙 (J.obj X)) ≫ retainLeft J g := extend_comp J (𝟙 (J.obj X)) g
      _ = _ := congrArg (fun k => extend J k ≫ retainLeft J g) (J.map_id X).symm
  have diagonal : lift (𝟙 X) (𝟙 X) ≫ (p ▷ X) = lift p (𝟙 X) := by
    apply hom_ext <;> simp
  unfold ProofRelevant.Semantics.Categorical.bind
  rw [retain, Category.assoc, ← retainLeft_pre_map J p g, ← Category.assoc, ← J.map_comp,
    diagonal, retainLeft_values]
  have mapLift : J.map (lift p (𝟙 X)) = pairArrows p.hom (𝟙 X.obj) := valueLift_hom p (𝟙 X)
  rw [mapLift]
  rw [tensorLeft_pair p.property (isPureMor_id _), Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pair_values {S : Sig.{u}} {X A B : ValueCat S}
    (f : X.obj ⟶ A.obj) (g : X.obj ⟶ B.obj) :
    pairArrow (values S) f g = pairArrows f g := by
  let J := values S
  have keepResults : lift (fst (X ⊗ A) B ≫ snd X A) (snd (X ⊗ A) B) = snd X A ▷ B := by
    apply hom_ext <;> simp
  unfold ProofRelevant.Semantics.Categorical.pair ProofRelevant.Semantics.Categorical.retainedContext
  rw [keepResults, bind_pair_pure_left, bind_values]
  exact (pairArrows_seq f g).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem packedNative_pair (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t s : Tm Empty Φ n} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A)
    (e : Derivation Φ (Ctx.nil : Ctx Empty τ) β s B) :
    packedNative pe (.pair d e) = pairArrows (packedNative pe d) (packedNative pe e) := by
  let S := signature (τ := τ) (Φ := Φ) pe
  let J := values S
  let X := valueObj (τ := τ) (Φ := Φ) pe (packType (S := S) (Bridge.BoundCtx.toThesis β))
  let Y := valueObj (τ := τ) (Φ := Φ) pe A
  let Z := valueObj (τ := τ) (Φ := Φ) pe B
  let k := (packedEnvIso (Φ := Φ) pe β).inv
  calc
    _ = J.map k ≫ pairArrow J (denoteInSyntax pe d) (denoteInSyntax pe e) := by
      change J.map k ≫ (pairArrow J (denoteInSyntax pe d) (denoteInSyntax pe e) ≫ 𝟙 _) = _
      rw [Category.comp_id]
    _ = pairArrow J (packedNative pe d) (packedNative pe e) :=
      (pair_pre_map J k (denoteInSyntax pe d) (denoteInSyntax pe e)).symm
    _ = pairArrows (packedNative pe d) (packedNative pe e) :=
      @pair_values S X Y Z (packedNative pe d) (packedNative pe e)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem packedNative_pair_eq_packedArrow (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t s : Tm Empty Φ n} {A B : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t A)
    (e : Derivation Φ (Ctx.nil : Ctx Empty τ) β s B)
    (ha : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis t) A)
    (hb : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis s) B)
    (ih₁ : packedNative pe d = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) ha)
    (ih₂ : packedNative pe e = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) hb) :
    packedNative pe (.pair d e) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) (.pair ha hb) := by
  rw [packedNative_pair pe d e, packedArrow_pair ha hb, ih₁, ih₂]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem packedNative_let2 (pe : ε)
    {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n} {s : Tm Empty Φ (n + 2)} {A B C : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t (product A B))
    (e : Derivation Φ (Ctx.nil : Ctx Empty τ) (.snoc (.snoc β A) B) s C) :
    let S := signature (τ := τ) (Φ := Φ) pe
    let X := of (S := S) (packType (Bridge.BoundCtx.toThesis β))
    packedNative pe (.let₂ d e) =
      pairArrows (𝟙 X) (packedNative pe d) ≫ (tensorAssociator X (of A) (of B)).inv ≫
        packedNative pe e := by
  let S := signature (τ := τ) (Φ := Φ) pe
  let J := values S
  let M := typeModel (τ := τ) (Φ := Φ) pe
  let X := valueObj (τ := τ) (Φ := Φ) pe (packType (S := S) (Bridge.BoundCtx.toThesis β))
  let Y := valueObj (τ := τ) (Φ := Φ) pe A
  let Z := valueObj (τ := τ) (Φ := Φ) pe B
  let W := valueObj (τ := τ) (Φ := Φ) pe C
  let k := (packedEnvIso (Φ := Φ) pe β).inv
  let q := envPairHom M (Ctx.nil : Ctx Empty τ) β A B
  let p := J.map q ≫ denoteInSyntax pe e
  have pairMap : (𝟙 (envObj M (Ctx.nil : Ctx Empty τ) β)) ⊗ₘ (M.productIso A B).hom = 𝟙 _ := by
    change (𝟙 _) ⊗ₘ (𝟙 _) = 𝟙 _
    simp
  have beforeBind : packedNative pe (.let₂ d e) =
      J.map k ≫ bindArrow J (denoteInSyntax pe d) p := by
    change J.map k ≫ bindArrow J (denoteInSyntax pe d)
      (J.map ((𝟙 _) ⊗ₘ (M.productIso A B).hom) ≫ p) = _
    have mapId := (congrArg J.map pairMap).trans (J.map_id _)
    exact congrArg (fun f => J.map k ≫ bindArrow J (denoteInSyntax pe d) f)
      ((congrArg (fun f => f ≫ p) mapId).trans (Category.id_comp p))
  have afterSplit :
      J.map (k ▷ (Y ⊗ Z)) ≫ p =
        J.map (α_ X Y Z).inv ≫ packedNative pe e := by
    unfold p packedNative
    rw [← J.map_comp_assoc, packedEnvInv_pair, J.map_comp, Category.assoc]
  calc
    _ = J.map k ≫ bindArrow J (denoteInSyntax pe d) p := beforeBind
    _ = bindArrow J (packedNative pe d) (J.map (k ▷ (Y ⊗ Z)) ≫ p) :=
      (bind_pre_map J k (denoteInSyntax pe d) p).symm
    _ = bindArrow J (packedNative pe d) (J.map (α_ X Y Z).inv ≫ packedNative pe e) :=
      congrArg (bindArrow J (packedNative pe d)) afterSplit
    _ = _ := @bind_values S X (Y ⊗ Z) W (packedNative pe d)
      (J.map (α_ X Y Z).inv ≫ packedNative pe e)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem route_packed_sum (pe : ε)
    (X : ValueCat (signature (τ := τ) (Φ := Φ) pe)) (A B : τ) :
    let S := signature (τ := τ) (Φ := Φ) pe
    let J := values S
    let Y := valueObj (Φ := Φ) pe A
    let Z := valueObj (Φ := Φ) pe B
    J.map (X ◁ ((typeModel (Φ := Φ) pe).coprodIso A B).hom) ≫ routeEnvironment J X Y Z =
      contextSumSplit X.obj Y.obj Z.obj := by
  let S := signature (τ := τ) (Φ := Φ) pe
  let J := values S
  let Y := valueObj (Φ := Φ) pe A
  let Z := valueObj (Φ := Φ) pe B
  let i := (typeModel (Φ := Φ) pe).coprodIso A B
  let d := DistributivePremonoidalCategory.leftInv X.obj Y.obj Z.obj
  have route : routeEnvironment J X Y Z = tensorLeft X.obj (splitMapCoprod J Y Z) ≫ d := by
    rw [routeEnvironment_tensor_comparison]
    change 𝟙 _ ≫ tensorLeft X.obj (splitMapCoprod J Y Z) ≫ d ≫ coprod.map (𝟙 _) (𝟙 _) = _
    simp
  have comparison : J.map (X ◁ i.hom) = tensorLeft X.obj (J.map i.hom) :=
    (tensorLeft_value (R := X) i.hom).symm
  change J.map (X ◁ i.hom) ≫ routeEnvironment J X Y Z = _
  rw [comparison, route, ← Category.assoc, ← tensorLeft_comp]
  change tensorLeft X.obj (J.map i.hom ≫ inv (coprodComparison J Y Z)) ≫ d = _
  rw [map_coprodIso pe A B]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem case_values (pe : ε)
    (X : ValueCat (signature (τ := τ) (Φ := Φ) pe)) (A B : τ)
    {D : ValueCat (signature (τ := τ) (Φ := Φ) pe)}
    (f : X.obj ⟶ (valueObj (Φ := Φ) pe (Silmaril.coprod A B)).obj)
    (l : (X ⊗ valueObj (Φ := Φ) pe A).obj ⟶ D.obj)
    (r : (X ⊗ valueObj (Φ := Φ) pe B).obj ⟶ D.obj) :
    let S := signature (τ := τ) (Φ := Φ) pe
    let J := values S
    caseWithContext J (f ≫ J.map ((typeModel (Φ := Φ) pe).coprodIso A B).hom) l r =
      pairArrows (𝟙 X.obj) f ≫ contextSumSplit X.obj (of A) (of B) ≫ coprod.desc l r := by
  let S := signature (τ := τ) (Φ := Φ) pe
  let J := values S
  let M := typeModel (τ := τ) (Φ := Φ) pe
  let Y := valueObj (Φ := Φ) pe A
  let Z := valueObj (Φ := Φ) pe B
  let P := valueObj (Φ := Φ) pe (Silmaril.coprod A B)
  let i := (M.coprodIso A B).hom
  let branches : (J.obj (X ⊗ Y) ⨿ J.obj (X ⊗ Z)) ⟶ J.obj D := coprod.desc l r
  calc
    _ = bindArrow J (f ≫ J.map i) (routeEnvironment J X Y Z ≫ branches) := by
      simp only [caseWithContext, routeEnvironment, branches, Category.assoc]
      rfl
    _ = bindArrow J f (J.map (X ◁ i) ≫ routeEnvironment J X Y Z ≫ branches) := by
      unfold ProofRelevant.Semantics.Categorical.bind
      rw [extend_postmap, Category.assoc]
    _ = bindArrow J f (contextSumSplit X.obj Y.obj Z.obj ≫ branches) := by
      rw [← Category.assoc, route_packed_sum pe X A B]
    _ = _ := @bind_values S X P D f (contextSumSplit X.obj Y.obj Z.obj ≫ branches)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem packedNative_case (pe : ε) {n : Nat} {β : BoundCtx τ n}
    {t : Tm Empty Φ n} {l r : Tm Empty Φ (n + 1)} {A B D : τ}
    (d : Derivation Φ (Ctx.nil : Ctx Empty τ) β t (Silmaril.coprod A B))
    (dl : Derivation Φ (Ctx.nil : Ctx Empty τ) (β.snoc A) l D)
    (dr : Derivation Φ (Ctx.nil : Ctx Empty τ) (β.snoc B) r D) :
    let S := signature (τ := τ) (Φ := Φ) pe
    let X := of (S := S) (packType (Bridge.BoundCtx.toThesis β))
    packedNative pe (.case d dl dr) = pairArrows (𝟙 X) (packedNative pe d) ≫
      contextSumSplit X (of A) (of B) ≫ coprod.desc (packedNative pe dl) (packedNative pe dr) := by
  let S := signature (τ := τ) (Φ := Φ) pe
  let J := values S
  let M := typeModel (τ := τ) (Φ := Φ) pe
  let X := valueObj (τ := τ) (Φ := Φ) pe (packType (S := S) (Bridge.BoundCtx.toThesis β))
  let Y := valueObj (τ := τ) (Φ := Φ) pe A
  let Z := valueObj (τ := τ) (Φ := Φ) pe B
  let W := valueObj (τ := τ) (Φ := Φ) pe D
  let k := (packedEnvIso (Φ := Φ) pe β).inv
  let i := (M.coprodIso A B).hom
  let ll := J.map (envSnocIso M (Ctx.nil : Ctx Empty τ) β A).hom ≫ denoteInSyntax pe dl
  let rr := J.map (envSnocIso M (Ctx.nil : Ctx Empty τ) β B).hom ≫ denoteInSyntax pe dr
  have lhs : J.map (k ▷ Y) ≫ ll = packedNative pe dl := by
    unfold ll packedNative
    rw [← J.map_comp_assoc, packedEnvInv_snoc]
  have rhs : J.map (k ▷ Z) ≫ rr = packedNative pe dr := by
    unfold rr packedNative
    rw [← J.map_comp_assoc, packedEnvInv_snoc]
  have transported : packedNative pe (.case d dl dr) =
      caseWithContext J (packedNative pe d ≫ J.map i) (packedNative pe dl) (packedNative pe dr) := by
    change J.map k ≫ caseWithContext J (denoteInSyntax pe d ≫ J.map i) ll rr = _
    rw [← case_pre_map]
    calc
      _ = caseWithContext J (packedNative pe d ≫ J.map i)
          (J.map (k ▷ Y) ≫ ll) (J.map (k ▷ Z) ≫ rr) :=
        congrArg (fun f => caseWithContext J f _ _)
          (Category.assoc (J.map k) (denoteInSyntax pe d) (J.map i)).symm
      _ = _ := congrArg₂ (caseWithContext J (packedNative pe d ≫ J.map i)) lhs rhs
  exact transported.trans (case_values pe X A B (D := W)
    (packedNative pe d) (packedNative pe dl) (packedNative pe dr))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem packedNative_iter (pe : ε) {n : Nat} {β : BoundCtx τ n}
    {a : Tm Empty Φ n} {b : Tm Empty Φ (n + 1)} {A B : τ}
    (da : Derivation Φ (Ctx.nil : Ctx Empty τ) β a A)
    (db : Derivation Φ (Ctx.nil : Ctx Empty τ) (β.snoc A) b (Silmaril.coprod B A)) :
    let S := signature (τ := τ) (Φ := Φ) pe
    let J := values S
    let X := of (S := S) (packType (Bridge.BoundCtx.toThesis β))
    packedNative pe (.iter da db) = pairArrows (𝟙 X) (packedNative pe da) ≫
      contextualLoop J (packedNative pe db ≫ J.map ((typeModel (Φ := Φ) pe).coprodIso B A).hom) := by
  let S := signature (τ := τ) (Φ := Φ) pe
  let J := values S
  let M := typeModel (τ := τ) (Φ := Φ) pe
  let X := valueObj (τ := τ) (Φ := Φ) pe (packType (S := S) (Bridge.BoundCtx.toThesis β))
  let Y := valueObj (Φ := Φ) pe A
  let Z := valueObj (Φ := Φ) pe B
  let k := (packedEnvIso (Φ := Φ) pe β).inv
  let i := (M.coprodIso B A).hom
  let f := J.map (envSnocIso M (Ctx.nil : Ctx Empty τ) β A).hom ≫
    denoteInSyntax pe db ≫ J.map i
  have body : J.map (k ▷ Y) ≫ contextualLoop J f =
      contextualLoop J (packedNative pe db ≫ J.map i) := by
    rw [← contextualLoop_pre_map]
    unfold f packedNative
    rw [← J.map_comp_assoc, packedEnvInv_snoc, Category.assoc]
  calc
    _ = J.map k ≫ bindArrow J (denoteInSyntax pe da) (contextualLoop J f) := rfl
    _ = bindArrow J (packedNative pe da) (J.map (k ▷ Y) ≫ contextualLoop J f) :=
      (bind_pre_map J k (denoteInSyntax pe da) (contextualLoop J f)).symm
    _ = bindArrow J (packedNative pe da) (contextualLoop J (packedNative pe db ≫ J.map i)) :=
      congrArg (bindArrow J (packedNative pe da)) body
    _ = _ := @bind_values S X Y Z (packedNative pe da) _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem contextualLoop_carried (pe : ε) {n : Nat} {β : BoundCtx τ n} {A B : τ}
    {b : Thesis.LambdaIter.LocallyNameless.Tm Empty Φ (n + 1)}
    (hb : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil ((Bridge.BoundCtx.toThesis β).snoc A) b (Silmaril.coprod B A)) :
    let J := values (signature (τ := τ) (Φ := Φ) pe)
    contextualLoop J (packedArrow hb ≫ J.map ((typeModel (Φ := Φ) pe).coprodIso B A).hom) =
      Silmaril.Thesis.LambdaIter.Syn.SynCat.iterate (packedArrow (carriedIterTyping hb)) := by
  let S := signature (τ := τ) (Φ := Φ) pe
  let J := values S
  let α := Bridge.BoundCtx.toThesis β
  let R := valueObj (τ := τ) (Φ := Φ) pe (packType (S := S) α)
  let Y := valueObj (τ := τ) (Φ := Φ) pe A
  let Z := valueObj (τ := τ) (Φ := Φ) pe B
  let W := R ⊗ Y
  let U : ValueCat S := ⟨cop Z.obj W.obj⟩
  let p := fst R Y
  let f := packedArrow (S := S) hb
  let i := ((typeModel (Φ := Φ) pe).coprodIso B A).hom
  let body := f ≫ J.map i
  let out : J.obj (R ⊗ Z) ⟶ J.obj U := J.map (snd R Z) ≫ injl Z.obj W.obj
  let recur : J.obj (R ⊗ Y) ⟶ J.obj U := injr Z.obj W.obj
  let ht := HasType.inl (B := packType (S := S) (α.snoc A))
    (HasType.newest (Φ := S.Instr) (Γ := (Thesis.LambdaIter.Ctx.nil :
      Thesis.LambdaIter.Ctx Empty S.Ty)) (β := α.snoc A) (A := B))
  let hr := HasType.inr (A := B) ((packTermTyping (S := S) (α.snoc A)).underBinder (X := A))
  have exitBranch : packedArrow (S := S) ht = J.map (p ▷ Z) ≫ out := by
    unfold ht out
    rw [packedArrow_inl]
    have proj : packedArrow (S := S) (HasType.newest (β := α.snoc A) (A := B)) = J.map (snd W Z) :=
      packedArrow_bv_zero (S := S) (α.snoc A) B
    calc
      _ = J.map (snd W Z) ≫ injl Z.obj W.obj := congrArg (fun f => f ≫ injl Z.obj W.obj) proj
      _ = _ := by rw [← J.map_comp_assoc, whiskerRight_snd]
  have projectState : J.map (p ▷ Y) =
      pairArrows (first W.obj Y.obj ≫ first R.obj Y.obj) (second W.obj Y.obj) := by
    have eq : p ▷ Y = lift (fst W Y ≫ p) (snd W Y) := by
      apply hom_ext <;> simp [W]
    exact (congrArg J.map eq).trans (valueLift_hom _ _)
  have recurBranch : packedArrow (S := S) hr = J.map (p ▷ Y) ≫ recur := by
    unfold hr recur
    rw [packedArrow_inr, packedArrow_carriedState, projectState]
    rfl
  have step : packedArrow (S := S) (carriedIterTyping hb) =
      contextualStep J body ≫ coprod.desc out recur := by
    change packedArrow (S := S) (.case hb ht hr) = _
    rw [packedArrow_case, exitBranch, recurBranch]
    refine (case_values pe W B A (D := U) f (J.map (p ▷ Z) ≫ out) (J.map (p ▷ Y) ≫ recur)).symm.trans ?_
    calc
      _ = retainEnvironment J p body ≫ routeEnvironment J R Z Y ≫ coprod.desc out recur :=
        caseWithContext_project (E := W) (R := R) (A := Z) (B := Y) J p body out recur
      _ = _ := (Category.assoc (retainEnvironment J p body) (routeEnvironment J R Z Y)
        (coprod.desc out recur)).symm
  have dropExit : coprod.map (J.map (snd R Z)) (𝟙 (J.obj W)) ≫ (copIso Z.obj W.obj).inv =
      coprod.desc out recur := by
    apply coprod.hom_ext
    · rw [← Category.assoc, coprod.inl_map, Category.assoc]
      exact (congrArg (fun f => J.map (snd R Z) ≫ f) (coprod_inl_copIso_inv Z.obj W.obj)).trans
        (coprod.inl_desc out recur).symm
    · rw [← Category.assoc, coprod.inr_map, Category.id_comp]
      exact (coprod_inr_copIso_inv Z.obj W.obj).trans (coprod.inr_desc out recur).symm
  calc
    _ = iterate' (contextualStep J body) ≫ J.map (snd R Z) := by
      simp only [contextualLoop, contextualStep, retainEnvironment, routeEnvironment, Category.assoc]
      rfl
    _ = iterate' (contextualStep J body ≫ coprod.map (J.map (snd R Z)) (𝟙 (J.obj W))) :=
      iterate'_naturality _ _
    _ = Silmaril.Thesis.LambdaIter.Syn.SynCat.iterate (contextualStep J body ≫ coprod.desc out recur) := by
      unfold iterate'
      rw [Category.assoc]
      exact congrArg (fun f => Silmaril.Thesis.LambdaIter.Syn.SynCat.iterate
        (contextualStep J body ≫ f)) dropExit
    _ = _ := congrArg Silmaril.Thesis.LambdaIter.Syn.SynCat.iterate step.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem packedNative_iter_eq_packedArrow (pe : ε) {n : Nat} {β : BoundCtx τ n}
    {a : Tm Empty Φ n} {b : Tm Empty Φ (n + 1)} {A B : τ}
    (da : Derivation Φ (Ctx.nil : Ctx Empty τ) β a A)
    (db : Derivation Φ (Ctx.nil : Ctx Empty τ) (β.snoc A) b (Silmaril.coprod B A))
    (ha : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil (Bridge.BoundCtx.toThesis β) (Bridge.toThesis a) A)
    (hb : HasType (signature (τ := τ) (Φ := Φ) pe).Instr
      .nil ((Bridge.BoundCtx.toThesis β).snoc A) (Bridge.toThesis b) (Silmaril.coprod B A))
    (iha : packedNative pe da = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) ha)
    (ihb : packedNative pe db = packedArrow (S := signature (τ := τ) (Φ := Φ) pe) hb) :
    packedNative pe (.iter da db) =
      packedArrow (S := signature (τ := τ) (Φ := Φ) pe) (.iter ha hb) := by
  rw [packedNative_iter pe da db, packedArrow_iter_state ha hb, iha, ihb, contextualLoop_carried pe hb]

end Silmaril.Isotope.LetIter.Semantics.Categorical.Syntactic.PackingProofs
