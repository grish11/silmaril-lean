module

public import Silmaril.SSA.Isotope.LetIter.Counterexample.Defs
import Silmaril.SSA.Isotope.Bridge.Defs
import Silmaril.SSA.Isotope.LetIter.Categorical.LetEta.Thms
import Silmaril.Semantics.ElgotMonads.Thms
import Mathlib.GroupTheory.Perm.Basic

/-! # Twisted writer interpretation of let-η -/

public section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend)
open CategoryTheory.PremonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.WriterCounterexample

private abbrev W := Equiv.Perm (Fin 3)
private abbrev M := WriterT W Part
private abbrev T := ofTypeMonad M
private abbrev C := Kleisli T
private abbrev J := Kleisli.Adjunction.toKleisli T

private noncomputable def logged {X Y : C} (w : W) (f : X.of → Y.of) : X ⟶ Y :=
  Kleisli.Hom.mk (TypeCat.ofHom (fun x => WriterT.mk (Part.some (f x, w))))

@[simp] private theorem logged_comp {X Y Z : C}
    (u v : W) (f : X.of → Y.of) (g : Y.of → Z.of) :
    logged u f ≫ logged v g = logged (u * v) (g ∘ f) := by
  apply Kleisli.hom_ext
  apply ConcreteCategory.coe_ext
  rw [Kleisli.Type.comp_of_eq_kleisliRight]
  funext x
  apply WriterT.ext
  change (Part.some (f x, u) >>= fun p => (fun q => (q.1, p.2 * q.2)) <$>
      Part.some (g p.1, v)) = Part.some (g (f x), u * v)
  simp

@[simp] private theorem map_logged {X Y : Type} (f : X ⟶ Y) :
    J.map f = logged 1 f := rfl

@[simp] private theorem id_logged (X : C) : 𝟙 X = logged 1 id := rfl

@[simp] private theorem left_logged (X : C) {Y Z : C} (w : W) (f : Y.of → Z.of) :
    X ◁ logged w f = logged w (fun (p : X.of × Y.of) => (p.1, f p.2)) := by
  apply Kleisli.hom_ext
  apply ConcreteCategory.coe_ext
  funext x
  apply WriterT.ext
  rfl

@[simp] private theorem right_logged {X Y : C} (Z : C) (w : W) (f : X.of → Y.of) :
    logged w f ▷ Z = logged w (fun (p : X.of × Z.of) => (f p.1, p.2)) := by
  apply Kleisli.hom_ext
  apply ConcreteCategory.coe_ext
  funext x
  apply WriterT.ext
  rfl

private noncomputable def effectIso (X : C) (w : W) : X ≅ X where
  hom := logged w id
  inv := logged w⁻¹ id
  hom_inv_id := by simp
  inv_hom_id := by simp

@[instance_reducible] private noncomputable def twistedStrong (w : W) : Functor.StrongPremonoidal J where
  unitIso := effectIso _ w
  tensorIso X Y := effectIso (J.obj (X ⊗ Y)) w⁻¹
  tensor_naturality_left f Z := by
    simp only [effectIso, map_logged, right_logged, logged_comp, one_mul, mul_one, Function.comp_def, id]
    rfl
  tensor_naturality_right X _ _ f := by
    simp only [effectIso, map_logged, left_logged, logged_comp, one_mul, mul_one, Function.comp_def, id]
    rfl
  associativity X Y Z := by
    change J.map (α_ X Y Z).hom ≫ _ = _
    simp [effectIso, Function.comp_def]
  left_unitality X := by
    change _ = J.map (λ_ X).hom
    simp [effectIso, Function.comp_def]
  right_unitality X := by
    change _ = J.map (ρ_ X).hom
    simp [effectIso, Function.comp_def]
  map_central := fun f => Kleisli.toKleisli_map_isCentral T f

@[instance_reducible] private noncomputable def twistedFreyd (w : W) : FreydCategory J where
  toStrongPremonoidal := twistedStrong w
  braiding X Y := by
    change _ = J.map (BraidedCategory.braiding X Y).hom ≫ _
    simp [twistedStrong, effectIso, Function.comp_def]
  obj_bijective := FreydCategory.obj_bijective (J := J)

@[instance_reducible] private noncomputable def twistedElgot (w : W) : StrongElgotFreydCategory J :=
  { (inferInstance : StrongElgotFreydCategory J) with
    toFreydCategory := twistedFreyd w }

private theorem leftTensor_id_first {D : Type*} [Category D] [PremonoidalCategory D]
    (R : D) {X Y : D} (f : X ⟶ Y) : leftTensor (𝟙 R) f = R ◁ f := by
  simp only [leftTensor, PremonoidalCategory.id_whiskerRight, Category.id_comp]

private theorem logged_bind_drop {R A : Type} (u v : W) (f : R → A) :
    let _ : FreydCategory J := twistedFreyd u
    extend J (logged (X := J.obj R) (Y := J.obj A) v f) ≫
      J.map (CartesianMonoidalCategory.snd R A) = logged (u * v * u⁻¹) f := by
  let _ : FreydCategory J := twistedFreyd u
  dsimp only
  change (J.map (Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.duplicate R) ≫
    (effectIso _ u⁻¹).inv ≫ leftTensor (𝟙 (J.obj R)) (logged v f) ≫
    (effectIso _ u⁻¹).hom) ≫ J.map (CartesianMonoidalCategory.snd R A) = _
  erw [leftTensor_id_first]
  simp only [effectIso, map_logged, left_logged, logged_comp, inv_inv, one_mul, mul_one]
  rfl

section ExactLet

open Silmaril.Isotope.LetIter.LocallyNameless

local instance : Silmaril.TypeFormers Type where
  product := Prod
  unit := PUnit
  coprod := Sum
  empty := Empty

local instance : Silmaril.HasTy PUnit.{1} Type where
  src _ := PUnit
  trg _ := PUnit

local instance : Silmaril.HasEff PUnit.{1} Bool where
  eff _ := true

@[instance_reducible] private noncomputable def typesModel : TypeModel Type Type where
  obj := id
  productIso _ _ := Iso.refl _
  unitIso := Iso.refl _
  coprodIso A B := (Types.binaryCoproductIso A B).symm
  emptyIsInitial := IsInitial.ofUniqueHom (fun _ => ↾Empty.elim)
    (fun X f => by ext x; exact x.elim)

@[instance_reducible] private noncomputable def emit (v : W) : InstructionModel J typesModel PUnit.{1} where
  denote _ := logged v id

private abbrev Γempty : Silmaril.Isotope.Ctx Empty Type := .nil

private def primitive :
    Derivation PUnit.{1} Γempty .nil (.op (PUnit.unit : PUnit.{1}) .unit) (PUnit : Type) :=
  .op .unit

private def newestVar :
    Derivation PUnit.{1} Γempty (.snoc .nil PUnit) (.bv 0) (PUnit : Type) :=
  .bv

set_option maxHeartbeats 600000 in
private theorem exact_letEta_can_fail {u v : W} (hne : u * v * u⁻¹ ≠ v) :
    let _ : StrongElgotFreydCategory J := twistedElgot u
    let _ : InstructionModel J typesModel PUnit.{1} := emit v
    Silmaril.Isotope.LetIter.LocallyNameless.Equiv false Γempty .nil (.let₁ (.op (PUnit.unit : PUnit.{1}) .unit) (.bv 0))
      (.op (PUnit.unit : PUnit.{1}) .unit) (PUnit : Type) ∧
    denote J typesModel (.let₁ primitive newestVar) ≠ denote J typesModel primitive := by
  let _ : StrongElgotFreydCategory J := twistedElgot u
  let _ : FreydCategory J := twistedFreyd u
  let _ : InstructionModel J typesModel PUnit.{1} := emit v
  dsimp only
  refine ⟨Silmaril.Isotope.LetIter.LocallyNameless.Equiv.letEta primitive.toHasType, ?_⟩
  let R := envObj typesModel Γempty .nil
  let f : J.obj R ⟶ J.obj PUnit := logged v (fun _ => PUnit.unit)
  have hprimitive : denote J typesModel primitive = f := by
    change J.map (CartesianMonoidalCategory.toUnit R ≫ typesModel.unitIso.inv) ≫ logged v id = _
    simp only [map_logged, logged_comp, one_mul]
    rfl
  have continuation : J.map (envSnocIso typesModel Γempty .nil PUnit).hom ≫
      denote J typesModel newestVar = J.map (CartesianMonoidalCategory.snd R PUnit) := by
    have var : denote J typesModel newestVar =
        J.map (boundVar typesModel (Γ := Γempty) (β := .snoc .nil PUnit) (0 : Fin 1)) := rfl
    rw [var, ← J.map_comp]
    rfl
  have hlet : denote J typesModel (.let₁ primitive newestVar) =
      extend J f ≫ J.map (CartesianMonoidalCategory.snd R PUnit) := by
    rw [denote, hprimitive, continuation]
    rfl
  have hcomputed : extend J f ≫ J.map (CartesianMonoidalCategory.snd R PUnit) =
      logged (u * v * u⁻¹) (fun _ => PUnit.unit) :=
    logged_bind_drop (R := R) (A := PUnit) u v (fun _ => PUnit.unit)
  rw [hlet, hcomputed, hprimitive]
  intro h
  have hlog : (Part.some (PUnit.unit, u * v * u⁻¹) : Part (PUnit × W)) =
      Part.some (PUnit.unit, v) :=
    congrArg (fun g : J.obj R ⟶ J.obj PUnit => (g.of (PUnit.unit, PUnit.unit)).run) h
  exact hne (congrArg Prod.snd (Part.some_inj.mp hlog))

private def swap01 : W := Equiv.swap 0 1
private def swap12 : W := Equiv.swap 1 2

private theorem effect_changes : swap01 * swap12 * swap01⁻¹ ≠ swap12 := by
  intro h
  have he := congrArg (fun x : W => x 0) h
  have hleft : (swap01 * swap12 * swap01⁻¹) 0 = 2 := rfl
  have hright : swap12 0 = 0 := rfl
  rw [hleft, hright] at he
  exact (by decide : (2 : Fin 3) ≠ 0) he

theorem closedLetEtaUnsound_proof : ¬ ClosedLetEtaSound := by
  intro sound
  let _ : StrongElgotFreydCategory J := twistedElgot swap01
  let _ : InstructionModel J typesModel PUnit.{1} := emit swap12
  exact (exact_letEta_can_fail effect_changes).2 (sound J typesModel primitive)

/-- The same comparison used in the old soundness counterexample fails the
central-unit refinement. -/
private theorem twistedWriterUnitNotCentral :
    let _ : StrongElgotFreydCategory J := twistedElgot swap01
    let _ : FreydCategory J := twistedFreyd swap01
    ¬ FreydCategory.CentralUnit J := by
  let _ : StrongElgotFreydCategory J := twistedElgot swap01
  let _ : FreydCategory J := twistedFreyd swap01
  let _ : InstructionModel J typesModel PUnit.{1} := emit swap12
  change ¬ FreydCategory.CentralUnit J
  intro h
  exact (exact_letEta_can_fail effect_changes).2
    (denote_let_eta J typesModel h.unit_central primitive)

end ExactLet

end Silmaril.Isotope.LetIter.Semantics.Categorical.WriterCounterexample
