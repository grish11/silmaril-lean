module

import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms
public import Silmaril.SSA.Isotope.LetIter.Counterexample.Diagonal.Defs
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# A Freyd countermodel with a central unit

Value maps preserve two distinguished points. Computation maps also accumulate a signed
charge on their codomain. Whiskering places a charge at the base point in the fixed coordinate.
The tensor comparison has a mixed charge with zero marginals. A sign-reversing computation
detects this charge in diagonal exchange and in contextual bind associativity.
-/

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open CategoryTheory.PremonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true
noncomputable section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical.CentralUnitDiagonal

public structure Value where
  carrier : Type
  base : carrier
  mark : carrier

public structure ValueHom (X Y : Value) where
  run : X.carrier → Y.carrier
  base : run X.base = Y.base
  mark : run X.mark = Y.mark

@[ext] theorem ValueHom.ext {X Y : Value} {f g : ValueHom X Y} (h : f.run = g.run) : f = g := by
  cases f
  cases g
  cases h
  rfl

public instance : Category Value where
  Hom := ValueHom
  id _ := ⟨id, rfl, rfl⟩
  comp f g := ⟨g.run ∘ f.run,
    by simp only [Function.comp_apply, f.base, g.base],
    by simp only [Function.comp_apply, f.mark, g.mark]⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem valueId (X : Value) : ValueHom.run (𝟙 X) = id := rfl
@[simp] theorem valueComp {X Y Z : Value} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ValueHom.run (f ≫ g) = g.run ∘ f.run := rfl

abbrev unit : Value := ⟨Unit, (), ()⟩

abbrev product (X Y : Value) : Value := ⟨X.carrier × Y.carrier, (X.base, Y.base), (X.mark, Y.mark)⟩

def fst (X Y : Value) : product X Y ⟶ X := ⟨Prod.fst, rfl, rfl⟩

def snd (X Y : Value) : product X Y ⟶ Y := ⟨Prod.snd, rfl, rfl⟩

def pair {X Y Z : Value} (f : Z ⟶ X) (g : Z ⟶ Y) : Z ⟶ product X Y :=
  ⟨fun z => (f.run z, g.run z), by rw [f.base, g.base], by rw [f.mark, g.mark]⟩

abbrev terminalCone : LimitCone (Functor.empty.{0} Value) :=
  ⟨asEmptyCone unit, IsTerminal.ofUniqueHom (fun _ => ⟨fun _ => (), rfl, rfl⟩) (by
    intro Y f
    apply ValueHom.ext
    funext x
    cases f.run x
    rfl)⟩

abbrev productCone (X Y : Value) : LimitCone (Limits.pair X Y) :=
  ⟨BinaryFan.mk (fst X Y) (snd X Y), BinaryFan.isLimitMk
    (fun s => pair s.fst s.snd) (fun _ => rfl) (fun _ => rfl) (by
      intro s m h₁ h₂
      apply ValueHom.ext
      funext z
      exact Prod.ext (congrFun (congrArg ValueHom.run h₁) z)
        (congrFun (congrArg ValueHom.run h₂) z))⟩

instance : CartesianMonoidalCategory Value :=
  .ofChosenFiniteProducts terminalCone productCone

instance : BraidedCategory Value := .ofCartesianMonoidalCategory

@[simp] theorem valueTensor {X Y X' Y' : Value} (f : X ⟶ X') (g : Y ⟶ Y') :
    ValueHom.run (f ⊗ₘ g) = fun p => (f.run p.1, g.run p.2) := rfl

@[simp] theorem valueLeft (X : Value) {Y Y' : Value} (g : Y ⟶ Y') :
    ValueHom.run (X ◁ g) = fun p => (p.1, g.run p.2) := rfl

@[simp] theorem valueRight {X X' : Value} (f : X ⟶ X') (Y : Value) :
    ValueHom.run (f ▷ Y) = fun p => (f.run p.1, p.2) := rfl

@[simp] theorem valueAssoc (X Y Z : Value) :
    ValueHom.run (α_ X Y Z).hom = fun p => (p.1.1, p.1.2, p.2) := rfl

@[simp] theorem valueAssocInv (X Y Z : Value) :
    ValueHom.run (α_ X Y Z).inv = fun p => ((p.1, p.2.1), p.2.2) := rfl

@[simp] theorem valueUnitLeft (Y : Value) : ValueHom.run (λ_ Y).hom = Prod.snd := rfl
@[simp] theorem valueUnitRight (X : Value) : ValueHom.run (ρ_ X).hom = Prod.fst := rfl

@[simp] theorem valueSwap (X Y : Value) :
    ValueHom.run (BraidedCategory.braiding X Y).hom = Prod.swap := rfl

structure Computation where
  value : Value

abbrev Charge (X : Value) := FreeAbelianGroup X.carrier
abbrev push {X Y : Type} (f : X → Y) := FreeAbelianGroup.map f

def signAction {A : Type} [AddGroup A] (s : Bool) (p : A) : A := if s then -p else p

@[simp] theorem signFalse {A : Type} [AddGroup A] (p : A) :
    signAction false p = p := rfl

@[simp] theorem signZero {A : Type} [AddGroup A] (s : Bool) :
    signAction s (0 : A) = 0 := by cases s <;> simp [signAction]

@[simp] theorem signPlus {A : Type} [AddCommGroup A] (s : Bool) (p q : A) :
    signAction s (p + q) = signAction s p + signAction s q := by
  cases s <;> simp [signAction, add_comm]

@[simp] theorem signXor {A : Type} [AddCommGroup A] (s t : Bool) (p : A) :
    signAction s (signAction t p) = signAction (s ^^ t) p := by
  cases s <;> cases t <;> simp [signAction]

@[simp] theorem pushSign {X Y : Type} (f : X → Y) (s : Bool) (p : FreeAbelianGroup X) :
    push f (signAction s p) = signAction s (push f p) := by
  cases s <;> simp [signAction]

structure EffectHom (X Y : Computation) where
  value : X.value ⟶ Y.value
  charge : Charge Y.value
  sign : Bool

@[ext] theorem EffectHom.ext {X Y : Computation} {f g : EffectHom X Y}
    (hv : f.value = g.value) (hc : f.charge = g.charge) (hs : f.sign = g.sign) : f = g := by
  cases f
  cases g
  cases hv
  cases hc
  cases hs
  rfl

def compose {X Y Z : Computation} (f : EffectHom X Y) (g : EffectHom Y Z) : EffectHom X Z :=
  ⟨f.value ≫ g.value, push g.value.run f.charge + signAction f.sign g.charge, f.sign ^^ g.sign⟩

@[instance_reducible] def computationCategory : Category Computation where
  Hom := EffectHom
  id _ := ⟨𝟙 _, 0, false⟩
  comp := compose
  id_comp f := by cases f; simp [compose]
  comp_id f := by cases f; simp [compose, FreeAbelianGroup.map_id_apply]
  assoc f g h := by
    apply EffectHom.ext
    · rfl
    · simp [compose, FreeAbelianGroup.map_comp_apply, add_assoc]
    · simp [compose]

local instance : Category Computation := computationCategory

abbrev J : Value ⥤ Computation where
  obj X := ⟨X⟩
  map f := ⟨f, 0, false⟩
  map_comp f g := by
    apply EffectHom.ext
    · rfl
    · change 0 = push g.run 0 + signAction false 0
      simp
    · rfl

@[simp] theorem effectCompValue {X Y Z : Computation} (f : X ⟶ Y) (g : Y ⟶ Z) :
    EffectHom.value (f ≫ g) = f.value ≫ g.value := rfl

@[simp] theorem effectCompCharge {X Y Z : Computation} (f : X ⟶ Y) (g : Y ⟶ Z) :
    EffectHom.charge (f ≫ g) = push g.value.run f.charge + signAction f.sign g.charge := rfl

@[simp] theorem effectCompSign {X Y Z : Computation} (f : X ⟶ Y) (g : Y ⟶ Z) :
    EffectHom.sign (f ≫ g) = (f.sign ^^ g.sign) := rfl

@[simp] theorem pushPush {X Y Z : Type} (f : X → Y) (g : Y → Z) (a : FreeAbelianGroup X) :
    push g (push f a) = push (g ∘ f) a :=
  (FreeAbelianGroup.map_comp_apply a).symm

abbrev cp (X Y : Computation) : Computation := ⟨X.value ⊗ Y.value⟩

def pureArrow {X Y : Computation} (f : X.value ⟶ Y.value) : X ⟶ Y := ⟨f, 0, false⟩

@[simp] theorem pureValue {X Y : Computation} (f : X.value ⟶ Y.value) :
    EffectHom.value (pureArrow (X := X) (Y := Y) f) = f := rfl
@[simp] theorem pureCharge {X Y : Computation} (f : X.value ⟶ Y.value) :
    EffectHom.charge (pureArrow (X := X) (Y := Y) f) = 0 := rfl
@[simp] theorem pureSign {X Y : Computation} (f : X.value ⟶ Y.value) :
    EffectHom.sign (pureArrow (X := X) (Y := Y) f) = false := rfl

@[simp] theorem mapPure {X Y : Value} (f : X ⟶ Y) :
    J.map f = pureArrow f := rfl

@[simp] theorem pureId (X : Computation) : pureArrow (X := X) (Y := X) (𝟙 X.value) = 𝟙 X := rfl

@[simp] theorem pureComp {X Y Z : Computation} (f : X.value ⟶ Y.value) (g : Y.value ⟶ Z.value) :
    pureArrow (X := X) (Y := Y) f ≫ pureArrow (Y := Z) g = pureArrow (f ≫ g) := by
  apply EffectHom.ext
  · rfl
  · simp
  · rfl

def wl (X : Computation) {Y Z : Computation} (f : Y ⟶ Z) : cp X Y ⟶ cp X Z :=
  ⟨X.value ◁ f.value, push (fun z => (X.value.base, z)) f.charge, f.sign⟩

def wr {X Y : Computation} (f : X ⟶ Y) (Z : Computation) : cp X Z ⟶ cp Y Z :=
  ⟨f.value ▷ Z.value, push (fun y => (y, Z.value.base)) f.charge, f.sign⟩

@[simp] theorem wlPure (X : Computation) {Y Z : Computation} (f : Y.value ⟶ Z.value) :
    wl X (pureArrow (X := Y) (Y := Z) f) = pureArrow (X.value ◁ f) := by
  apply EffectHom.ext
  · rfl
  · simp [wl]
  · rfl

@[simp] theorem wrPure {X Y : Computation} (f : X.value ⟶ Y.value) (Z : Computation) :
    wr (pureArrow (X := X) (Y := Y) f) Z = pureArrow (f ▷ Z.value) := by
  apply EffectHom.ext
  · rfl
  · simp [wr]
  · rfl

abbrev structureData : MonoidalCategoryStruct Computation where
  tensorObj := cp
  whiskerLeft := wl
  whiskerRight := wr
  tensorHom {_ Y X' _} f g := wr f X' ≫ wl Y g
  tensorUnit := J.obj (𝟙_ Value)
  associator X Y Z := J.mapIso (α_ X.value Y.value Z.value)
  leftUnitor X := J.mapIso (λ_ X.value)
  rightUnitor X := J.mapIso (ρ_ X.value)

local instance : MonoidalCategoryStruct Computation := structureData

@[simp] theorem ctLeft (X : Computation) {Y Z : Computation} (f : Y ⟶ Z) : X ◁ f = wl X f := rfl
@[simp] theorem ctRight {X Y : Computation} (f : X ⟶ Y) (Z : Computation) : f ▷ Z = wr f Z := rfl
@[simp] theorem assocPure (X Y Z : Computation) :
    (α_ X Y Z).hom = pureArrow (α_ X.value Y.value Z.value).hom := rfl
@[simp] theorem assocInvPure (X Y Z : Computation) :
    (α_ X Y Z).inv = pureArrow (α_ X.value Y.value Z.value).inv := rfl
@[simp] theorem lunitPure (X : Computation) : (λ_ X).hom = pureArrow (λ_ X.value).hom := rfl
@[simp] theorem runitPure (X : Computation) : (ρ_ X).hom = pureArrow (ρ_ X.value).hom := rfl

theorem pureCentral {X Y : Computation} (f : X.value ⟶ Y.value) : IsCentral (pureArrow f) := by
  constructor <;> intro X' Y' g
  · apply EffectHom.ext
    · change (f ▷ X'.value) ≫ (Y.value ◁ g.value) = (X.value ◁ g.value) ≫ (f ▷ Y'.value)
      exact (MonoidalCategory.whisker_exchange f g.value).symm
    · simp [leftTensor, rightTensor, wl, wr]
      change push (fun z => (Y.value.base, z)) g.charge =
        push (fun p : X.value.carrier × Y'.value.carrier => (f.run p.1, p.2))
          (push (fun z => (X.value.base, z)) g.charge)
      rw [pushPush]
      simp [Function.comp_def, f.base]
    · simp [leftTensor, rightTensor, wl, wr]
  · apply EffectHom.ext
    · change (g.value ▷ X.value) ≫ (Y'.value ◁ f) = (X'.value ◁ f) ≫ (g.value ▷ Y.value)
      exact (MonoidalCategory.whisker_exchange g.value f).symm
    · simp [leftTensor, rightTensor, wl, wr]
      change push (fun p : Y'.value.carrier × X.value.carrier => (p.1, f.run p.2))
        (push (fun y => (y, X.value.base)) g.charge) =
        push (fun y => (y, Y.value.base)) g.charge
      rw [pushPush]
      simp [Function.comp_def, f.base]
    · simp [leftTensor, rightTensor, wl, wr]

@[instance_reducible] def premonoidal : PremonoidalCategory Computation where
  toMonoidalCategoryStruct := structureData
  tensorHom_def _ _ := rfl
  whiskerLeft_id X Y := by
    change wl X (pureArrow (𝟙 Y.value)) = 𝟙 _
    rw [wlPure, MonoidalCategory.whiskerLeft_id, pureId]
  whiskerLeft_comp X {Y Z W} f g := by
    apply EffectHom.ext
    · exact MonoidalCategory.whiskerLeft_comp _ _ _
    · simp [wl]
      change push (fun x => (X.value.base, g.value.run x)) f.charge =
        push (fun p : X.value.carrier × Z.value.carrier => (p.1, g.value.run p.2))
          (push (fun z => (X.value.base, z)) f.charge)
      rw [pushPush]
      rfl
    · rfl
  id_whiskerRight X Y := by
    change wr (pureArrow (𝟙 X.value)) Y = 𝟙 _
    rw [wrPure, MonoidalCategory.id_whiskerRight, pureId]
  comp_whiskerRight {_ Y _} f g Z := by
    apply EffectHom.ext
    · exact MonoidalCategory.comp_whiskerRight _ _ _
    · simp [wr]
      change push (fun x => (g.value.run x, Z.value.base)) f.charge =
        push (fun p : Y.value.carrier × Z.value.carrier => (g.value.run p.1, p.2))
          (push (fun y => (y, Z.value.base)) f.charge)
      rw [pushPush]
      rfl
    · rfl
  associator_central X Y Z := pureCentral (α_ X.value Y.value Z.value).hom
  leftUnitor_central X := pureCentral (λ_ X.value).hom
  rightUnitor_central X := pureCentral (ρ_ X.value).hom
  associator_naturality_left {_ Y} f Z W := by
    apply EffectHom.ext
    · exact MonoidalCategory.associator_naturality_left _ _ _
    · simp [wr]
      change push (fun p : (Y.value.carrier × Z.value.carrier) × W.value.carrier =>
        (p.1.1, p.1.2, p.2)) (push (fun p => (p, W.value.base))
          (push (fun y => (y, Z.value.base)) f.charge)) =
        push (fun y => (y, Z.value.base, W.value.base)) f.charge
      simp only [pushPush]
      rfl
    · simp [wr]
  associator_naturality_middle X {_ Z} f W := by
    apply EffectHom.ext
    · exact MonoidalCategory.associator_naturality_middle _ _ _
    · simp [wl, wr]
      change push (fun p : (X.value.carrier × Z.value.carrier) × W.value.carrier =>
        (p.1.1, p.1.2, p.2)) (push (fun p => (p, W.value.base))
          (push (fun z => (X.value.base, z)) f.charge)) =
        push (fun p => (X.value.base, p)) (push (fun z => (z, W.value.base)) f.charge)
      simp only [pushPush]
      rfl
    · simp [wl, wr]
  associator_naturality_right X Y {_ W} f := by
    apply EffectHom.ext
    · exact MonoidalCategory.associator_naturality_right _ _ _
    · simp [wl]
      change push (fun p : (X.value.carrier × Y.value.carrier) × W.value.carrier =>
        (p.1.1, p.1.2, p.2)) (push (fun w => ((X.value.base, Y.value.base), w)) f.charge) =
        push (fun p => (X.value.base, p)) (push (fun w => (Y.value.base, w)) f.charge)
      simp only [pushPush]
      rfl
    · simp [wl]
  leftUnitor_naturality {_ _} f := by
    apply EffectHom.ext
    · exact MonoidalCategory.leftUnitor_naturality _
    · simp [wl]
      change push Prod.snd (push (fun z => ((), z)) f.charge) = f.charge
      rw [pushPush]
      exact FreeAbelianGroup.map_id_apply _
    · simp [wl]
  rightUnitor_naturality {_ _} f := by
    apply EffectHom.ext
    · exact MonoidalCategory.rightUnitor_naturality _
    · simp [wr]
      change push Prod.fst (push (fun y => (y, ())) f.charge) = f.charge
      rw [pushPush]
      exact FreeAbelianGroup.map_id_apply _
    · simp [wr]
  pentagon W X Y Z := by
    simp only [MonoidalCategory.Pentagon, assocPure, ctRight, ctLeft, wrPure, wlPure, pureComp]
    exact congrArg pureArrow (MonoidalCategory.pentagon W.value X.value Y.value Z.value)
  triangle X Y := by
    simp only [assocPure, lunitPure, runitPure, ctRight, ctLeft, wrPure, wlPure, pureComp]
    exact congrArg pureArrow (MonoidalCategory.triangle X.value Y.value)


local instance : PremonoidalCategory Computation := premonoidal

abbrev swapIso (X Y : Computation) : X ⊗ Y ≅ Y ⊗ X :=
  J.mapIso (BraidedCategory.braiding X.value Y.value)

@[simp] theorem swapPure (X Y : Computation) :
    (swapIso X Y).hom = pureArrow (BraidedCategory.braiding X.value Y.value).hom := rfl

abbrev symmetric : SymmetricPremonoidalCategory Computation where
  braiding := swapIso
  naturality_left f Z := by
    change wr f Z ≫ (swapIso _ _).hom = (swapIso _ _).hom ≫ wl Z f
    apply EffectHom.ext
    · exact BraidedCategory.braiding_naturality_left f.value Z.value
    · simp [wr, wl]
      change push Prod.swap (push (fun y => (y, Z.value.base)) f.charge) =
        push (fun y => (Z.value.base, y)) f.charge
      rw [pushPush]
      rfl
    · simp [wr, wl]
  naturality_right X {_ _} f := by
    change wl X f ≫ (swapIso _ _).hom = (swapIso _ _).hom ≫ wr f X
    apply EffectHom.ext
    · exact BraidedCategory.braiding_naturality_right X.value f.value
    · simp [wr, wl]
      change push Prod.swap (push (fun y => (X.value.base, y)) f.charge) =
        push (fun y => (y, X.value.base)) f.charge
      rw [pushPush]
      rfl
    · simp [wr, wl]
  hexagon_forward X Y Z := by
    simp only [assocPure, swapPure, ctLeft, ctRight, wlPure, wrPure, pureComp]
    exact congrArg pureArrow (BraidedCategory.hexagon_forward X.value Y.value Z.value)
  hexagon_reverse X Y Z := by
    simp only [assocInvPure, swapPure, ctLeft, ctRight, wlPure, wrPure, pureComp]
    exact congrArg pureArrow (BraidedCategory.hexagon_reverse X.value Y.value Z.value)
  braiding_central X Y := pureCentral (BraidedCategory.braiding X.value Y.value).hom
  symmetry X Y := by
    simp only [swapPure, pureComp, SymmetricCategory.symmetry]
    exact pureId (X ⊗ Y)

local instance : SymmetricPremonoidalCategory Computation := symmetric

abbrev atom {A : Type} (x : A) := FreeAbelianGroup.of x

/-- A mixed charge whose two marginals vanish. -/
def tensorCharge (X Y : Value) : Charge (X ⊗ Y) :=
  atom (X.mark, Y.mark) - atom (X.mark, Y.base) - atom (X.base, Y.mark) + atom (X.base, Y.base)

@[simp] theorem baseProduct (X Y : Value) : (X ⊗ Y).base = (X.base, Y.base) := rfl
@[simp] theorem markProduct (X Y : Value) : (X ⊗ Y).mark = (X.mark, Y.mark) := rfl
@[simp] theorem baseUnit : (𝟙_ Value).base = () := rfl
@[simp] theorem markUnit : (𝟙_ Value).mark = () := rfl

def scalarIso (X : Computation) (charge : Charge X.value) : X ≅ X where
  hom := ⟨𝟙 _, charge, false⟩
  inv := ⟨𝟙 _, -charge, false⟩
  hom_inv_id := by
    apply EffectHom.ext
    · exact Category.comp_id _
    · change push id charge + signAction false (-charge) = 0
      simp [FreeAbelianGroup.map_id_apply]
    · rfl
  inv_hom_id := by
    apply EffectHom.ext
    · exact Category.comp_id _
    · change push id (-charge) + signAction false charge = 0
      simp [FreeAbelianGroup.map_id_apply]
    · rfl

@[simp] theorem scalarHomCharge (X : Computation) (charge : Charge X.value) :
    (scalarIso X charge).hom.charge = charge := rfl
@[simp] theorem scalarHomValue (X : Computation) (charge : Charge X.value) :
    (scalarIso X charge).hom.value = 𝟙 X.value := rfl
@[simp] theorem scalarHomSign (X : Computation) (charge : Charge X.value) :
    (scalarIso X charge).hom.sign = false := rfl

abbrev strong : Functor.StrongPremonoidal J where
  unitIso := Iso.refl _
  tensorIso X Y := scalarIso (J.obj (X ⊗ Y)) (tensorCharge X Y)
  tensor_naturality_left {X Y} f Z := by
    apply EffectHom.ext
    · change (f ▷ Z) ≫ 𝟙 (Y ⊗ Z) = 𝟙 (X ⊗ Z) ≫ (f ▷ Z)
      rw [Category.comp_id, Category.id_comp]
    · simp [wr, tensorCharge, f.base, f.mark]
    · rfl
  tensor_naturality_right X {Y Z} f := by
    apply EffectHom.ext
    · change (X ◁ f) ≫ 𝟙 (X ⊗ Z) = 𝟙 (X ⊗ Y) ≫ (X ◁ f)
      rw [Category.comp_id, Category.id_comp]
    · simp [wl, tensorCharge, f.base, f.mark]
    · rfl
  associativity X Y Z := by
    apply EffectHom.ext
    · change (α_ X Y Z).hom ≫ (X ◁ 𝟙 (Y ⊗ Z)) ≫ 𝟙 (X ⊗ (Y ⊗ Z)) =
        (𝟙 (X ⊗ Y) ▷ Z) ≫ 𝟙 ((X ⊗ Y) ⊗ Z) ≫ (α_ X Y Z).hom
      simp
    · simp [wl, wr, tensorCharge, Function.comp_def]
      abel
    · rfl
  left_unitality X := by
    apply EffectHom.ext
    · exact Category.id_comp _
    · simp [tensorCharge]
    · rfl
  right_unitality X := by
    apply EffectHom.ext
    · exact Category.id_comp _
    · simp [tensorCharge]
    · rfl
  map_central f := pureCentral f

abbrev freyd : FreydCategory J where
  toStrongPremonoidal := strong
  braiding X Y := by
    change (scalarIso (J.obj (X ⊗ Y)) (tensorCharge X Y)).hom ≫ J.map (BraidedCategory.braiding X Y).hom =
      (swapIso (J.obj X) (J.obj Y)).hom ≫ (scalarIso (J.obj (Y ⊗ X)) (tensorCharge Y X)).hom
    apply EffectHom.ext
    · change 𝟙 (X ⊗ Y) ≫ (BraidedCategory.braiding X Y).hom = (BraidedCategory.braiding X Y).hom ≫ 𝟙 (Y ⊗ X)
      rw [Category.id_comp, Category.comp_id]
    · simp [tensorCharge, Prod.swap]
      abel
    · rfl
  obj_bijective := ⟨fun _ _ h => congrArg Computation.value h, fun x => ⟨x.value, by cases x; rfl⟩⟩

local instance : FreydCategory J := freyd

theorem unitCentral : FreydCategory.CentralUnit J :=
  FreydCategory.CentralUnit.of_unitIso_eqToIso J rfl rfl

open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (duplicate extend bind)
open Silmaril.Isotope.LetIter.Semantics.Categorical (extend_map)

abbrev E : Value := ⟨Bool, false, true⟩

def flipSign : J.obj unit ⟶ J.obj unit := ⟨𝟙 _, 0, true⟩

noncomputable abbrev diagonal : J.obj E ⟶ J.obj E ⊗ J.obj E :=
  J.map (duplicate E) ≫ (Functor.StrongPremonoidal.tensorIso (J := J) E E).inv

def coefficient : FreeAbelianGroup ((Bool × Bool) × Unit) →+ ℤ :=
  FreeAbelianGroup.lift fun p => if p = ((true, false), ()) then 1 else 0

theorem diagonalNotCentral : ¬ IsCentral diagonal := by
  intro h
  have chargeEq := congrArg EffectHom.charge (h.1 flipSign)
  have coefficientEq := congrArg coefficient chargeEq
  change coefficient (push (fun p => (p, ())) (-tensorCharge E E)) =
    coefficient (-(push (fun p => (p, ())) (-tensorCharge E E))) at coefficientEq
  have first : (((true, true), ()) : (Bool × Bool) × Unit) ≠ ((true, false), ()) := by decide
  have third : (((false, true), ()) : (Bool × Bool) × Unit) ≠ ((true, false), ()) := by decide
  have fourth : (((false, false), ()) : (Bool × Bool) × Unit) ≠ ((true, false), ()) := by decide
  norm_num [coefficient, tensorCharge, first, third, fourth] at coefficientEq

def tick : J.obj E ⟶ J.obj unit := ⟨⟨fun _ => (), rfl, rfl⟩, 0, true⟩

abbrev firstOutput : E ⊗ unit ⟶ E := CartesianMonoidalCategory.fst E unit

theorem extendTickCharge : (extend J tick).charge = 0 := by
  change push (fun p : Bool × Unit => p)
    (push (fun p : Bool × Bool => (p.1, ())) (-tensorCharge E E)) -
      (show FreeAbelianGroup (Bool × Unit) from tensorCharge E unit) = 0
  simp [tensorCharge]

theorem tickBind :
    bind J tick (J.map firstOutput) = (⟨𝟙 E, 0, true⟩ : J.obj E ⟶ J.obj E) := by
  apply EffectHom.ext
  · apply ValueHom.ext
    rfl
  · change (extend J tick ≫ J.map firstOutput).charge = 0
    simp [extendTickCharge]
  · rfl

abbrev bindResult : J.obj (E ⊗ E) ⟶ J.obj (E ⊗ E) := 𝟙 _

def bindCoefficient : FreeAbelianGroup (Bool × Bool) →+ ℤ :=
  FreeAbelianGroup.lift fun p => if p = (true, false) then 1 else 0

/-- The native contextual bind associativity equation fails at this plain Freyd boundary. -/
theorem bindAssocFails :
    bind J (bind J tick (J.map firstOutput)) bindResult ≠
      bind J tick
        (bind J (J.map firstOutput)
          (J.map (firstOutput ▷ E) ≫ bindResult)) := by
  intro h
  rw [tickBind] at h
  unfold Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind at h
  rw [extend_map] at h
  simp only [Category.comp_id, ← J.map_comp] at h
  have rightCharge : (extend J tick ≫
      J.map (CartesianMonoidalCategory.lift (𝟙 (E ⊗ unit)) firstOutput ≫ (firstOutput ▷ E))).charge = 0 := by
    simp [extendTickCharge]
  have hc := congrArg EffectHom.charge h
  rw [rightCharge] at hc
  change push (fun p : Bool × Bool => p)
    (push (fun p : Bool × Bool => p) (-tensorCharge E E)) - (show FreeAbelianGroup (Bool × Bool) from tensorCharge E E) = 0 at hc
  have hv := congrArg bindCoefficient hc
  have first : ((true, true) : Bool × Bool) ≠ (true, false) := by decide
  have third : ((false, true) : Bool × Bool) ≠ (true, false) := by decide
  have fourth : ((false, false) : Bool × Bool) ≠ (true, false) := by decide
  norm_num [bindCoefficient, tensorCharge, first, third, fourth] at hv

public theorem not_centralUnitTransportedDiagonals_proof : ¬ CentralUnitTransportedDiagonals := by
  intro h
  have := unitCentral
  exact diagonalNotCentral (h J E)

public theorem not_centralUnitContextualBindAssoc_proof : ¬ CentralUnitContextualBindAssoc := by
  intro h
  have := unitCentral
  exact bindAssocFails (h J tick (J.map firstOutput) bindResult)

end Silmaril.Isotope.LetIter.Semantics.Categorical.CentralUnitDiagonal
