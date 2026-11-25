module

public import Silmaril.Semantics.Calco2019.FreeExtensions
public import Mathlib.CategoryTheory.Monad.Kleisli
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Guarded categories and monads (CALCO 2019, Article 13, §4)

Coproducts are selected. In the Kleisli category the selected coproduct object
is the base coproduct, and its injections are the pure maps of the base injections.
-/

@[expose] public section

universe u v u' v'

namespace Silmaril.Calco2019

open CategoryTheory CategoryTheory.Limits

/-- A chosen binary coproduct cocone for each pair of objects. -/
structure Coproducts (K : Type u) [Category.{v} K] where
  sum : K → K → K
  inl {X Y : K} : X ⟶ sum X Y
  inr {X Y : K} : Y ⟶ sum X Y
  isColimit (X Y : K) : IsColimit (BinaryCofan.mk (inl (X := X) (Y := Y)) inr)

namespace Coproducts

variable {K : Type u} [Category.{v} K] (P : Coproducts K)

def desc {X Y Z : K} (f : X ⟶ Z) (g : Y ⟶ Z) : P.sum X Y ⟶ Z :=
  (P.isColimit X Y).desc (BinaryCofan.mk f g)

@[reassoc (attr := simp)]
theorem inl_desc {X Y Z : K} (f : X ⟶ Z) (g : Y ⟶ Z) :
    P.inl ≫ P.desc f g = f :=
  (P.isColimit X Y).fac (BinaryCofan.mk f g) ⟨.left⟩

@[reassoc (attr := simp)]
theorem inr_desc {X Y Z : K} (f : X ⟶ Z) (g : Y ⟶ Z) :
    P.inr ≫ P.desc f g = g :=
  (P.isColimit X Y).fac (BinaryCofan.mk f g) ⟨.right⟩

theorem hom_ext {X Y Z : K} {f g : P.sum X Y ⟶ Z}
    (hl : P.inl ≫ f = P.inl ≫ g) (hr : P.inr ≫ f = P.inr ≫ g) : f = g := by
  apply (P.isColimit X Y).hom_ext
  rintro ⟨j⟩
  cases j
  · exact hl
  · exact hr

@[simp]
theorem desc_comp {X Y Z W : K} (f : X ⟶ Z) (g : Y ⟶ Z) (h : Z ⟶ W) :
    P.desc f g ≫ h = P.desc (f ≫ h) (g ≫ h) := by
  apply P.hom_ext <;> simp

@[simp] theorem desc_inl_inr (X Y : K) :
    P.desc (P.inl (X := X) (Y := Y)) P.inr = 𝟙 (P.sum X Y) := by
  apply P.hom_ext <;> simp

def map {X Y V W : K} (f : X ⟶ V) (g : Y ⟶ W) : P.sum X Y ⟶ P.sum V W :=
  P.desc (f ≫ P.inl) (g ≫ P.inr)

@[reassoc (attr := simp)]
theorem map_desc {X Y V W Z : K} (f : X ⟶ V) (g : Y ⟶ W)
    (h : V ⟶ Z) (k : W ⟶ Z) :
    P.map f g ≫ P.desc h k = P.desc (f ≫ h) (g ≫ k) := by
  simp [map]

def assoc {X Y Z : K} : P.sum (P.sum X Y) Z ⟶ P.sum X (P.sum Y Z) :=
  P.desc (P.desc P.inl (P.inl ≫ P.inr)) (P.inr ≫ P.inr)

def assocInv {X Y Z : K} : P.sum X (P.sum Y Z) ⟶ P.sum (P.sum X Y) Z :=
  P.desc (P.inl ≫ P.inl) (P.map P.inr (𝟙 Z))

theorem assoc_assocInv (X Y Z : K) :
    P.assoc (X := X) (Y := Y) (Z := Z) ≫ P.assocInv = 𝟙 _ := by
  apply P.hom_ext
  · apply P.hom_ext <;> simp [assoc, assocInv, map]
  · simp [assoc, assocInv, map]

def swap {X Y : K} : P.sum X Y ⟶ P.sum Y X :=
  P.desc P.inr P.inl

def merge {X Y : K} : P.sum (P.sum Y X) X ⟶ P.sum Y X :=
  P.desc (𝟙 _) P.inr

/-- Use Mathlib's selected binary coproducts. -/
noncomputable def ofHasBinaryCoproducts (K : Type u) [Category.{v} K] [HasBinaryCoproducts K] :
    Coproducts K where
  sum X Y := X ⨿ Y
  inl := coprod.inl
  inr := coprod.inr
  isColimit X Y := coprodIsCoprod X Y

/-- The inherited coproducts of the paper's §2. -/
noncomputable def kleisli (T : CategoryTheory.Monad K) : Coproducts (Kleisli T) where
  sum X Y := .mk T (P.sum X.of Y.of)
  inl := (Kleisli.Adjunction.toKleisli T).map P.inl
  inr := (Kleisli.Adjunction.toKleisli T).map P.inr
  isColimit X Y := by
    let F := Kleisli.Adjunction.toKleisli T
    letI : F.IsLeftAdjoint := ⟨_, ⟨Kleisli.Adjunction.adj T⟩⟩
    exact mapIsColimitOfPreservesOfIsColimit F _ _ (P.isColimit X.of Y.of)

end Coproducts

/-- A functor preserving the two specified injections into each chosen coproduct. -/
structure PreservesSelectedCoproducts {C : Type u} {K : Type u'} [Category.{v} C]
    [Category.{v'} K] (P : Coproducts C) (Q : Coproducts K) (J : C ⥤ K) : Prop where
  sum_eq (X Y : C) : J.obj (P.sum X Y) = Q.sum (J.obj X) (J.obj Y)
  inl (X Y : C) : J.map (P.inl (X := X) (Y := Y)) ≫ eqToHom (sum_eq X Y) = Q.inl
  inr (X Y : C) : J.map (P.inr (X := X) (Y := Y)) ≫ eqToHom (sum_eq X Y) = Q.inr

/-- The pure embedding preserves the chosen inherited coproducts. -/
theorem Coproducts.kleisliPreservesSelected {C : Type u} [Category.{v} C]
    (P : Coproducts C) (T : CategoryTheory.Monad C) :
    PreservesSelectedCoproducts P (P.kleisli T) (Kleisli.Adjunction.toKleisli T) where
  sum_eq _ _ := rfl
  inl _ _ := Category.comp_id _
  inr _ _ := Category.comp_id _

/-- Definition 6. Guardedness in a selected right summand. -/
structure Guardedness {K : Type u} [Category.{v} K] (P : Coproducts K) where
  guarded {X Y Z : K} : (X ⟶ P.sum Y Z) → Prop
  trivial {X Y Z : K} (f : X ⟶ Y) : guarded (f ≫ P.inl (Y := Z))
  parallel {X Y V W : K} {f : X ⟶ P.sum V W} {g : Y ⟶ P.sum V W} :
    guarded f → guarded g → guarded (P.desc f g)
  compose {X Y Z V W : K} {f : X ⟶ P.sum Y Z} {g : Y ⟶ P.sum V W}
    (h : Z ⟶ P.sum V W) : guarded f → guarded g → guarded (f ≫ P.desc g h)

namespace Guardedness

variable {K : Type u} [Category.{v} K] {P : Coproducts K} (G : Guardedness P)

/-- Notation 7 for two nested guarded summands. -/
def nested {X Y Z W : K} (f : X ⟶ P.sum (P.sum Y Z) W) : Prop :=
  G.guarded (f ≫ P.assoc)

/-- Guardedness in the left summand, after exchanging the two summands. -/
def left {X Y Z : K} (f : X ⟶ P.sum Y Z) : Prop :=
  G.guarded (f ≫ P.swap)

/-- Guardedness of the entire output, using the initial object as the return summand. -/
def all [HasInitial K] {X Y : K} (f : X ⟶ Y) : Prop :=
  G.guarded (f ≫ P.inr (X := ⊥_ K))

/-- The fixpoint equation for the body of a loop. -/
def IsFixpoint {X Y : K} (f : X ⟶ P.sum Y X) (g : X ⟶ Y) : Prop :=
  f ≫ P.desc (𝟙 Y) g = g

/-- Definition 12. Guarded iteration by unique fixpoints. -/
def Iterative : Prop :=
  ∀ {X Y : K} (f : X ⟶ P.sum Y X), G.guarded f → ∃! g, IsFixpoint f g

/-- A choice of fixpoint for each guarded loop body. -/
structure Fixpoints where
  iterate {X Y : K} (f : X ⟶ P.sum Y X) : G.guarded f → (X ⟶ Y)
  fixpoint {X Y : K} (f : X ⟶ P.sum Y X) (hf : G.guarded f) : IsFixpoint f (iterate f hf)

variable {G} in
/-- The dinaturality equation uses either of the paper's alternative guards. -/
def Fixpoints.Dinaturality (F : G.Fixpoints) : Prop :=
  ∀ {X Y Z : K} (g : X ⟶ P.sum Y Z) (h : Z ⟶ P.sum Y X),
    (G.guarded g ∨ G.guarded h) →
    ∀ (hg : G.guarded (g ≫ P.desc P.inl h)) (hh : G.guarded (h ≫ P.desc P.inl g)),
    F.iterate (g ≫ P.desc P.inl h) hg = g ≫ P.desc (𝟙 Y) (F.iterate (h ≫ P.desc P.inl g) hh)

variable {G} in
/-- The Conway equations shared by guarded Conway operators and Proposition 17. -/
structure Fixpoints.NaturalCodiagonal (F : G.Fixpoints) : Prop where
  naturality {X Y Z : K} (f : X ⟶ P.sum Y X) (g : Y ⟶ Z) (hf : G.guarded f)
      (hg : G.guarded (f ≫ P.map g (𝟙 X))) :
    F.iterate (f ≫ P.map g (𝟙 X)) hg = F.iterate f hf ≫ g
  codiagonal {X Y : K} (f : X ⟶ P.sum (P.sum Y X) X) (hf : G.nested f)
      (hinner : G.guarded f) (houter : G.guarded (F.iterate f hinner))
      (hmerged : G.guarded (f ≫ P.merge)) :
    F.iterate (f ≫ P.merge) hmerged = F.iterate (F.iterate f hinner) houter

/-- Definition 14. Guarded Conway iteration. -/
structure Conway extends G.Fixpoints where
  naturalCodiagonal : toFixpoints.NaturalCodiagonal
  dinaturality : toFixpoints.Dinaturality

variable {G} in
/-- Definition 16. Uniformity for a functor supplying the permitted changes of state. -/
def Fixpoints.Uniform (F : G.Fixpoints) {C : Type u'} [Category.{v'} C] (J : C ⥤ K) : Prop :=
  ∀ {X Z : C} {Y : K} (f : J.obj X ⟶ P.sum Y (J.obj X))
    (g : J.obj Z ⟶ P.sum Y (J.obj Z)) (h : Z ⟶ X)
    (hf : G.guarded f) (hg : G.guarded g),
    J.map h ≫ f = g ≫ P.map (𝟙 Y) (J.map h) →
    J.map h ≫ F.iterate f hf = F.iterate g hg

variable {G} in
/-- Uniformity for a single change of state in the computation category. -/
def Fixpoints.UniformAt (F : G.Fixpoints) {X Z : K} (h : Z ⟶ X) : Prop :=
  ∀ {Y : K} (f : X ⟶ P.sum Y X) (g : Z ⟶ P.sum Y Z)
    (hf : G.guarded f) (hg : G.guarded g),
    h ≫ f = g ≫ P.map (𝟙 Y) h → h ≫ F.iterate f hf = F.iterate g hg

variable {G} in
/-- Structural changes of state used in the derivation of dinaturality. -/
structure Fixpoints.CoproductUniformity (F : G.Fixpoints) : Prop where
  inl {X Z : K} : F.UniformAt (P.inl (X := X) (Y := Z))
  inr {X Z : K} : F.UniformAt (P.inr (X := X) (Y := Z))
  swap {X Z : K} : F.UniformAt (P.swap (X := X) (Y := Z))
  fold (X : K) : F.UniformAt (P.desc (𝟙 X) (𝟙 X))

/-- The total guardedness of Proposition 9(1). -/
def greatest (P : Coproducts K) : Guardedness P where
  guarded _ := True
  trivial _ := True.intro
  parallel _ _ := True.intro
  compose _ _ _ := True.intro

/-- The vacuous guardedness of Proposition 9(2). -/
def least (P : Coproducts K) : Guardedness P where
  guarded f := ∃ g, f = g ≫ P.inl
  trivial f := ⟨f, rfl⟩
  parallel := by
    rintro X Y V W f g ⟨f', rfl⟩ ⟨g', rfl⟩
    exact ⟨P.desc f' g', (P.desc_comp f' g' P.inl).symm⟩
  compose := by
    rintro X Y Z V W f g h ⟨f', rfl⟩ ⟨g', rfl⟩
    exact ⟨f' ≫ g', by simp⟩

variable {G} in
/-- Choose the unique fixpoint of each guarded loop. -/
noncomputable def Fixpoints.ofIterative (h : G.Iterative) : G.Fixpoints where
  iterate f hf := (h f hf).exists.choose
  fixpoint f hf := (h f hf).exists.choose_spec

end Guardedness

section Monads

variable {C : Type u} [Category.{v} C] (P : Coproducts C)

/-- Definitions 6 and 19 use the Kleisli category with its inherited coproducts. -/
abbrev MonadGuardedness (T : CategoryTheory.Monad C) := Guardedness (P.kleisli T)

/-- Regard a base arrow into a computation as a map in the Kleisli category. -/
abbrev kleisliArrow {T : CategoryTheory.Monad C} {X Y : C} (f : X ⟶ T.obj Y) :
    Kleisli.mk T X ⟶ Kleisli.mk T Y :=
  Kleisli.Hom.mk f

/-- Definition 11(1). A monad map preserves guards on Kleisli arrows. -/
def MonadGuardedness.Preserves {T S : CategoryTheory.Monad C}
    (G : MonadGuardedness P T) (G' : MonadGuardedness P S) (m : T ⟶ S) : Prop :=
  ∀ {X Y Z : C} (f : X ⟶ T.obj (P.sum Y Z)),
    G.guarded (kleisliArrow f) → G'.guarded (kleisliArrow (f ≫ m.app (P.sum Y Z)))

/-- Definition 11(2). Every component of the transformation is guarded in its entire output. -/
def MonadGuardedness.GuardedNatTrans [HasInitial C] {T : CategoryTheory.Monad C}
    (G : MonadGuardedness P T) {H : C ⥤ C} (σ : H ⟶ (T : C ⥤ C)) : Prop :=
  ∀ X : C, G.guarded (Y := Kleisli.mk T (⊥_ C)) (Z := Kleisli.mk T X)
    (kleisliArrow (σ.app X ≫ T.map (P.inr (X := ⊥_ C) (Y := X))))

/-- Definition 19(1). Guarded Kleisli loops have unique solutions. -/
def IsGuardedIterative {T : CategoryTheory.Monad C} (G : MonadGuardedness P T) : Prop :=
  G.Iterative

/-- Definition 19(2). The permitted changes of state are pure Kleisli maps. -/
structure GuardedElgotMonad where
  monad : CategoryTheory.Monad C
  guard : MonadGuardedness P monad
  iteration : guard.Conway
  uniformity : iteration.toFixpoints.Uniform (Kleisli.Adjunction.toKleisli monad)

/-- Definition 19(3). A guarded Elgot monad with total guardedness. -/
def GuardedElgotMonad.IsElgot (T : GuardedElgotMonad P) : Prop :=
  ∀ {X Y Z : Kleisli T.monad} (f : X ⟶ (P.kleisli T.monad).sum Y Z), T.guard.guarded f

/-- Morphisms used in Definition 21 and Theorem 28 preserve both guards and their chosen solutions. -/
structure GuardedElgotMonadHom (T S : GuardedElgotMonad P) where
  hom : T.monad ⟶ S.monad
  guarded : MonadGuardedness.Preserves P T.guard S.guard hom
  iteration {X Y : C} (f : X ⟶ T.monad.obj (P.sum Y X))
      (hf : T.guard.guarded (kleisliArrow f)) :
    (T.iteration.iterate (kleisliArrow f) hf).of ≫ hom.app Y =
      (S.iteration.iterate (kleisliArrow (f ≫ hom.app (P.sum Y X))) (guarded f hf)).of

end Monads

end Silmaril.Calco2019
