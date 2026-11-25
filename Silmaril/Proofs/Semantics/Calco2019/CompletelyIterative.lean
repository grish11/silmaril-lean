module

public import Silmaril.Semantics.Calco2019.CompletelyIterative.Defs
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard

public section

universe u v

namespace Silmaril.Calco2019.Proofs.CompletelyIterative

open CategoryTheory

variable {C : Type u} [Category.{v} C] {T : CategoryTheory.Monad C}
  (I : IdealizedMonad T) (P : Coproducts C)

local notation "J" => Kleisli.Adjunction.toKleisli T
local notation "K" => P.kleisli T

private theorem include_comp {A B : Kleisli T} (f : A ⟶ B) :
    I.includeIdeal A ≫ f = (J).map (I.ideal.map f) ≫ I.includeIdeal B := by
  apply Kleisli.hom_ext
  exact ((I.inclusion.naturality f).symm).trans (pure_comp_of T _ _).symm

theorem trivial {X Y Z : Kleisli T} (f : X ⟶ Y) :
    I.WeaklyGuarded P (Y := Y) (Z := Z) (f ≫ (K).inl) := by
  refine ⟨f ≫ (K).inl, ?_⟩
  simp [IdealizedMonad.guardBody]

theorem parallel {X Y V W : Kleisli T} {f : X ⟶ (K).sum V W} {g : Y ⟶ (K).sum V W}
    (hf : I.WeaklyGuarded P (Y := V) (Z := W) f)
    (hg : I.WeaklyGuarded P (Y := V) (Z := W) g) :
    I.WeaklyGuarded P (Y := V) (Z := W) ((K).desc f g) := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  exact ⟨(K).desc a b, ((K).desc_comp _ _ _).symm⟩

theorem compose {X Y Z V W : Kleisli T} {f : X ⟶ (K).sum Y Z} {g : Y ⟶ (K).sum V W}
    (h : Z ⟶ (K).sum V W) (hf : I.WeaklyGuarded P (Y := Y) (Z := Z) f)
    (hg : I.WeaklyGuarded P (Y := V) (Z := W) g) :
    I.WeaklyGuarded P (Y := V) (Z := W) (f ≫ (K).desc g h) := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  let k := (K).desc (b ≫ I.guardBody P V W) h
  let m := (J).map (I.ideal.map k)
  refine ⟨a ≫ (K).desc b (m ≫ (K).inr), ?_⟩
  simp only [Category.assoc]
  congr 1
  change (K).desc (K).inl (I.includeIdeal ((K).sum Y Z)) ≫ k =
    (K).desc b (m ≫ (K).inr) ≫ (K).desc (K).inl (I.includeIdeal ((K).sum V W))
  rw [(K).desc_comp, (K).desc_comp, (K).inl_desc, Category.assoc, (K).inr_desc, include_comp]
  rfl

/-- Rotating the factorization exposes a strongly guarded equation on the
ideal object. Its unique solution determines the solution to the weak loop. -/
theorem iterative (hI : I.CompletelyIterative P) {X Y : Kleisli T} (f : X ⟶ (K).sum Y X)
    (hf : I.WeaklyGuarded P (Y := Y) (Z := X) f) :
    ∃! g, Guardedness.IsFixpoint (P := K) f g := by
  obtain ⟨j, rfl⟩ := hf
  let Z := Kleisli.mk T (I.ideal.obj ((K).sum Y X))
  let U := (K).sum Y Z
  let i : Z ⟶ (K).sum Y X := I.includeIdeal ((K).sum Y X)
  let b : U ⟶ (K).sum Y X := I.guardBody P Y X
  let k : (K).sum Y X ⟶ U := (K).desc (K).inl j
  let g : Z ⟶ U := i ≫ k
  have hg : I.StronglyGuarded P (Y := Y) (Z := Z) g := by
    refine ⟨I.ideal.map k ≫ P.inr, ?_⟩
    change I.includeIdeal ((K).sum Y X) ≫ k = _
    rw [include_comp, (J).map_comp]
    change _ = ((J).map (I.ideal.map k) ≫ (K).inr) ≫ (K).desc (K).inl (I.includeIdeal U)
    rw [Category.assoc, (K).inr_desc]
  obtain ⟨s, hs, unique⟩ := hI g hg
  let r : X ⟶ Y := j ≫ (K).desc (𝟙 Y) s
  have hrotation (q : Z ⟶ Y) :
      g ≫ (K).desc (𝟙 Y) q = i ≫ (K).desc (𝟙 Y) (j ≫ (K).desc (𝟙 Y) q) := by
    simp only [g, k, Category.assoc, (K).desc_comp, (K).inl_desc]
  have hsolution (t : X ⟶ Y) :
      (j ≫ b) ≫ (K).desc (𝟙 Y) t = j ≫ (K).desc (𝟙 Y) (i ≫ (K).desc (𝟙 Y) t) := by
    simp only [b, IdealizedMonad.guardBody, Category.assoc, (K).desc_comp, (K).inl_desc, i]
  refine ⟨r, ?_, ?_⟩
  · change (j ≫ b) ≫ (K).desc (𝟙 Y) r = r
    have e : i ≫ (K).desc (𝟙 Y) r = s := (hrotation s).symm.trans hs
    rw [hsolution, e]
  · intro t ht
    change (j ≫ b) ≫ (K).desc (𝟙 Y) t = t at ht
    let q : Z ⟶ Y := i ≫ (K).desc (𝟙 Y) t
    have e : j ≫ (K).desc (𝟙 Y) q = t := (hsolution t).symm.trans ht
    have hq : Guardedness.IsFixpoint (P := K) g q := by
      change g ≫ (K).desc (𝟙 Y) q = q
      rw [hrotation, e]
    exact e.symm.trans (congrArg (fun w => j ≫ (K).desc (𝟙 Y) w) (unique q hq))

end Silmaril.Calco2019.Proofs.CompletelyIterative
