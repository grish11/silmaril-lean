module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton.Defs

/-! # Raw singleton category comparison for a normalized seed -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton

open CategoryTheory
open OrderedPairSingleton (Rep composeRep ofRegion_bind_compRep)
open Paper.Extension.Singleton (ofType ofRegion ofRegion_eq_iff)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] (S : NormalizedSeed τ Φ)
  {A B C : τ}

local notation "G" => ofType S.step
local notation "Guarded" => Extension.Singleton.TypeCategory S.step

theorem normalize_guarded {r : Region Φ} (hr : ValueBranches [A] r [B]) :
    normalizeHom S (rawClass S hr.hasType) = ofRegion S.step hr :=
  (ofRegion_eq_iff S.step hr.hasType.bindBranchArguments hr).mpr
    (.paper (.cfgEta (.native hr.bindBranchArguments_equiv.symm)))

theorem normalizeHom_injective : Function.Injective (normalizeHom S (A := A) (B := B)) :=
  fun f g => Quotient.inductionOn₂ f g (fun r s h => Quotient.sound
    ((S.eqv_iff_normalized r.property s.property).mpr
      ((ofRegion_eq_iff S.step r.property.bindBranchArguments s.property.bindBranchArguments).mp h)))

theorem normalizeHom_surjective : Function.Surjective (normalizeHom S (A := A) (B := B)) := by
  intro f
  induction f using Quot.ind with
  | _ f =>
    obtain ⟨_, hr, rfl⟩ := Paper.TypeCategory.exists_ofRegion (τ := τ) (Φ := Φ) (A := A) (B := B) f
    exact ⟨rawClass S hr.hasType, normalize_guarded S hr⟩

theorem normalize_compRep (r : Rep (Φ := Φ) A B) (s : Rep (Φ := Φ) B C) :
    normalizeHom S (Quotient.mk _ (composeRep r s)) =
      normalizeHom S (Quotient.mk _ r) ≫ normalizeHom S (Quotient.mk _ s) :=
  ofRegion_bind_compRep S.step r s

/-- Use the same literal bind-first composition at every normalized seed. -/
def compose (f : RawHom S A B) (g : RawHom S B C) : RawHom S A C :=
  Quotient.map₂ composeRep (fun r r' hr s s' hs => Quotient.exact
    (normalizeHom_injective S (by
      rw [normalize_compRep, normalize_compRep, congrArg (normalizeHom S) (Quotient.sound hr),
        congrArg (normalizeHom S) (Quotient.sound hs)]))) f g

@[simp] theorem normalize_identity : normalizeHom S (identity S A) = 𝟙 (G A) :=
  (normalize_guarded S (.br (ℓ := 0) rfl (.var (i := 0) rfl))).trans
    ((congrArg (Extension.Singleton.projection S.step).map (Paper.TypeCategory.ofRegion_id (τ := τ) (Φ := Φ) A)).trans
      ((Extension.Singleton.projection S.step).map_id _))

@[simp] theorem normalize_compose (f : RawHom S A B) (g : RawHom S B C) :
    normalizeHom S (compose S f g) = normalizeHom S f ≫ normalizeHom S g :=
  Quotient.inductionOn₂ f g (normalize_compRep S)

instance rawCategory : Category.{v} (RawTypeCategory S) where
  Hom X Y := RawHom S X.as Y.as
  id X := identity S X.as
  comp f g := compose S f g
  id_comp f := normalizeHom_injective S (by simp)
  comp_id f := normalizeHom_injective S (by simp)
  assoc f g h := normalizeHom_injective S (by simp [Category.assoc])

def normalizeFunctor : RawTypeCategory S ⥤ Guarded where
  obj X := G X.as
  map := normalizeHom S
  map_id _ := normalize_identity S
  map_comp f g := normalize_compose S f g

noncomputable def homEquiv (A B : τ) : RawHom S A B ≃ (G A ⟶ G B) :=
  Equiv.ofBijective (normalizeHom S) ⟨normalizeHom_injective S, normalizeHom_surjective S⟩

noncomputable def toRawHom (f : G A ⟶ G B) : RawHom S A B :=
  (homEquiv S A B).symm f

@[simp] theorem normalize_toRawHom (f : G A ⟶ G B) :
    normalizeHom S (toRawHom S f) = f :=
  (homEquiv S A B).apply_symm_apply f

noncomputable def toRawFunctor : Guarded ⥤ RawTypeCategory S where
  obj X := ⟨X.as⟩
  map := toRawHom S
  map_id X := normalizeHom_injective S
    ((normalize_toRawHom S (𝟙 X)).trans (normalize_identity S).symm)
  map_comp f g := normalizeHom_injective S
    ((normalize_toRawHom S (f ≫ g)).trans
      ((normalize_compose S (toRawHom S f) (toRawHom S g)).trans
        (congrArg₂ CategoryStruct.comp (normalize_toRawHom S f) (normalize_toRawHom S g))).symm)

/-- The raw and guarded quotients are strictly isomorphic at the syntax types. -/
noncomputable def categoryIso : Cat.of (RawTypeCategory S) ≅ Cat.of Guarded where
  hom := (normalizeFunctor S).toCatHom
  inv := (toRawFunctor S).toCatHom
  hom_inv_id := by
    apply Cat.ext
    change normalizeFunctor S ⋙ toRawFunctor S = 𝟭 _
    exact Functor.hext (fun _ => rfl) (fun X Y f =>
      heq_of_eq ((homEquiv S X.as Y.as).symm_apply_apply f))
  inv_hom_id := by
    apply Cat.ext
    change toRawFunctor S ⋙ normalizeFunctor S = 𝟭 _
    exact Functor.hext (fun _ => rfl) (fun _ _ f => heq_of_eq (normalize_toRawHom S f))

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithProjectionReturnsAndUnitEta.WithBranchBinding.Singleton
