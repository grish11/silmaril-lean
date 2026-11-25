module

public import Silmaril.Semantics.Calco2019.Defs
import Silmaril.Proofs.Semantics.Calco2019.FreeExtensions
import Silmaril.Proofs.Semantics.Calco2019.Guardedness
import Silmaril.Proofs.Semantics.Calco2019.Iteration
import Silmaril.Proofs.Semantics.Calco2019.Dinaturality

/-! # Free extensions and guarded iteration -/

public section

universe u v u' v'

namespace Silmaril.Calco2019

open CategoryTheory CategoryTheory.Limits

section FreeExtensions

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  {O : Bimodule C D} {A : C} {B I V W : D}

/-- The unique initial leg turns a free object into a free extension. -/
theorem isFreeExtension_initial_iff (i : IsInitial I) (e : O.Hom A V) :
    O.IsFreeExtension e (i.to V) ↔ O.IsFreeObject e :=
  Proofs.isFreeExtension_initial_iff i e

/-- Postcomposing a free generator with a coproduct leg gives the free-extension generator. -/
theorem isFreeExtension_coprod_iff {d : O.Hom A W} (hd : O.IsFreeObject d)
    (l : W ⟶ V) (r : B ⟶ V) :
    O.IsFreeExtension (O.post d l) r ↔ Nonempty (IsColimit (BinaryCofan.mk l r)) :=
  Proofs.isFreeExtension_coprod_iff hd l r

/-- Recover the unique left coproduct leg at the vertex of a free extension. -/
theorem freeExtension_coprodLeg {d : O.Hom A W} (hd : O.IsFreeObject d)
    {e : O.Hom A V} {r : B ⟶ V} (hr : O.IsFreeExtension e r) :
    ∃! l : W ⟶ V, O.post d l = e ∧ Nonempty (IsColimit (BinaryCofan.mk l r)) := by
  obtain ⟨l, h, unique⟩ := hd V e
  exact ⟨l, ⟨h, (isFreeExtension_coprod_iff hd l r).mp (h.symm ▸ hr)⟩, fun q hq => unique q hq.1⟩

end FreeExtensions

namespace Guardedness

variable {K : Type u} [Category.{v} K] {P : Coproducts K} {G : Guardedness P}
  {A X Y Z V W : K}

/-- An initial arrow is guarded in either summand. -/
theorem initial (i : IsInitial A) : G.guarded (i.to (P.sum Y Z)) :=
  Proofs.guarded_initial i

theorem precomp {f : X ⟶ P.sum Y Z} (hf : G.guarded f) (u : A ⟶ X) :
    G.guarded (u ≫ f) :=
  Proofs.guarded_precomp hf u

theorem map {f : X ⟶ P.sum Y Z} (hf : G.guarded f) (g : Y ⟶ V) (h : Z ⟶ W) :
    G.guarded (f ≫ P.map g h) :=
  Proofs.guarded_map hf g h

/-- A guard on the two rightmost summands gives a guard on the rightmost summand. -/
theorem weaken {f : X ⟶ P.sum (P.sum Y Z) W} (hf : G.nested f) : G.guarded f :=
  Proofs.guarded_weaken hf

theorem least_le (G : Guardedness P) {f : X ⟶ P.sum Y Z} :
    (least P).guarded f → G.guarded f :=
  Proofs.least_le G

/-- Solving the rightmost recursion preserves the guard on the middle summand. -/
theorem guarded_fixpoint {f : X ⟶ P.sum (P.sum Y Z) X} (hf : G.nested f)
    {g : X ⟶ P.sum Y Z} (hg : IsFixpoint f g) : G.guarded g :=
  Proofs.guarded_fixpoint hf hg

theorem merge {f : X ⟶ P.sum (P.sum Y Z) Z} (hf : G.nested f) :
    G.guarded (f ≫ P.merge) :=
  Proofs.guarded_merge hf

/-- Either alternative guard in dinaturality guards both loop bodies. -/
theorem dinaturality_bodies (g : X ⟶ P.sum Y Z) (h : Z ⟶ P.sum Y X)
    (guard : G.guarded g ∨ G.guarded h) :
    G.guarded (g ≫ P.desc P.inl h) ∧ G.guarded (h ≫ P.desc P.inl g) :=
  Proofs.guarded_dinaturality g h guard

theorem vacuous_iterative : (least P).Iterative :=
  Proofs.vacuous_iterative

namespace Fixpoints

/-- The selected coproduct injections, swap and fold are permitted uniformity maps. -/
theorem coproductUniformity_of_uniform (F : G.Fixpoints)
    {C : Type u'} [Category.{v'} C] {Q : Coproducts C} {J : C ⥤ K}
    (S : PreservesSelectedCoproducts Q P J) (surj : Function.Surjective J.obj)
    (U : F.Uniform J) : F.CoproductUniformity :=
  Proofs.coproductUniformity_of_uniform F S surj U

/-- Derive guarded dinaturality from the other Conway laws and structural uniformity. -/
theorem dinaturality_of_coproductUniformity (F : G.Fixpoints)
    (N : F.NaturalCodiagonal) (U : F.CoproductUniformity) : F.Dinaturality :=
  Proofs.derive_dinaturality F N U

/-- Proposition 17. Objectwise surjectivity suffices for the changes of state used in the proof. -/
theorem dinaturality_of_uniform (F : G.Fixpoints)
    {C : Type u'} [Category.{v'} C] {Q : Coproducts C} {J : C ⥤ K}
    (S : PreservesSelectedCoproducts Q P J) (surj : Function.Surjective J.obj)
    (N : F.NaturalCodiagonal) (U : F.Uniform J) : F.Dinaturality :=
  F.dinaturality_of_coproductUniformity N (F.coproductUniformity_of_uniform S surj U)

theorem ofIterative_naturalCodiagonal (h : G.Iterative) :
    (ofIterative h).NaturalCodiagonal :=
  Proofs.iterative_naturalCodiagonal h

theorem ofIterative_dinaturality (h : G.Iterative) :
    (ofIterative h).Dinaturality :=
  Proofs.iterative_dinaturality h

theorem ofIterative_uniform (h : G.Iterative) {C : Type u'} [Category.{v'} C] (J : C ⥤ K) :
    (ofIterative h).Uniform J :=
  Proofs.iterative_uniform h J

end Fixpoints
end Guardedness
/-- Use the unique guarded solutions from Definition 19(1) to form a guarded Elgot monad. -/
@[expose]
noncomputable def GuardedElgotMonad.ofIterative {C : Type u} [Category.{v} C]
    {P : Coproducts C} {T : CategoryTheory.Monad C} {G : MonadGuardedness P T}
    (h : G.Iterative) : GuardedElgotMonad P where
  monad := T
  guard := G
  iteration :=
    { toFixpoints := Guardedness.Fixpoints.ofIterative h
      naturalCodiagonal := Guardedness.Fixpoints.ofIterative_naturalCodiagonal h
      dinaturality := Guardedness.Fixpoints.ofIterative_dinaturality h }
  uniformity := Guardedness.Fixpoints.ofIterative_uniform h _

end Silmaril.Calco2019
