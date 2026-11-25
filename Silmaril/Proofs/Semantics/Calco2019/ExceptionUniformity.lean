module

public import Silmaril.Semantics.Calco2019.ExceptionGuardThms
import Silmaril.Proofs.Semantics.Calco2019.ResumptionGuard

public section

universe u v

namespace Silmaril.Calco2019.Proofs

open CategoryTheory Exception

variable {C : Type u} [Category.{v} C] {P : Coproducts C}
  (T : GuardedElgotMonad P) (E : C)

theorem exception_uniformity :
    (fixpoints T E).Uniform (Kleisli.Adjunction.toKleisli ((family P T.monad).obj E)) := by
  let L := (family P T.monad).obj E
  let K := P.kleisli L
  let J := Kleisli.Adjunction.toKleisli L
  let Q := T.monad
  let K₀ := P.kleisli Q
  let J₀ := Kleisli.Adjunction.toKleisli Q
  intro X Z Y f g h hf hg comm
  let f' : X ⟶ Q.obj (P.sum (P.sum Y.of X) E) := f.of
  let g' : Z ⟶ Q.obj (P.sum (P.sum Y.of Z) E) := g.of
  let I : Y.of ⟶ Y.of := 𝟙 _
  let j := P.map I h
  have jEq : K.map (𝟙 Y) (J.map h) = J.map j := by
    have e : 𝟙 Y = J.map I := (J.map_id Y.of).symm
    rw [e]
    exact kleisli_map_pure L I h
  have raw : h ≫ f' = g' ≫ L.map j :=
    (pure_comp_of L h f).symm.trans
      ((congrArg Kleisli.Hom.of comm).trans
        ((congrArg (fun j' => (g ≫ j').of) jEq).trans (comp_pure_of L g j)))
  let a := f' ≫ Q.map (rearrange P E (Y := Y.of) (Z := X))
  let b := g' ≫ Q.map (rearrange P E (Y := Y.of) (Z := Z))
  let r := P.sum Y.of E
  let m := P.map (𝟙 r) h
  have rearr : P.map j (𝟙 E) ≫ rearrange P E =
      rearrange P E ≫ m := by
    simp [j, I, r, m, rearrange, Coproducts.map, Category.assoc]
  have c : h ≫ a = b ≫ Q.map m := by
    dsimp only [a, b]
    rw [← Category.assoc, raw]
    have fm := family_map P Q E j
    exact (congrArg (· ≫ Q.map (rearrange P E)) (congrArg (g' ≫ ·) fm)).trans
      (by simp only [Category.assoc, ← Functor.map_comp, rearr])
  let a' : J₀.obj X ⟶ K₀.sum (J₀.obj r) (J₀.obj X) := kleisliArrow a
  let b' : J₀.obj Z ⟶ K₀.sum (J₀.obj r) (J₀.obj Z) := kleisliArrow b
  have cs : J₀.map h ≫ a' = b' ≫ K₀.map (𝟙 (J₀.obj r)) (J₀.map h) := by
    have e : 𝟙 (J₀.obj r) = J₀.map (𝟙 r) := (J₀.map_id r).symm
    rw [e, kleisli_map_pure]
    apply Kleisli.hom_ext
    exact (pure_comp_of Q h a').trans (c.trans (comp_pure_of Q b' m).symm)
  have e := T.uniformity a' b' h hf hg cs
  apply Kleisli.hom_ext
  exact (pure_comp_of L h ((fixpoints T E).iterate f hf)).trans
    ((pure_comp_of Q h (T.iteration.iterate a' hf)).symm.trans (congrArg Kleisli.Hom.of e))

end Silmaril.Calco2019.Proofs
