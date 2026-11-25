module

public import Silmaril.Semantics.Calco2019.Examples.Delay.Defs

@[expose] public section

universe u

namespace Silmaril.Calco2019.Examples.Delay.Proofs

open CategoryTheory CategoryTheory.Endofunctor CategoryTheory.Limits

theorem corec_unique {X S : Type u} (body : S → X ⊕ S) (k : S → Computation X)
    (hk : ∀ s, Computation.destruct (k s) = Computation.rmap k (body s)) :
    k = Computation.corec body := by
  funext s
  apply Computation.eq_of_bisim (fun p q => ∃ t, p = k t ∧ q = Computation.corec body t) ?_
    ⟨s, rfl, rfl⟩
  rintro _ _ ⟨t, rfl, rfl⟩
  rw [hk, Computation.corec_eq]
  cases h : body t with
  | inl x => rfl
  | inr t' => exact ⟨t', rfl, rfl⟩

theorem map_apply {X S V : Type u} (k : S ⟶ V) (t : X ⊕ S) :
    (family.toParametrizedMonad.parameter X).map k t = Computation.rmap k t := by
  change typeCoproducts.map (𝟙 X) k t = _
  cases t <;> rfl

def corecHom (X : Type u) (S : Coalgebra (family.toParametrizedMonad.parameter X)) :
    S ⟶ coalgebra X where
  f := TypeCat.ofHom (Computation.corec S.str)
  h := by
    apply ConcreteCategory.hom_ext
    intro s
    change (family.toParametrizedMonad.parameter X).map
      (TypeCat.ofHom (Computation.corec S.str)) (S.str s) = _
    exact (map_apply (X := X) _ (S.str s)).trans (Computation.corec_eq S.str s).symm

noncomputable def terminal (X : Type u) : IsTerminal (coalgebra X) := by
  refine IsTerminal.ofUniqueHom (corecHom X) ?_
  intro S k
  apply Coalgebra.Hom.ext
  apply ConcreteCategory.hom_ext
  intro s
  apply congrFun (corec_unique S.str k.f ?_) s
  intro t
  have eq := ConcreteCategory.congr_hom k.h t
  change (family.toParametrizedMonad.parameter X).map k.f (S.str t) =
    Computation.destruct (k.f t) at eq
  exact eq.symm.trans (map_apply (X := X) k.f (S.str t))

noncomputable def resumptions : FinalResumptions family.toParametrizedMonad where
  coalgebra := coalgebra
  final := terminal

theorem unit_eq (X : Type u) (x : X) : resumptions.unit X x = Computation.pure x := by
  apply Computation.destruct_eq_pure
  exact ConcreteCategory.congr_hom (resumptions.unit_out X) x

theorem extend_eq {X Y : Type u} (f : X → Computation Y) (c : Computation X) :
    resumptions.extend typeCoproducts (TypeCat.ofHom f) c = Computation.bind c f := by
  have eq : TypeCat.ofHom (fun p => Computation.bind p f) =
      resumptions.extend typeCoproducts (TypeCat.ofHom f) := by
    apply resumptions.extend_unique typeCoproducts
    apply ConcreteCategory.hom_ext
    intro p
    change Computation.destruct (Computation.bind p f) =
      (resumptions.out X ≫ (family.toParametrizedMonad.parameter X).map
        (TypeCat.ofHom (fun p => Computation.bind p f)) ≫
        family.toParametrizedMonad.extend (TypeCat.ofHom f ≫ resumptions.out Y)) p
    have layer (t : X ⊕ Computation X) :
        ((family.toParametrizedMonad.parameter X).map
            (TypeCat.ofHom (fun p => Computation.bind p f)) ≫
          family.toParametrizedMonad.extend (TypeCat.ofHom f ≫ resumptions.out Y)) t =
          Sum.elim (fun x => Computation.destruct (f x))
            (fun p => Sum.inr (Computation.bind p f)) t := by
      cases t <;> rfl
    refine Eq.trans ?_ (layer (Computation.destruct p)).symm
    induction p using Computation.recOn <;> simp
  exact (congrArg (fun k : Computation X ⟶ Computation Y => k c) eq).symm

end Silmaril.Calco2019.Examples.Delay.Proofs
