module

public import Silmaril.Logic.Smt.Uflia.SortMaps.Defs
public import Mathlib.Logic.Function.Basic

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.SortMaps.Hom
open CategoryTheory
variable {A B C : Signature}

private theorem carrier_value_eq (f : A ⟶ B) (M : Model B.symbols)
    (s : SortCode A.users) : (carriers f M).value s = M.carriers.value (f.sorts s) := by
  cases s with
  | bool => exact congrArg M.carriers.value f.bool.symm
  | int => exact congrArg M.carriers.value f.int.symm
  | user _ => rfl

private theorem transport_value_heq (f : A ⟶ B) (M : Model B.symbols)
    (s : SortCode A.users) (x : (carriers f M).value s) : HEq (value f M s x) x :=
  cast_heq _ _

private theorem transport_value_symm_heq (f : A ⟶ B) (M : Model B.symbols)
    (s : SortCode A.users) (x : M.carriers.value (f.sorts s)) :
    HEq ((value f M s).symm x) x := cast_heq _ _

private theorem carriers_ext {U : Type} (X Y : Carriers U) (h : X.user = Y.user) :
    X = Y := by
  cases X
  cases Y
  cases h
  rfl

private theorem model_ext {U : Type} {S : Uflia.Signature U} (M N : Model S)
    (hc : M.carriers = N.carriers) (hop : HEq (@M.operation) (@N.operation)) : M = N := by
  cases M
  cases N
  cases hc
  cases hop
  rfl

theorem model_reduct_id (M : Model A.symbols) : reduct (𝟙 A) M = M := by
  cases M
  rfl

theorem carriers_comp (f : A ⟶ B) (g : B ⟶ C) (M : Model C.symbols) :
    carriers (f ≫ g) M = carriers f (reduct g M) := by
  apply carriers_ext
  funext u
  exact (carrier_value_eq g M (f.sorts (.user u))).symm

theorem model_reduct_comp (f : A ⟶ B) (g : B ⟶ C) (M : Model C.symbols) :
    reduct (f ≫ g) M = reduct f (reduct g M) := by
  apply model_ext _ _ (carriers_comp f g M)
  apply Function.hfunext rfl
  intro n n' hn
  cases hn
  apply Function.hfunext rfl
  intro inputs inputs' hi
  cases hi
  apply Function.hfunext rfl
  intro output output' ho
  cases ho
  apply Function.hfunext rfl
  intro op op' hop
  cases hop
  apply Function.hfunext
  · change ((i : Fin n) → (carriers (f ≫ g) M).value (inputs i)) =
      ((i : Fin n) → (carriers f (reduct g M)).value (inputs i))
    rw [carriers_comp f g M]
  intro args args' ha
  change HEq ((value (f ≫ g) M output).symm _)
    ((value f (reduct g M) output).symm _)
  apply (transport_value_symm_heq (f ≫ g) M output _).trans
  apply HEq.trans _ (transport_value_symm_heq f (reduct g M) output _).symm
  apply HEq.trans _ (transport_value_symm_heq g M (f.sorts output) _).symm
  apply heq_of_eq
  congr 1
  funext i
  apply eq_of_heq
  apply (transport_value_heq (f ≫ g) M (inputs i) _).trans
  apply HEq.trans _ (transport_value_heq g M (f.sorts (inputs i)) _).symm
  apply HEq.trans _ (transport_value_heq f (reduct g M) (inputs i) _).symm
  exact dcongr_heq (HEq.rfl : HEq i i)
    (fun j k hjk => by
      cases hjk
      exact congrArg (fun D : Carriers A.users => D.value (inputs j)) (carriers_comp f g M))
    (fun _ _ => ha)

private theorem hom_ext_heq {U : Type} {S : Uflia.Signature U}
    {M N M' N' : Model S} (hm : M = M') (hn : N = N')
    (h : M ⟶ N) (h' : M' ⟶ N') (hu : HEq h.user h'.user) : HEq h h' := by
  cases hm
  cases hn
  exact heq_of_eq (Model.Hom.ext _ _ (eq_of_heq hu))

private theorem hom_value_natural (f : A ⟶ B) {M N : Model B.symbols} (h : M ⟶ N)
    (s : SortCode A.users) (x : (carriers f M).value s) :
    value f N s ((hom f h).value s x) = h.value (f.sorts s) (value f M s x) := by
  have transport {s t : SortCode B.users} (e : s = t) (y : M.carriers.value s) :
      Equiv.cast (congrArg N.carriers.value e) (h.value s y) =
        h.value t (Equiv.cast (congrArg M.carriers.value e) y) := by
    cases e
    rfl
  cases s with
  | bool => exact transport f.bool.symm x
  | int => exact transport f.int.symm x
  | user u => rfl

theorem model_reductFunctor_id (A : Signature) :
    reductFunctor (𝟙 A) = 𝟭 (Model A.symbols) := by
  refine Functor.hext model_reduct_id ?_
  intro M N h
  apply hom_ext_heq (model_reduct_id M) (model_reduct_id N)
  apply heq_of_eq
  rfl

theorem model_reductFunctor_comp (f : A ⟶ B) (g : B ⟶ C) :
    reductFunctor (f ≫ g) = reductFunctor g ⋙ reductFunctor f := by
  refine Functor.hext (model_reduct_comp f g) ?_
  intro M N h
  apply hom_ext_heq (model_reduct_comp f g M) (model_reduct_comp f g N)
  apply Function.hfunext rfl
  intro u u' hu
  cases hu
  apply Function.hfunext
  · exact congrArg (fun D : Carriers A.users => D.user u) (carriers_comp f g M)
  intro x x' hx
  change HEq (h.value (g.sorts (f.sorts (.user u))) x)
    ((hom g h).value (f.sorts (.user u)) x')
  apply HEq.trans _ (transport_value_heq g N (f.sorts (.user u)) _)
  rw [hom_value_natural]
  apply heq_of_eq
  congr 1
  apply eq_of_heq
  exact hx.trans (transport_value_heq g M (f.sorts (.user u)) x').symm

end Silmaril.Logic.Smt.Uflia.SortMaps.Hom
