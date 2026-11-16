module

public import Silmaril.Logic.STLCEquations.Defs

/-! Public intrinsically typed lambda terms and full-function set models, with
arbitrary base-type maps. Sentences are equations only: raw typing reflection
cannot admit maps that identify distinct source base types. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.STLCEquations
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube
open Silmaril.Calculi.LambdaCube.STLC
open Cslib.LambdaCalculus.LocallyNameless.Stlc

instance : Category Language where
  Hom := Hom
  id := Hom.identity
  comp := Hom.comp
  id_comp := by
    intro S T f
    refine Hom.ext (f := _) (g := _) ?_ ?_
    · rfl
    · simp [Hom.comp, Hom.identity]
      funext as τ o
      apply eq_of_heq
      exact (cast_heq _ _).trans (f.op_heq (by simp) (by simp) (cast_heq _ _))
  comp_id := by
    intro S T f
    refine Hom.ext (f := _) (g := _) ?_ ?_
    · rfl
    · simp [Hom.comp, Hom.identity]
  assoc := by
    intro S T U V f g h
    refine Hom.ext (f := _) (g := _) ?_ ?_
    · rfl
    · simp [Hom.comp, Function.comp_def]
      funext as τ o
      apply eq_of_heq
      exact (cast_heq _ _).trans
        ((h.op_heq
          (as := as.map (mapTy (g.base ∘ f.base)))
          (bs := (as.map (mapTy f.base)).map (mapTy g.base))
          (τ := mapTy (g.base ∘ f.base) τ)
          (υ := mapTy g.base (mapTy f.base τ))
          (p := g.op (f.op o))
          (by simp [List.map_map]) (by simp) (cast_heq _ _)).trans (cast_heq _ _).symm)

/-- Evaluation commutes with signature translation. -/
theorem eval_map {S T : Language} (f : Hom S T) (M : SetModel T.source)
    {Γ τ} (t : Term S.source Γ τ) (ρ : Tuple (carrier (M.base ∘ f.base)) Γ) :
    eval M (mapTerm f t) (envMap f.base M.base ρ) =
      carrierMap f.base M.base τ (eval (reduct f M) t ρ) := by
  induction t with
  | var x =>
      simp only [mapTerm, eval, envMap_eq_reindex, reindexTuple_apply]
  | lam t ih =>
      funext d
      change eval M (mapTerm f t) (Tuple.cons d (envMap f.base M.base ρ)) =
        carrierMap f.base M.base _ (eval (reduct f M) t
          (Tuple.cons ((carrierMap f.base M.base _).symm d) ρ))
      have h := ih (Tuple.cons ((carrierMap f.base M.base _).symm d) ρ)
      simp only [envMap, Tuple.cons_zero, Tuple.cons_succ, Equiv.apply_symm_apply] at h
      convert h using 1; rfl
  | app t u iht ihu =>
      simp only [mapTerm, eval]
      erw [iht, ihu]
      change carrierMap f.base M.base _ (eval (reduct f M) t ρ
        ((carrierMap f.base M.base _).symm (carrierMap f.base M.base _ (eval (reduct f M) u ρ)))) = _
      exact congrArg (carrierMap f.base M.base _) (congrArg (eval (reduct f M) t ρ)
        ((carrierMap f.base M.base _).symm_apply_apply _))
  | op o args ih =>
      simp only [mapTerm, eval, reduct, Equiv.apply_symm_apply]
      apply congrArg (M.op (f.op o))
      change Tuple.map (fun a (v : Term T.source _ a) => eval M v (envMap f.base M.base ρ))
        (reindexTuple (mapTy f.base) (fun _ x => mapTerm f (args _ x))) = _
      rw [reindexTuple_natural]
      simp only [envMap_eq_reindex]
      apply congrArg (reindexTuple (mapTy f.base))
      funext a x
      have h := ih a x ρ
      simp only [envMap_eq_reindex] at h
      convert h using 1; rfl

theorem satisfaction {S T : Language} (f : Hom S T) (M : SetModel T.source)
    (p : Sentence S) : Holds M (mapSentence f p) ↔ Holds (reduct f M) p := by
  cases p with
  | equation t u =>
    constructor
    · intro h ρ
      apply (carrierMap f.base M.base _).injective
      exact (eval_map f M t ρ).symm.trans ((h _).trans (eval_map f M u ρ))
    · intro h η
      obtain ⟨ρ, rfl⟩ := envMap_surjective f.base M.base _ η
      rw [eval_map, eval_map, h ρ]

/-- Identity signature translation preserves intrinsic terms. -/
theorem mapTerm_identity {S : Language} {Γ τ} (t : Term S.source Γ τ) :
    HEq (mapTerm (Hom.identity S) t) t := by
  induction t with
  | var x =>
      simp [mapTerm, Hom.identity]
      congr 1 <;> try simp
      erw [mapTy_id]
      exact var_map_id x
  | lam t ih => simp [mapTerm, Hom.identity]; congr 1 <;> simp
  | app t u iht ihu => simp [mapTerm, Hom.identity]; congr 1 <;> simp
  | op o args ih =>
      simp [mapTerm, Hom.identity]
      congr 1 <;> try simp
      exact reindexTuple_heq_id (by simp) mapTy_id _ args ih

/-- Restricting a set model along the identity signature map preserves it. -/
theorem reduct_identity {S : Language} (M : SetModel S.source) : reduct (Hom.identity S) M = M := by
  refine SetModel.ext rfl ?_
  apply heq_of_eq
  funext as τ o args
  change (carrierMap id M.base τ).symm
    (M.op ((Hom.identity S).op o) (envMap id M.base args)) = M.op o args
  apply eq_of_heq
  apply equiv_symm_apply_heq_refl (by simp) _ (carrierMap_identity M.base τ)
  exact M.op_heq (as := as.map (mapTy id)) (bs := as)
    (τ := mapTy id τ) (υ := τ) (o := (Hom.identity S).op o) (p := o)
    (by simp) (by simp) (by simp [Hom.identity]) (envMap_identity M.base args)

/-- Intrinsic signature translation respects composition. -/
theorem mapTerm_comp {S T U : Language} (f : Hom S T) (g : Hom T U)
    {Γ τ} (t : Term S.source Γ τ) :
    HEq (mapTerm (f.comp g) t) (mapTerm g (mapTerm f t)) := by
  induction t with
  | var x =>
      simp only [mapTerm]
      congr 1 <;> simp [List.map_map]
      exact (by rw [mapTy_comp]; exact var_map_comp _ _ x)
  | lam t ih => simp only [mapTerm]; congr 1 <;> simp_all [List.map_map]
  | app t u iht ihu => simp only [mapTerm]; congr 1 <;> simp_all [List.map_map]
  | op o args ih =>
      simp only [mapTerm]
      congr 1 <;> simp [List.map_map]
      · exact Hom.comp_op f g o
      · change HEq
          (reindexTuple (mapTy (f.comp g).base) (fun _ x => mapTerm (f.comp g) (args _ x)))
          (reindexTuple (mapTy g.base) (Tuple.map (fun a (v : Term T.source _ a) => mapTerm g v)
            (reindexTuple (mapTy f.base) (fun _ x => mapTerm f (args _ x)))))
        rw [reindexTuple_natural]
        exact (reindexTuple_congr (by simp [List.map_map])
          (by simp only [Hom.comp_base, mapTy_comp]; rfl) _ _ ih).trans
          (reindexTuple_comp _ _ _)

/-- Restriction along a composite is successive restriction. -/
theorem reduct_comp {S T U : Language} (f : Hom S T) (g : Hom T U)
    (M : SetModel U.source) : reduct (f.comp g) M = reduct f (reduct g M) := by
  refine SetModel.ext rfl ?_
  apply heq_of_eq
  funext as τ o args
  change (carrierMap (g.base ∘ f.base) M.base τ).symm
    (M.op ((f.comp g).op o) (envMap (g.base ∘ f.base) M.base args)) =
    (carrierMap f.base (M.base ∘ g.base) τ).symm
      ((carrierMap g.base M.base (mapTy f.base τ)).symm
        (M.op (g.op (f.op o)) (envMap g.base M.base (envMap f.base (M.base ∘ g.base) args))))
  apply eq_of_heq
  apply equiv_symm_trans_heq (by simp) _ _ _ (carrierMap_comp _ _ _ _)
  exact M.op_heq (by simp [List.map_map]) (by simp)
    (Hom.comp_op f g o) (envMap_comp _ _ _ _)

theorem mapSentence_identity {S : Language} (p : Sentence S) :
    mapSentence (Hom.identity S) p = p := by
  cases p with
  | equation t u =>
      simp only [mapSentence]
      congr 1 <;> simp [Hom.identity]
      all_goals exact mapTerm_identity _

theorem mapSentence_comp {S T U : Language} (f : Hom S T) (g : Hom T U)
    (p : Sentence S) : mapSentence (f.comp g) p = mapSentence g (mapSentence f p) := by
  cases p with
  | equation t u =>
      simp only [mapSentence]
      congr 1 <;> simp [List.map_map]
      all_goals exact mapTerm_comp f g _

private theorem arrow_hext {S : Language} {M M' N N' : Model S}
    (hM : M = M') (hN : N = N') (f : M ⟶ N) (g : M' ⟶ N') : HEq f g := by
  cases hM; cases hN
  exact heq_of_eq (Subsingleton.elim _ _)

theorem reductFunctor_identity (S : Language) :
    reductFunctor (Hom.identity S) = 𝟭 (Model S) := by
  have h : ∀ M : Model S, pullModel (Hom.identity S) M = M :=
    fun M => Algebraic.Lambda.LambdaModel.ext (reduct_identity M.toSetModel)
  apply Functor.hext h
  intro M N f
  exact arrow_hext (h M) (h N) _ _

theorem reductFunctor_comp {S T U : Language} (f : Hom S T) (g : Hom T U) :
    reductFunctor (f.comp g) = reductFunctor g ⋙ reductFunctor f := by
  have h : ∀ M : Model U, pullModel (f.comp g) M = pullModel f (pullModel g M) :=
    fun M => Algebraic.Lambda.LambdaModel.ext (reduct_comp f g M.toSetModel)
  apply Functor.hext h
  intro M N a
  exact arrow_hext (h M) (h N) _ _


end Silmaril.Logic.STLCEquations
