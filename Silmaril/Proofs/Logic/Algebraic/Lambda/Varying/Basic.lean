module

public import Silmaril.Logic.Algebraic.Lambda.Varying.Defs

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Algebraic.Lambda.Varying
open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Calculi.TypedLambda Silmaril.Calculi.LambdaCube
open Silmaril.Calculi.LambdaCube.STLC
open Cslib.LambdaCalculus.LocallyNameless.Stlc

theorem mapOperation_original {A D : EQ.Signature} (f : A ⟶ D)
    {n w s} (o : A.Op n w s) :
    HEq (mapOperation f (.original o)) (Operation.original (f.ops o)) := by
  simp [mapOperation]

theorem signatureMap_identity (A : EQ.Signature) :
    signatureMap (𝟙 A) = STLCEquations.Hom.identity (language A) := by
  refine STLCEquations.Hom.ext (f := _) (g := _) rfl ?_
  apply heq_of_eq
  funext as τ o
  apply eq_of_heq
  cases o with
  | original o =>
      apply (mapOperation_original (𝟙 A) o).trans
      simp [STLCEquations.Hom.identity]
      rfl

theorem signatureMap_comp {A D E : EQ.Signature} (f : A ⟶ D) (g : D ⟶ E) :
    signatureMap (f ≫ g) = (signatureMap f).comp (signatureMap g) := by
  refine STLCEquations.Hom.ext (f := _) (g := _) rfl ?_
  apply heq_of_eq
  funext as τ o
  apply eq_of_heq
  cases o with
  | original o =>
      have hi := (signatureMap g).op_heq (context_map f.sorts _) rfl
        (mapOperation_original f o)
      have hr := (STLCEquations.Hom.comp_op (signatureMap f) (signatureMap g)
        (Operation.original o)).trans (hi.trans (mapOperation_original g (f.ops o)))
      exact (mapOperation_original (f ≫ g) o).trans hr.symm

theorem contextVar_map {B D : Type} (f : B → D) {n : Nat} (w : Fin n → B) (i : Fin n) :
    HEq ((contextVar w i).map (mapTy f)) (contextVar (f ∘ w) i) := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change HEq (Var.zero : Var ((context w).map (mapTy f)) (.base (f (w 0))))
          (Var.zero : Var (context (f ∘ w)) (.base (f (w 0))))
        congr 1
        simp [context_map, Function.comp_def]
      · change HEq (((contextVar (fun i => w i.succ) j).map (mapTy f)).succ)
          ((contextVar (fun i => f (w i.succ)) j).succ)
        congr 1 <;> first | exact ih (fun i => w i.succ) j | simp [context_map, Function.comp_def]

theorem reindex_envTuple {B D : Type} (f : B → D) {n : Nat} (w : Fin n → B)
    (X : Ty D → Type) (ρ : ∀ i, X (.base (f (w i)))) :
    HEq (reindexTuple (mapTy f) (envTuple w (fun τ => X (mapTy f τ)) ρ))
      (envTuple (f ∘ w) X ρ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [context, envTuple, reindexTuple]
      congr 1 <;> first | exact ih (fun i => w i.succ) (fun i => ρ i.succ) | simp [context_map, Function.comp_def]

theorem envTuple_heq {B : Type} {n : Nat} (w : Fin n → B) {X Y : Ty B → Type}
    (hXY : X = Y) {ρ : ∀ i, X (.base (w i))} {σ : ∀ i, Y (.base (w i))}
    (h : ∀ i, HEq (ρ i) (σ i)) : HEq (envTuple w X ρ) (envTuple w Y σ) := by
  cases hXY
  exact heq_of_eq (congrArg (envTuple w X) (funext fun i => eq_of_heq (h i)))

theorem term_naturality {A D : EQ.Signature} (f : A ⟶ D)
    {n : Nat} {Γ : Fin n → A.S} {s : A.S} (t : EQ.Term A Γ s) :
    HEq (STLCEquations.mapTerm (signatureMap f) (term t)) (term (t.map f)) := by
  induction t with
  | var i =>
      simp only [term, STLCEquations.mapTerm, EQ.Term.map]
      congr 1 <;> simp [signatureMap, context_map]
      exact contextVar_map f.sorts Γ i
  | app o args ih =>
      simp only [term, STLCEquations.mapTerm, EQ.Term.map]
      congr 1 <;> simp [signatureMap, context_map]
      · exact mapOperation_original f o
      · have h :
            (fun a x => STLCEquations.mapTerm (signatureMap f)
              (envTuple _ (fun τ => Term (signature A) (context Γ) τ)
                (fun i => term (args i)) a x)) =
              envTuple _ (fun τ => Term (signature D)
                ((context Γ).map (mapTy f.sorts)) (mapTy f.sorts τ))
                (fun i => STLCEquations.mapTerm (signatureMap f) (term (args i))) :=
            envTuple_map _ _ _ _ _
        apply (heq_of_eq (congrArg (reindexTuple (mapTy f.sorts)) h)).trans
        apply (reindex_envTuple f.sorts _ _ _).trans
        exact envTuple_heq _ (by funext τ; rw [context_map]; rfl) ih

theorem compile_naturality {A D : EQ.Signature} (f : A ⟶ D) (e : EQ.Equation A) :
    STLCEquations.mapSentence (signatureMap f) (compile e) = compile (e.map f) := by
  cases e
  simp only [compile, EQ.Equation.map, STLCEquations.mapSentence]
  congr 1 <;> simp [signatureMap, context_map]
  all_goals exact term_naturality f _

theorem satisfaction {A : EQ.Signature} (M : STLC.SetModel (signature A))
    (e : EQ.Equation A) : STLCEquations.Holds M (compile e) ↔ e.Holds (reduct M) :=
  satisfies_equation M e

theorem envMap_envTuple {A D : EQ.Signature} (f : A ⟶ D)
    (base : D.S → Type) {n : Nat} (w : Fin n → A.S) (ρ : ∀ i, base (f.sorts (w i))) :
    HEq (envMap f.sorts base (envTuple w (carrier (base ∘ f.sorts)) ρ))
      (envTuple (f.sorts ∘ w) (carrier base) ρ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [context, envTuple, envMap, carrierMap]
      congr 1 <;> first | exact ih (fun i => w i.succ) (fun i => ρ i.succ) | simp [context_map, Function.comp_def]

theorem reduct_naturality {A D : EQ.Signature} (f : A ⟶ D)
    (M : STLC.SetModel (signature D)) :
    reduct (STLCEquations.reduct (signatureMap f) M) =
      (EQ.Algebra.reduct f).obj (reduct M) := by
  unfold reduct EQ.Algebra.reduct STLCEquations.reduct
  congr 1
  funext n w s o args
  change (carrierMap f.sorts M.base (.base s)).symm
      (M.op (mapOperation f (.original o))
        (envMap f.sorts M.base (envTuple w (carrier (M.base ∘ f.sorts)) args))) = _
  change M.op (mapOperation f (.original o))
      (envMap f.sorts M.base (envTuple w (carrier (M.base ∘ f.sorts)) args)) = _
  apply eq_of_heq
  exact M.op_heq (context_map f.sorts w) rfl (mapOperation_original f o)
    (envMap_envTuple f M.base w args)

private theorem algebraHom_heq {A : EQ.Signature} {M M' N N' : EQ.Algebra A}
    (hM : M = M') (hN : N = N') (f : M ⟶ N) (g : M' ⟶ N')
    (h : HEq f.map g.map) : HEq f g := by
  cases hM
  cases hN
  cases f
  cases g
  cases eq_of_heq h
  rfl

theorem modelReduct_naturality {A D : EQ.Signature} (f : A ⟶ D) :
    modelReduct D ⋙ EQ.Algebra.reduct f =
      STLCEquations.reductFunctor (signatureMap f) ⋙ modelReduct A := by
  apply Functor.hext (F := modelReduct D ⋙ EQ.Algebra.reduct f)
    (G := STLCEquations.reductFunctor (signatureMap f) ⋙ modelReduct A)
    (fun M => (reduct_naturality f M.toSetModel).symm)
  intro M N h
  apply algebraHom_heq (reduct_naturality f M.toSetModel).symm
    (reduct_naturality f N.toSetModel).symm
  cases h.down
  rfl

end Silmaril.Logic.Algebraic.Lambda.Varying
