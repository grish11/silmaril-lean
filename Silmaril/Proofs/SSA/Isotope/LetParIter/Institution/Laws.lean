module

public import Silmaril.SSA.Isotope.LetParIter.Institution.Defs

public section

namespace Silmaril.Isotope.LetParIter.Institution.Proofs

open CategoryTheory Parallel LetIter.ProofRelevant.Semantics
open Silmaril.Isotope.Institution (InstrSig)

universe u v w

variable {τ ε : Type u} [TypeFormers τ]
variable {ν : Type w} [DecidableEq ν]
variable {P Q R : InstrSig τ ε}
variable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A B C : τ}

theorem map_cast (σ : P ⟶ Q) (h : A = B) (a : Expr P Γ β A) :
    (a.cast h).map σ = (a.map σ).cast h := by
  cases h
  rfl

theorem cast_cast (h : A = B) (k : B = C) (a : Expr P Γ β A) :
    (a.cast h).cast k = a.cast (h.trans k) := by
  cases h
  cases k
  rfl

theorem map_op (σ : P ⟶ Q) (f : P.Instr) (a : Expr P Γ β (instrSrc f)) :
    (Expr.op f a).map σ = Expr.relabelOp σ f (a.map σ) := rfl

theorem map_relabelOp (σ : P ⟶ Q) (θ : Q ⟶ R) (f : P.Instr)
    (a : Expr Q Γ β (instrSrc f)) :
    (Expr.relabelOp σ f a).map θ = Expr.relabelOp (σ ≫ θ) f (a.map θ) := by
  simp only [Expr.relabelOp, map_cast, map_op, cast_cast]
  rfl

theorem expr_map_id (a : Expr P Γ β A) : a.map (𝟙 P) = a := by
  obtain ⟨_, d⟩ := a
  induction d with
  | fv | bv | unit => rfl
  | op _ h => exact congrArg (Expr.op _) h
  | let₁ _ _ ha hb => exact congrArg₂ Expr.let₁ ha hb
  | pair _ _ ha hb => exact congrArg₂ Expr.pair ha hb
  | let₂ _ _ ha hb => exact congrArg₂ Expr.let₂ ha hb
  | inl _ h => exact congrArg Expr.inl h
  | inr _ h => exact congrArg Expr.inr h
  | case _ _ _ he hl hr => exact congr (congrArg₂ Expr.case he hl) hr
  | abort _ h => exact congrArg Expr.abort h
  | iter _ _ ha hb => exact congrArg₂ Expr.iter ha hb
  | par _ _ ha hb => exact congrArg₂ Expr.par ha hb

theorem expr_map_comp (σ : P ⟶ Q) (θ : Q ⟶ R) (a : Expr P Γ β A) :
    (a.map σ).map θ = a.map (σ ≫ θ) := by
  obtain ⟨_, d⟩ := a
  induction d with
  | fv | bv | unit => rfl
  | op da ih =>
      change (Expr.relabelOp σ _ (Expr.mapDerivation σ da)).map θ = _
      rw [map_relabelOp]
      exact congrArg (Expr.relabelOp (σ ≫ θ) _) ih
  | let₁ _ _ ha hb => exact congrArg₂ Expr.let₁ ha hb
  | pair _ _ ha hb => exact congrArg₂ Expr.pair ha hb
  | let₂ _ _ ha hb => exact congrArg₂ Expr.let₂ ha hb
  | inl _ h => exact congrArg Expr.inl h
  | inr _ h => exact congrArg Expr.inr h
  | case _ _ _ he hl hr => exact congr (congrArg₂ Expr.case he hl) hr
  | abort _ h => exact congrArg Expr.abort h
  | iter _ _ ha hb => exact congrArg₂ Expr.iter ha hb
  | par _ _ ha hb => exact congrArg₂ Expr.par ha hb

theorem sentence_map_id (s : Sentence P ν) : s.map (𝟙 P) = s := by
  cases s
  simp only [Sentence.map, expr_map_id]

theorem sentence_map_comp (σ : P ⟶ Q) (θ : Q ⟶ R) (s : Sentence P ν) :
    (s.map σ).map θ = s.map (σ ≫ θ) := by
  cases s
  simp only [Sentence.map, expr_map_comp]

variable [Subtyping τ] [Bot ε] [TypeModel.{u, v} τ]

open Model (transport reduct)

theorem reduct_id (P : InstrSig τ ε) : reductFunctor (𝟙 P) = 𝟭 (Model P) := rfl

omit [TypeFormers τ] [Subtyping τ] [TypeModel τ] in
theorem transport_transport {D : τ → Sort w} (h : A = B) (k : B = C) (x : D A) :
    transport D k (transport D h x) = transport D (h.trans k) x := by
  cases h
  cases k
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem reduct_comp_obj (σ : P ⟶ Q) (θ : Q ⟶ R) (M : Model R) :
    reduct (σ ≫ θ) M = reduct σ (reduct θ M) := by
  unfold reduct
  congr 1
  congr 1
  · funext f a
    change Model.restrictInstr (σ ≫ θ) M f a =
      transport (fun T => M.Carrier (TyDen T)) (σ.target f)
        (Model.restrictInstr θ M (σ.instr f)
        (transport TyDen (σ.source f).symm a))
    simp only [Model.restrictInstr, transport_transport]
    rfl
  · funext f hf a
    change Model.restrictPureInstr (σ ≫ θ) M f hf a =
      transport TyDen (σ.target f) (Model.restrictPureInstr θ M (σ.instr f) _
        (transport TyDen (σ.source f).symm a))
    simp only [Model.restrictPureInstr, transport_transport]
    rfl

theorem eqToHom_app {M N : Model P} (h : M = N) {X : Type v} (x : M.Carrier X) :
    (eqToHom h).app x = cast (congrArg (fun K => K.Carrier X) h) x := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem reduct_comp (σ : P ⟶ Q) (θ : Q ⟶ R) :
    reductFunctor (σ ≫ θ) = reductFunctor θ ⋙ reductFunctor σ := by
  refine CategoryTheory.Functor.ext (fun M => reduct_comp_obj σ θ M) (fun M N F => ?_)
  apply Model.Hom.ext
  funext X x
  rw [Model.comp_app, Model.comp_app]
  change F.app x = (eqToHom (reduct_comp_obj σ θ N).symm).app
    (F.app ((eqToHom (reduct_comp_obj σ θ M)).app x))
  rw [eqToHom_app, eqToHom_app]
  rfl

theorem eval_cast (M : Model P) (h : A = B) (a : Expr P Γ β A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    M.eval (a.cast h) γ ρ = transport (fun T => M.Carrier (TyDen T)) h (M.eval a γ ρ) := by
  cases h
  rfl

theorem bind_cast (M : Model P) (h : A = B) (x : M.Carrier (TyDen A))
    (k : TyDen B → M.Carrier (TyDen C)) :
    M.bind (transport (fun T => M.Carrier (TyDen T)) h x) k =
      M.bind x (fun a => k (transport TyDen h a)) := by
  cases h
  rfl

theorem cast_bind (M : Model P) {X : Type v} (h : A = B) (x : M.Carrier X)
    (k : X → M.Carrier (TyDen A)) :
    transport (fun T => M.Carrier (TyDen T)) h (M.bind x k) =
      M.bind x (fun a => transport (fun T => M.Carrier (TyDen T)) h (k a)) := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem eval_relabelOp (σ : P ⟶ Q) (M : Model Q) (f : P.Instr)
    (a : Expr Q Γ β (instrSrc f)) (γ : CtxDen Γ) (ρ : BoundDen β) :
    M.eval (Expr.relabelOp σ f a) γ ρ = M.bind (M.eval a γ ρ) (M.restrictInstr σ f) := by
  rw [Expr.relabelOp, eval_cast]
  change transport (fun T => M.Carrier (TyDen T)) (σ.target f)
    (M.bind (M.eval (a.cast (σ.source f).symm) γ ρ) (M.instructions.denote (σ.instr f))) = _
  rw [eval_cast, cast_bind, bind_cast]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem eval_reduct (σ : P ⟶ Q) (M : Model Q) (a : Expr P Γ β A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    M.eval (a.map σ) γ ρ = (reduct σ M).eval a γ ρ := by
  obtain ⟨_, d⟩ := a
  induction d with
  | op da ih =>
      change M.eval (Expr.relabelOp σ _ (Expr.mapDerivation σ da)) γ ρ = _
      rw [eval_relabelOp]
      exact congrArg (fun x => M.bind x _) (ih ρ)
  | fv | bv | unit => rfl
  | _ =>
      simp_all only [Expr.map, Expr.mapDerivation, Expr.let₁, Expr.pair, Expr.let₂,
        Expr.inl, Expr.inr, Expr.case, Expr.abort, Expr.iter, Expr.par, Model.eval,
        LetParIter.denote, reduct]

set_option backward.isDefEq.respectTransparency false in
theorem eval_hom {M N : Model P} (F : Model.Hom M N)
    (a : Expr P Γ β A) (γ : CtxDen Γ) (ρ : BoundDen β) :
    F.app (M.eval a γ ρ) = N.eval a γ ρ := by
  obtain ⟨_, d⟩ := a
  induction d <;> simp_all only [Model.eval, LetParIter.denote, evalIter, evalPar,
    ← bind_pure_comp, denoteInstr, F.map_pure, F.map_bind, F.map_instr, F.map_iter, F.map_pair]
  · congr 1
    funext x
    split <;> simp_all
  · congr 1
    funext x
    exact Empty.elim (TypeModel.emptyEquiv x)

theorem satisfaction (σ : P ⟶ Q) (M : Model Q) (s : Sentence P ν) :
    Sat M (s.map σ) ↔ Sat (reduct σ M) s := by
  unfold Sat Sentence.map
  simp only [eval_reduct]
  exact Iff.rfl

end Silmaril.Isotope.LetParIter.Institution.Proofs
