module

public import Silmaril.SSA.Isotope.Institution.Adapters.Iteration.Defs
import Silmaril.SSA.Isotope.Parallel.Hierarchy.Thms

@[expose] public section

namespace Silmaril.Isotope.Institution.Adapters.Iteration.Proofs

open CategoryTheory Semantics
open Silmaril.Logic.Metatheory.TheoryModel
open Parallel (Derivation)
open Parallel.Institution (Equation)
open LetParIter.Institution (Expr Sentence Sat)
open LetIter.ProofRelevant.Semantics (TypeModel TyDen CtxDen BoundDen)

universe u v

variable {τ ε : Type u} [TypeFormers τ] {S T : InstrSig τ ε} {ν : Type u} [DecidableEq ν]
  {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A B : τ}

open Silmaril.Isotope.LetIter.LocallyNameless in
private def iterMap (g : S ⟶ T) : {n : Nat} → {β : BoundCtx τ n} → {t : Tm ν S.Instr n} →
    {A : τ} → Derivation S.Instr Γ β t A → Derivation T.Instr Γ β (t.mapInstr g.instr) A
  | _, _, _, _, .fv h => .fv h
  | _, _, _, _, .bv => .bv
  | _, _, _, _, .op (f := f) a =>
      g.target f ▸ .op (f := g.instr f) ((g.source f).symm ▸ iterMap g a)
  | _, _, _, _, .let₁ a b => .let₁ (iterMap g a) (iterMap g b)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair a b => .pair (iterMap g a) (iterMap g b)
  | _, _, _, _, .let₂ a b => .let₂ (iterMap g a) (iterMap g b)
  | _, _, _, _, .inl a => .inl (iterMap g a)
  | _, _, _, _, .inr b => .inr (iterMap g b)
  | _, _, _, _, .case e l r => .case (iterMap g e) (iterMap g l) (iterMap g r)
  | _, _, _, _, .abort a => .abort (iterMap g a)
  | _, _, _, _, .iter a b => .iter (iterMap g a) (iterMap g b)

private abbrev iterFold (f : S ⟶ T) {k : Nat} {bound : BoundCtx τ k}
    {a : Silmaril.Isotope.LetIter.LocallyNameless.Tm ν S.Instr k} {X : τ}
    (d : Silmaril.Isotope.LetIter.LocallyNameless.Derivation S.Instr Γ bound a X) :
    Relational.LetIter.Program T Γ ⟨k, bound, X⟩ :=
  Silmaril.Isotope.LetIter.LocallyNameless.Models.denote
    (Algebra.reductObj (Silmaril.Isotope.Institution.LetIter.sigHom Γ f)
      (Silmaril.Isotope.LetIter.LocallyNameless.Models.syntaxAlgebra T.Instr Γ)) d

private theorem iterTranslate (f : S ⟶ T) {k : Nat} {bound : BoundCtx τ k}
    {a : Silmaril.Isotope.LetIter.LocallyNameless.Tm ν S.Instr k} {X : τ}
    (d : Silmaril.Isotope.LetIter.LocallyNameless.Derivation S.Instr Γ bound a X) :
    Relational.LetIter.Program.translate f (i := ⟨k, bound, X⟩) ⟨a, d⟩ = ⟨a.mapInstr f.instr, iterMap f d⟩ := by
  refine (Relational.LetIter.Program.translate_eq_fold f
    (i := ⟨k, bound, X⟩) ⟨a, d⟩).trans ?_
  change iterFold f d = _
  induction d with
  | fv | bv | unit => rfl
  | @op k bound op a d ih =>
      refine (Relational.LetIter.Program.translate_eq_fold f
        (i := ⟨k, bound, instrTrg op⟩) ⟨.op op a, .op d⟩).symm.trans ?_
      refine (Relational.LetIter.Program.translate_op f op ⟨a, d⟩).trans ?_
      erw [Relational.LetIter.Program.translate_eq_fold f (i := ⟨k, bound, instrSrc op⟩) ⟨a, d⟩]
      change (⟨.op (f.instr op) (iterFold f d).1,
        f.target op ▸ .op ((f.source op).symm ▸ (iterFold f d).2)⟩ :
          Relational.LetIter.Program T Γ ⟨k, bound, instrTrg op⟩) = _
      rw [ih]
      rfl
  | @let₁ k bound a b X Y dl dr ihp ihq =>
      exact congrArg₂ (fun (p : Relational.LetIter.Program T Γ ⟨k, bound, X⟩)
        (q : Relational.LetIter.Program T Γ ⟨k + 1, bound.snoc X, Y⟩) =>
        (⟨.let₁ p.1 q.1, .let₁ p.2 q.2⟩ : Relational.LetIter.Program T Γ ⟨k, bound, Y⟩)) ihp ihq
  | @pair k bound a b X Y dl dr ihp ihq =>
      exact congrArg₂ (fun (p : Relational.LetIter.Program T Γ ⟨k, bound, X⟩)
        (q : Relational.LetIter.Program T Γ ⟨k, bound, Y⟩) =>
        (⟨.pair p.1 q.1, .pair p.2 q.2⟩ : Relational.LetIter.Program T Γ ⟨k, bound, product X Y⟩)) ihp ihq
  | @let₂ k bound a b X Y Z dl dr ihp ihq =>
      exact congrArg₂ (fun (p : Relational.LetIter.Program T Γ ⟨k, bound, product X Y⟩)
        (q : Relational.LetIter.Program T Γ ⟨k + 2, (bound.snoc X).snoc Y, Z⟩) =>
        (⟨.let₂ p.1 q.1, .let₂ p.2 q.2⟩ : Relational.LetIter.Program T Γ ⟨k, bound, Z⟩)) ihp ihq
  | @inl k bound a X Y d ihp =>
      exact congrArg (fun (p : Relational.LetIter.Program T Γ ⟨k, bound, X⟩) =>
        (⟨.inl p.1, .inl p.2⟩ : Relational.LetIter.Program T Γ ⟨k, bound, coprod X Y⟩)) ihp
  | @inr k bound a X Y d ihp =>
      exact congrArg (fun (p : Relational.LetIter.Program T Γ ⟨k, bound, Y⟩) =>
        (⟨.inr p.1, .inr p.2⟩ : Relational.LetIter.Program T Γ ⟨k, bound, coprod X Y⟩)) ihp
  | @case k bound e l r X Y Z de dl dr ihp ihq ihr =>
      exact congrArg₂ (fun (p : Relational.LetIter.Program T Γ ⟨k, bound, coprod X Y⟩)
        (branches : Relational.LetIter.Program T Γ ⟨k + 1, bound.snoc X, Z⟩ × Relational.LetIter.Program T Γ ⟨k + 1, bound.snoc Y, Z⟩) =>
        (⟨.case p.1 branches.1.1 branches.2.1, .case p.2 branches.1.2 branches.2.2⟩ :
          Relational.LetIter.Program T Γ ⟨k, bound, Z⟩)) ihp (congrArg₂ Prod.mk ihq ihr)
  | @abort k bound a X d ihp =>
      exact congrArg (fun (p : Relational.LetIter.Program T Γ ⟨k, bound, empty⟩) =>
        (⟨.abort p.1, .abort p.2⟩ : Relational.LetIter.Program T Γ ⟨k, bound, X⟩)) ihp
  | @iter k bound a b X Y dl dr ihp ihq =>
      exact congrArg₂ (fun (p : Relational.LetIter.Program T Γ ⟨k, bound, X⟩)
        (q : Relational.LetIter.Program T Γ ⟨k + 1, bound.snoc X, coprod Y X⟩) =>
        (⟨.iter p.1 q.1, .iter p.2 q.2⟩ : Relational.LetIter.Program T Γ ⟨k, bound, Y⟩)) ihp ihq

private theorem case_cast {t : LetParCase.Tm ν T.Instr n} (h : A = B)
    (d : Derivation T.Instr Γ β t A) :
    Expr.ofLetParCase (Derivation.castResult h d) = (Expr.ofLetParCase d).cast h := by
  cases h
  rfl

private theorem iter_cast {t : LetIter.LocallyNameless.Tm ν T.Instr n} (h : A = B)
    (d : LetIter.LocallyNameless.Derivation T.Instr Γ β t A) :
    Expr.ofLetIter (h ▸ d : LetIter.LocallyNameless.Derivation T.Instr Γ β t B) =
      (Expr.ofLetIter d).cast h := by
  cases h
  rfl

private theorem caseExprMap (f : S ⟶ T) {t : LetParCase.Tm ν S.Instr n}
    (d : Derivation S.Instr Γ β t A) :
    (Expr.ofLetParCase d).map f = Expr.ofLetParCase (d.mapInstr f) := by
  induction d with
  | @op k b t op d ih =>
      change Expr.relabelOp f op ((Expr.ofLetParCase d).map f) =
        Expr.ofLetParCase (Derivation.castResult (f.target op)
          (.op (Derivation.castResult (f.source op).symm (d.mapInstr f))))
      rw [ih, case_cast]
      change _ = (Expr.op (f.instr op)
        (Expr.ofLetParCase (Derivation.castResult (f.source op).symm (d.mapInstr f)))).cast _
      rw [case_cast]
      rfl
  | iter => exact nomatch ‹Parallel.Tier.HasIter .case›
  | fv | bv | unit => rfl
  | let₁ a b iha ihb =>
      change Expr.let₁ ((Expr.ofLetParCase a).map f) ((Expr.ofLetParCase b).map f) =
        Expr.let₁ (Expr.ofLetParCase (a.mapInstr f)) (Expr.ofLetParCase (b.mapInstr f))
      erw [iha, ihb]
  | pair a b iha ihb =>
      change Expr.pair ((Expr.ofLetParCase a).map f) ((Expr.ofLetParCase b).map f) =
        Expr.pair (Expr.ofLetParCase (a.mapInstr f)) (Expr.ofLetParCase (b.mapInstr f))
      erw [iha, ihb]
  | let₂ a b iha ihb =>
      change Expr.let₂ ((Expr.ofLetParCase a).map f) ((Expr.ofLetParCase b).map f) =
        Expr.let₂ (Expr.ofLetParCase (a.mapInstr f)) (Expr.ofLetParCase (b.mapInstr f))
      erw [iha, ihb]
  | inl a iha =>
      change Expr.inl ((Expr.ofLetParCase a).map f) =
        Expr.inl (Expr.ofLetParCase (a.mapInstr f))
      erw [iha]
  | inr a iha =>
      change Expr.inr ((Expr.ofLetParCase a).map f) =
        Expr.inr (Expr.ofLetParCase (a.mapInstr f))
      erw [iha]
  | case e l r ihe ihl ihr =>
      change Expr.case ((Expr.ofLetParCase e).map f) ((Expr.ofLetParCase l).map f) ((Expr.ofLetParCase r).map f) =
        Expr.case (Expr.ofLetParCase (e.mapInstr f)) (Expr.ofLetParCase (l.mapInstr f)) (Expr.ofLetParCase (r.mapInstr f))
      erw [ihe, ihl, ihr]
      rfl
  | abort a iha =>
      change Expr.abort ((Expr.ofLetParCase a).map f) =
        Expr.abort (Expr.ofLetParCase (a.mapInstr f))
      erw [iha]
      rfl
  | par a b iha ihb =>
      change Expr.par ((Expr.ofLetParCase a).map f) ((Expr.ofLetParCase b).map f) =
        Expr.par (Expr.ofLetParCase (a.mapInstr f)) (Expr.ofLetParCase (b.mapInstr f))
      erw [iha, ihb]

private theorem iterExprMap (f : S ⟶ T) {t : LetIter.LocallyNameless.Tm ν S.Instr n}
    (d : LetIter.LocallyNameless.Derivation S.Instr Γ β t A) :
    (Expr.ofLetIter d).map f = Expr.ofLetIter (iterMap f d) := by
  induction d with
  | @op k b op t d ih =>
      change Expr.relabelOp f op ((Expr.ofLetIter d).map f) =
        Expr.ofLetIter (f.target op ▸
          LetIter.LocallyNameless.Derivation.op (f := f.instr op) ((f.source op).symm ▸ iterMap f d))
      rw [ih, iter_cast]
      change _ = (Expr.op (f.instr op)
        (Expr.ofLetIter ((f.source op).symm ▸ iterMap f d))).cast _
      rw [iter_cast]
      rfl
  | fv | bv | unit => rfl
  | let₁ a b iha ihb =>
      change Expr.let₁ ((Expr.ofLetIter a).map f) ((Expr.ofLetIter b).map f) =
        Expr.let₁ (Expr.ofLetIter (iterMap f a)) (Expr.ofLetIter (iterMap f b))
      erw [iha, ihb]
  | pair a b iha ihb =>
      change Expr.pair ((Expr.ofLetIter a).map f) ((Expr.ofLetIter b).map f) =
        Expr.pair (Expr.ofLetIter (iterMap f a)) (Expr.ofLetIter (iterMap f b))
      erw [iha, ihb]
  | let₂ a b iha ihb =>
      change Expr.let₂ ((Expr.ofLetIter a).map f) ((Expr.ofLetIter b).map f) =
        Expr.let₂ (Expr.ofLetIter (iterMap f a)) (Expr.ofLetIter (iterMap f b))
      erw [iha, ihb]
  | inl a iha =>
      change Expr.inl ((Expr.ofLetIter a).map f) =
        Expr.inl (Expr.ofLetIter (iterMap f a))
      erw [iha]
  | inr a iha =>
      change Expr.inr ((Expr.ofLetIter a).map f) =
        Expr.inr (Expr.ofLetIter (iterMap f a))
      erw [iha]
  | case e l r ihe ihl ihr =>
      change Expr.case ((Expr.ofLetIter e).map f) ((Expr.ofLetIter l).map f) ((Expr.ofLetIter r).map f) =
        Expr.case (Expr.ofLetIter (iterMap f e)) (Expr.ofLetIter (iterMap f l)) (Expr.ofLetIter (iterMap f r))
      erw [ihe, ihl, ihr]
      rfl
  | abort a iha =>
      change Expr.abort ((Expr.ofLetIter a).map f) =
        Expr.abort (Expr.ofLetIter (iterMap f a))
      erw [iha]
      rfl
  | iter a b iha ihb =>
      change Expr.iter ((Expr.ofLetIter a).map f) ((Expr.ofLetIter b).map f) =
        Expr.iter (Expr.ofLetIter (iterMap f a)) (Expr.ofLetIter (iterMap f b))
      erw [iha, ihb]
      rfl

theorem ofLetParCase_map (f : S ⟶ T) (φ : Equation S .case Γ) :
    (ofLetParCase φ).map f = ofLetParCase (φ.map f) := by
  cases φ
  unfold ofLetParCase Sentence.map Equation.map
  congr 1 <;> exact caseExprMap f _

theorem ofLetIter_map (f : S ⟶ T) (φ : Relational.LetIter.Sentence S Γ) :
    (ofLetIter φ).map f = ofLetIter (Relational.LetIter.Sentence.translate f φ) := by
  rw [Relational.LetIter.Sentence.translate_endpoints]
  obtain ⟨⟨depth, bound, result⟩, ⟨l, dl⟩, ⟨r, dr⟩⟩ := φ
  simp only [ofLetIter, Sentence.map]
  erw [iterTranslate f dl, iterTranslate f dr]
  congr 1 <;> exact iterExprMap f _

variable [Subtyping τ] [Bot ε] [TypeModel.{u, v} τ]

attribute [local instance] LetParIter.nativeProductModel LetParIter.nativeUnitModel
  nativeCoproductModel nativeEmptyModel

theorem nativeBound_get (ρ : BoundEnv (TyDen (τ := τ)) β) :
    BoundDen.get (nativeBound ρ) = ρ := by
  induction β with
  | nil => exact funext fun i => Fin.elim0 i
  | snoc β A ih =>
      funext i
      refine Fin.cases rfl (fun j => ?_) i
      exact congrFun (ih (fun j => ρ j.succ)) j

theorem caseModel_reduct (f : S ⟶ T) :
    LetParIter.Institution.reductFunctor f ⋙ caseModelFunctor.{u, v} =
      caseModelFunctor ⋙ Parallel.Institution.Model.reductFunctor f := by
  rfl

private theorem lower_caseControl (M : LetParIter.Institution.Model.{u, v} S) :
    Parallel.Institution.lowerControl (by decide) (Parallel.Control.case (TyDen (τ := τ)) Id)
      M.Carrier = LetParIter.Institution.caseControl τ M.Carrier := by
  have h : (Parallel.Institution.lowerControl (by decide)
      (Parallel.Control.case (TyDen (τ := τ)) Id) M.Carrier).loop =
      (LetParIter.Institution.caseControl τ M.Carrier).loop :=
    funext fun h => nomatch h
  exact congrArg (fun loop => { LetParIter.Institution.caseControl τ M.Carrier with loop }) h

private theorem eval_ofLetParCase (M : LetParIter.Institution.Model.{u, v} S)
    {t : LetParCase.Tm ν S.Instr n} (d : Derivation S.Instr Γ β t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    M.eval (Expr.ofLetParCase d) γ ρ = M.evalLetParCase d γ ρ := by
  rw [← LetParIter.Institution.Model.evalShared_eq_eval]
  exact Parallel.Hierarchy.denote_case_reduct (caseModel M).instr (caseModel M).par
    LetParIter.nativeControl d (visibleEnv γ) (BoundDen.get ρ)

theorem ofLetParCase_sat (hΓ : Function.Surjective (visibleEnv.{u, v} (Γ := Γ)))
    (M : LetParIter.Institution.Model.{u, v} S) (φ : Equation S .case Γ) :
    Sat M (ofLetParCase φ) ↔
      ((LetParCase.observation Γ (TyDen (τ := τ))).obj S).Sat (caseModel M) φ := by
  simp only [ofLetParCase, Sat, eval_ofLetParCase]
  change _ ↔ φ.Holds (caseModel M) _
  rw [lower_caseControl]
  constructor
  · intro h γ ρ
    obtain ⟨native, rfl⟩ := hΓ γ
    let satisfiesAt := fun (ρ : BoundEnv (TyDen (τ := τ)) φ.bound) =>
      φ.lhs.denote TyDen (caseModel M).instr (caseModel M).par
        (LetParIter.Institution.caseControl τ M.Carrier) (visibleEnv native) ρ =
      φ.rhs.denote TyDen (caseModel M).instr (caseModel M).par
        (LetParIter.Institution.caseControl τ M.Carrier) (visibleEnv native) ρ
    change satisfiesAt ρ
    rw [← nativeBound_get ρ]
    exact h native (nativeBound ρ)
  · intro h γ ρ
    exact h (visibleEnv γ) (BoundDen.get ρ)

theorem ofLetIter_sat (M : LetParIter.Institution.Model.{u, v} S)
    (φ : Relational.LetIter.Sentence S Γ) : Sat M (ofLetIter φ) ↔ IterSat M φ :=
  LetParIter.Institution.satisfaction_ofLetIter M φ.2.1.2 φ.2.2.2

theorem visibleEnv_nil_surjective :
    Function.Surjective (visibleEnv.{u, v} (Γ := (.nil : Ctx ν τ))) := by
  intro γ
  refine ⟨PUnit.unit, ?_⟩
  funext x A h
  simp [Ctx.lookup] at h

/-- The two native sequential interpreters agree on the same coercion-free witness. -/
theorem evalLetIter_eq (M : LetParIter.Institution.Model.{u, v} S)
    {t : LetIter.LocallyNameless.Tm ν S.Instr n}
    (d : LetIter.LocallyNameless.Derivation S.Instr Γ β t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    M.evalLetIter d γ ρ =
      d.denote TyDen (caseModel M).instr (visibleEnv γ) (BoundDen.get ρ) := by
  induction d <;> simp only [LetParIter.Institution.Model.evalLetIter, LetParIter.nativeTyping,
    LetIter.ProofRelevant.Semantics.denote, LetIter.LocallyNameless.Derivation.denote] at *
  case fv => rfl
  case unit => rfl
  case op _ ih => rw [ih]
  case let₁ _ _ iha ihb =>
    rw [iha]
    congr 1
    funext a
    exact ihb (ρ, a)
  case pair _ _ iha ihb =>
    rw [iha]
    congr 1
    funext a
    rw [ihb]
    rfl
  case let₂ _ _ iha ihb =>
    rw [iha]
    congr 1
    funext ab
    exact ihb _
  case inl _ ih =>
    rw [ih]
    rfl
  case inr _ ih =>
    rw [ih]
    rfl
  case case k bound scrutinee left right X Y Z he hl hr ihe ihl ihr =>
    rw [ihe]
    congr 1
    funext e
    rw [show CoproductModel.coprodEquiv (D := TyDen) X Y e = TypeModel.coprodEquiv X Y e from rfl]
    cases TypeModel.coprodEquiv X Y e
    · exact ihl _
    · exact ihr _
  case abort _ ih =>
    rw [ih]
    congr 1
    funext z
    exact (TypeModel.emptyEquiv z).elim
  case iter _ _ iha ihb =>
    rw [iha]
    congr 1
    congr 1
    funext a
    erw [ihb (ρ, a)]
    rfl

theorem set_satisfaction (hΓ : Function.Surjective (visibleEnv.{u, v} (Γ := Γ)))
    (pair : Elgot.ParallelPairing (SetM : Type v → Type v))
    (I : LetIter.ProofRelevant.Semantics.InstructionModel S.Instr τ ε SetM)
    (φ : Relational.LetIter.Sentence S Γ) :
    Sat (setModel pair I) (ofLetIter φ) ↔
      Relational.LetIter.Sentence.Satisfies (setRelations I) φ := by
  rw [ofLetIter_sat]
  have endpoint {t : LetIter.LocallyNameless.Tm ν S.Instr φ.1.depth}
      (d : LetIter.LocallyNameless.Derivation S.Instr Γ φ.1.bound t φ.1.result)
      (γ : CtxDen Γ) (ρ : BoundDen φ.1.bound) (b : TyDen φ.1.result) :
      b ∈ ((setModel pair I).evalLetIter d γ ρ).run ↔
        d.denoteRelation TyDen (setRelations I) (visibleEnv γ) (BoundDen.get ρ) b := by
    rw [evalLetIter_eq]
    exact (d.denoteRelation_iff_mem TyDen (setRelations I) (visibleEnv γ) (BoundDen.get ρ) b).symm
  constructor
  · intro h γ ρ b
    obtain ⟨native, rfl⟩ := hΓ γ
    have hEq := h native (nativeBound ρ)
    have hb := (endpoint φ.2.1.2 native (nativeBound ρ) b).symm.trans
      ((hEq ▸ Iff.rfl : b ∈ ((setModel pair I).evalLetIter φ.2.1.2 native (nativeBound ρ)).run ↔
        b ∈ ((setModel pair I).evalLetIter φ.2.2.2 native (nativeBound ρ)).run).trans
        (endpoint φ.2.2.2 native (nativeBound ρ) b))
    simpa only [nativeBound_get] using hb
  · intro h γ ρ
    apply Set.ext
    intro b
    exact (endpoint φ.2.1.2 γ ρ b).trans
      ((h (visibleEnv γ) (BoundDen.get ρ) b).trans (endpoint φ.2.2.2 γ ρ b).symm)

end Silmaril.Isotope.Institution.Adapters.Iteration.Proofs
