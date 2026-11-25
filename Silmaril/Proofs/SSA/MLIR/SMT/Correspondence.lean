module

public import Silmaril.SSA.MLIR.SMT.Defs

@[expose] public section

namespace Silmaril.MLIR.SMT.Proofs

open Silmaril.Logic.Smt.Uflia.Quantified

private theorem eval_ref {Γ : Context} {s : Ty} (x : Var Γ s) (env : Env Γ) :
    eval model env.toSmt x.toSmt.term = env.get x := by
  rw [Ref.eval_term]
  induction x with
  | here => cases env; rfl
  | there x ih =>
      cases env with
      | cons value rest =>
          exact (Ref.value_succ model rest.toSmt x.toSmt _ value).trans (ih rest)

set_option backward.isDefEq.respectTransparency false in
private theorem eval_rhs {Γ : Context} {s : Ty} (op : Rhs Γ s) (env : Env Γ) :
    eval model env.toSmt op.toSmt = op.eval env := by
  classical
  cases op <;>
    simp [Rhs.toSmt, Rhs.eval, eval, Silmaril.Logic.Smt.Uflia.Model.apply,
      Fin.cases, Fin.induction, Fin.induction.go, eval_ref]

set_option backward.isDefEq.respectTransparency false in
private theorem eval_quantifier (q : Quantifier) {Γ : Context} (env : Env Γ)
    (ss : List Ty) (target : Formula (Context.bind Γ ss)) (body : Env (Context.bind Γ ss) → Bool)
    (h : ∀ values, eval model values.toSmt target = body values) :
    eval model env.toSmt (q.toSmt ss target) = q.eval env ss body := by
  induction ss generalizing Γ with
  | nil => exact h env
  | cons s ss ih =>
      have pointwise (x : s.Value) :
          eval model (Fin.cases x env.toSmt) (q.toSmt (Γ := s :: Γ) ss target) =
            q.eval (.cons x env) ss body := ih (.cons x env) target body h
      cases q <;> simp only [Quantifier.toSmt, Quantifier.eval, eval]
      all_goals
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq, pointwise]

set_option backward.isDefEq.respectTransparency false in
theorem eval_block {Γ : Context} {s : Ty} (block : Block Γ s) (env : Env Γ) :
    eval model env.toSmt block.toSmt = block.eval env := by
  induction block with
  | yield x => exact eval_ref x env
  | letOp op rest ih =>
      rw [Block.toSmt, eval_instantiate, eval_rhs]
      exact ih (.cons (op.eval env) env)
  | letQuantifier q first others body rest ihBody ihRest =>
      rw [Block.toSmt, eval_instantiate, eval_quantifier q env (first :: others)
        body.toSmt body.eval ihBody]
      exact ihRest (.cons (q.eval env (first :: others) body.eval) env)

end Silmaril.MLIR.SMT.Proofs
