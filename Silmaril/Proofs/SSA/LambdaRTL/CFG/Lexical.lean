module

public import Silmaril.SSA.LambdaRTL.CFG.Lexical.Defs

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG

universe v w
variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [Monad M] [DecidableEq V] [DecidableEq K]

private theorem term_evalJump (model : Model F M α) (term : Term V K F) (input : V → α) :
    term.exec model (fun target payload _ => pure (target, payload)) input =
      term.toRegion.evalSSA model input := by
  induction term generalizing input with
  | br => rfl
  | case op x left y right ihLeft ihRight =>
    simp only [Term.exec, Term.toRegion, Region.evalSSA]
    congr 1
    funext value
    cases value with
    | inl a => exact ihLeft _
    | inr b => exact ihRight _

private theorem body_evalJump (model : Model F M α) (body : Body V K F) (input : V → α) :
    body.evalJump model input = body.toRegion.evalSSA model input := by
  induction body generalizing input with
  | term term => exact term_evalJump model term input
  | let1 x op body ih =>
    simp only [Body.evalJump, Body.exec, Body.toRegion, Region.evalSSA]
    congr 1
    funext a
    exact ih _
  | let2 x y op body ih =>
    simp only [Body.evalJump, Body.exec, Body.toRegion, Region.evalSSA]
    congr 1
    funext pair
    exact ih _

variable [LawfulMonad M]

private theorem joinAll_evalSSA (model : Model F M α) (input : V → α)
    (region : Region V K F) (blocks : List (K × Block V K F)) :
    (joinAll region blocks).evalSSA model input =
      region.evalSSA model input >>= blocks.foldlM (stepSSA model input) := by
  induction blocks generalizing region with
  | nil => simp [joinAll]
  | cons block tail ih =>
    rw [joinAll, ih]
    simp only [List.foldlM_cons, Region.evalSSA, bind_assoc, stepSSA, body_evalJump]

theorem runSSA_eq_evalSSA (graph : CFG V K F) (model : Model F M α) (input : V → α) :
    graph.runSSA model input = graph.toRegion.evalSSA model input := by
  rw [CFG.runSSA, CFG.toRegion, joinAll_evalSSA, body_evalJump]

end Silmaril.Proofs.SSA.LambdaRTL.CFG
