module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Version.Defs
import Silmaril.SSA.LambdaRTL.CFG.Thms
import Silmaril.SSA.LambdaRTL.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicRenaming

open Silmaril.Elgot
open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG Silmaril.SSA.LambdaRTL.CFG.Cyclic

universe v w

variable {V K : Type w} {F F' : Type v} {M : Type w → Type w} {α : Type w}
  [DecidableEq V] [DecidableEq K] [Monad M] [LawfulMonad M]

private theorem exec_mapOp (rename : F → F') (model : Model F' M α) {R : Type w}
    (next : K → α → (V → α) → M R) (body : Body V K F) (store : V → α) :
    (body.mapOp rename).exec model next store = body.exec (model.reduct rename) next store := by
  simp only [Body.exec_eq_evalRTL, Body.toRegion_mapOp, Region.evalRTL_mapOp]

omit [DecidableEq V] in
private theorem lookup_mapOp (rename : F → F') (table : List (K × Block V K F)) (label : K) :
    (table.map fun item => (item.1, item.2.mapOp rename)).lookup label =
      (table.lookup label).map (Block.mapOp rename) := by
  induction table with
  | nil => rfl
  | cons item rest ih =>
    rcases item with ⟨key, block⟩
    by_cases same : label = key
    · subst key
      simp only [List.map_cons, List.lookup_cons, beq_self_eq_true, Option.map_some]
    · simp only [List.map_cons, List.lookup_cons, beq_false_of_ne same, ih]

private theorem step_mapOp (rename : F → F') (model : Model F' M α)
    (table : List (K × Block V K F)) (transfer : Transfer V K α) :
    Cyclic.step model (table.map fun item => (item.1, item.2.mapOp rename)) transfer =
      Cyclic.step (model.reduct rename) table transfer := by
  rw [Cyclic.step, lookup_mapOp, Cyclic.step]
  cases table.lookup transfer.1 <;> simp [Block.mapOp, exec_mapOp]

private theorem stepSSA_mapOp (rename : F → F') (model : Model F' M α)
    (table : List (K × Block V K F)) (input : V → α) (transfer : K × α) :
    Cyclic.stepSSA model (table.map fun item => (item.1, item.2.mapOp rename)) input transfer =
      Cyclic.stepSSA (model.reduct rename) table input transfer := by
  rw [Cyclic.stepSSA, lookup_mapOp, Cyclic.stepSSA]
  cases table.lookup transfer.1 <;> simp [Block.mapOp, Body.evalJump, exec_mapOp]

variable [Iterate M]

theorem run_mapOp (rename : F → F') (model : Model F' M α) (graph : CFG V K F) (store : V → α) :
    Cyclic.run model (graph.mapOp rename) store = Cyclic.run (model.reduct rename) graph store := by
  simp only [Cyclic.run, CFG.mapOp, exec_mapOp, funext (step_mapOp rename model graph.blocks)]

theorem runSSA_mapOp (rename : F → F') (model : Model F' M α) (graph : CFG V K F) (input : V → α) :
    Cyclic.runSSA model (graph.mapOp rename) input = Cyclic.runSSA (model.reduct rename) graph input := by
  simp only [Cyclic.runSSA, CFG.mapOp, Body.evalJump, exec_mapOp,
    funext (stepSSA_mapOp rename model graph.blocks input)]

end Silmaril.Proofs.SSA.LambdaRTL.CFG.CyclicRenaming
