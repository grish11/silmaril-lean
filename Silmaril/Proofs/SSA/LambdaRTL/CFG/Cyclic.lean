module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Correctness

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.Elgot

universe v w
variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [Monad M] [LawfulMonad M] [Iterate M] [LawfulElgotMonad M] [DecidableEq V] [DecidableEq K]

private theorem iter_step_eq_jump (model : Model F M α)
    (table suffix : List (K × Block V K F)) (forward : ForwardTargets table suffix)
    (label : K) (value : α) (store : V → α) (lookup : table.lookup label = suffix.lookup label) :
    iter (step model table) (label, value, store) = jump model suffix label value store := by
  induction suffix generalizing label value store with
  | nil =>
    have unfoldStep := congrFun (LawfulElgotMonad.fixpoint (step model table)) (label, value, store)
    simpa [step, lookup, jump] using unfoldStep
  | cons block rest ih =>
    obtain ⟨targets, restForward⟩ := forward
    by_cases hit : label = block.1
    · subst label
      have lookupHit : table.lookup block.1 = some block.2 := by
        simpa [List.lookup] using lookup
      rw [show iter (step model table) (block.1, value, store) =
          step model table (block.1, value, store) >>= Sum.elim pure (iter (step model table))
          from congrFun (LawfulElgotMonad.fixpoint _) _]
      rw [jump, ite_eq_left rfl]
      simp only [step, lookupHit]
      calc
        _ = block.2.body.exec model (fun label value store => iter (step model table)
            (label, value, store)) (upd store block.2.param value) := by
              simp only [Body.exec_eq, bind_assoc, pure_bind, Sum.elim_inr]
        _ = _ := by
          apply Body.exec_congr
          intro target ht
          funext payload next
          exact ih restForward target payload next (targets target ht)
    · have lookupRest : table.lookup label = rest.lookup label := by
        simpa [List.lookup, beq_false_of_ne hit] using lookup
      simpa only [jump, ite_eq_right hit] using ih restForward label value store lookupRest

theorem run_eq_forward (model : Model F M α) (graph : CFG V K F)
    (forward : IsForward graph) (store : V → α) :
    Cyclic.run model graph store = graph.run model store := by
  unfold Cyclic.run CFG.run
  apply Body.exec_congr
  intro label _
  funext value next
  exact iter_step_eq_jump model graph.blocks graph.blocks forward label value next rfl

theorem iter_project_of_step_encoding {Output Target : Type w} (model : Model F M α)
    (table : List (K × Block V K F)) (project : Transfer V K α → Output)
    (encode : Transfer V K α → Target)
    (targetStep : Target → M (Output ⊕ Target))
    (commutes : ∀ transfer,
      Sum.map project encode <$> step model table transfer = targetStep (encode transfer))
    (initial : Transfer V K α) :
    project <$> iter (step model table) initial = iter targetStep (encode initial) := by
  let observed := mapReturn (step model table) (fun result => pure (project result))
  have square : (observed >=> liftPure (Sum.map id encode)) =
      (liftPure encode >=> targetStep) := by
    funext transfer
    change (observed transfer >>= liftPure (Sum.map id encode)) =
      (pure (encode transfer) >>= targetStep)
    rw [pure_bind, ← commutes transfer, ← bind_pure_comp]
    simp only [observed, mapReturn, bind_assoc]
    congr 1
    funext result
    cases result <;> simp [liftPure]
  have natural := congrFun
    (LawfulElgotMonad.naturality (step model table) (fun result => pure (project result))) initial
  have uniform := congrFun
    (LawfulElgotMonad.uniformity observed targetStep encode square) initial
  have result := natural.trans uniform
  change (iter (step model table) initial >>= fun exit => pure (project exit)) =
    (pure (encode initial) >>= iter targetStep) at result
  simpa using result

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic
