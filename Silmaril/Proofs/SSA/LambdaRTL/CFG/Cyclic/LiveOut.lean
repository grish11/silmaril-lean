module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut.Defs
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Thms
import Silmaril.SSA.LambdaRTL.CFG.Thms

public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.LiveOut

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut
open Silmaril.Elgot

universe v w
variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}
  [Monad M] [DecidableEq V] [DecidableEq K]

omit [Monad M] [DecidableEq V] [DecidableEq K] in
theorem reads_eval (model : Model F M α) (σ : V → α) (fields : List V) :
    (reads fields).eval model σ = Version.packVal model σ fields := by
  induction fields <;> simp_all only [reads, Val.eval, Version.packVal]

omit [DecidableEq K] in
private theorem term_exec (model : Model F M α) (isExit : K → Bool) (fields : K → List V)
    {R : Type w} (next : K → α → (V → α) → M R) (body : Term V K F) (σ : V → α) :
    (attachTerm isExit fields body).exec model next σ =
      body.exec model (fun k value store => next k
        (if isExit k then model.pair value (Version.packVal model store (fields k)) else value) store) σ := by
  induction body generalizing σ with
  | br k arg =>
    cases hit : isExit k <;> simp [attachTerm, Term.exec, hit, Val.eval, reads_eval]
  | case op x left y right ihl ihr =>
    simp only [attachTerm, Term.exec]
    congr 1
    funext reply
    cases reply
    · exact ihl _
    · exact ihr _

omit [DecidableEq K] in
private theorem body_exec (model : Model F M α) (isExit : K → Bool) (fields : K → List V)
    {R : Type w} (next : K → α → (V → α) → M R) (body : Body V K F) (σ : V → α) :
    (attachBody isExit fields body).exec model next σ =
      body.exec model (fun k value store => next k
        (if isExit k then model.pair value (Version.packVal model store (fields k)) else value) store) σ := by
  induction body generalizing σ with
  | term term => exact term_exec model isExit fields next term σ
  | let1 _ _ _ ih | let2 _ _ _ _ ih => simp only [attachBody, Body.exec, ih]

omit [Monad M] [DecidableEq V] in
private theorem lookup_attach (isExit : K → Bool) (fields : K → List V)
    (table : List (K × Block V K F)) (label : K) :
    (table.map fun item => (item.1, Block.mk item.2.param (attachBody isExit fields item.2.body))).lookup label =
      (table.lookup label).map (fun b => Block.mk b.param (attachBody isExit fields b.body)) := by
  induction table with
  | nil => rfl
  | cons item rest ih =>
    simp only [List.map_cons, List.lookup]
    cases label == item.1 <;> simp only [ih, Option.map_some]

variable [LawfulMonad M]

theorem step_commutes (model : Model F M α) (fields : K → List V) (graph : CFG V K F)
    (pending : Transfer V K α) :
    Sum.map (project model fields) (encode model fields graph) <$> Cyclic.step model graph.blocks pending =
      Cyclic.step model (attach fields graph).blocks (encode model fields graph pending) := by
  rcases pending with ⟨label, payload, store⟩
  have key : (encode model fields graph (label, payload, store)).1 = label := by
    simp only [encode]
    split <;> rfl
  unfold Cyclic.step
  rw [key]
  simp only [attach, lookup_attach]
  cases found : graph.blocks.lookup label with
  | none => simp [encode, found]
  | some block =>
    simp only [Option.map_some, encode, found, Option.isNone_some, Bool.false_eq_true, ite_false]
    rw [body_exec]
    simp only [Body.exec_eq_evalRTL, map_bind, map_pure, Sum.map_inr]
    congr 1
    funext out
    simp only [encode, project]
    split <;> rfl

variable [Iterate M] [LawfulElgotMonad M]

theorem run_project (model : Model F M α) (fields : K → List V) (graph : CFG V K F)
    (σ : V → α) :
    Cyclic.run model (attach fields graph) σ = project model fields <$> Cyclic.run model graph σ := by
  unfold Cyclic.run
  change (attachBody (fun k => (graph.blocks.lookup k).isNone) fields graph.entry).exec model _ σ = _
  rw [body_exec]
  simp only [Body.exec_eq_evalRTL, map_bind]
  congr 1
  funext out
  have square := iter_project_of_step_encoding model graph.blocks (project model fields)
    (encode model fields graph) (Cyclic.step model (attach fields graph).blocks)
    (step_commutes model fields graph) out
  cases out with
  | mk label rest =>
    cases rest with
    | mk payload store =>
      apply Eq.trans _ square.symm
      congr 1
      simp only [encode, project]
      split <;> rfl

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.LiveOut
