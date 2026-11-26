module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.ITree.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecutionRouting

/-! # Event-preserving entry and block routing -/

public section

universe u v w x

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecution

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.FiniteCFG
open Semantics (Env extend)
open Semantics.Interaction
open Region Region.SyntacticCategory
open Silmaril.Elgot.ITree

variable {F : Type w → Type w} {Φ : Type v} {α : Type u} (instr : Primitive F Φ α)

private theorem region_lifted (k : Nat → Region Φ) (i : Nat)
    (env : Env α) (ignored payload : Value α) :
    region instr (extend (extend env ignored) payload) (liftLSubstVars k i) =
      region instr (extend env payload) (k i) :=
  region_renameVars instr (k i) (Semantics.extend_rename (fun _ => rfl) payload)

private theorem flat_bind {labels n : Nat} (r : Flat Φ labels n) (k : Nat → Region Φ)
    (env : Env α) :
    region instr env (r.erase.bindBranchArguments.lsubst k) =
      (region instr env r.erase >>= fun p => region instr (extend env p.2) (k p.1)) := by
  induction r generalizing k env with
  | br i a =>
    change (term instr env (Morphism.CaseSSA.erase a) >>= fun v =>
      region instr (extend env v) (compLSubst labelId k i.val)) = _
    simp [compLSubst_id_left, Flat.erase, region]
  | let₁ a b ih =>
    simp [Flat.erase, bindBranchArguments, Region.lsubst, region, bind_assoc, ih, region_lifted]
  | let₂ a b ih =>
    simp only [Flat.erase, bindBranchArguments, Region.lsubst, region, bind_assoc]
    congr 1
    funext val
    cases val <;> simp [ih, region_lifted]
  | case a l r ihl ihr =>
    simp only [Flat.erase, bindBranchArguments, Region.lsubst, region, bind_assoc]
    congr 1
    funext val
    cases val <;> simp [ihl, ihr, region_lifted]

private theorem term_packedExitArg (a : Tm Φ) (i : Nat) (env : Env α) :
    term instr env (packedExitArg i a) =
      (term instr env a >>= fun v => pure (packedExitValue i v)) := by
  induction i with
  | zero => rfl
  | succ i ih => simp [packedExitArg, term, ih, packedExitValue]

private theorem route_tree (blocks i : Nat) (env : Env α) (v : Value α) :
    region instr (extend env v) (routeExit blocks i) = pure (0, routeValue blocks i v) := by
  by_cases h : i < blocks <;> simp [routeExit, routeValue, h, region, term, term_packedExitArg]

theorem routedFlat_tree {labels n : Nat} (blocks : Nat) (r : Flat Φ labels n)
    (env : Env α) :
    region instr env (routedFlat blocks r) =
      (region instr env r.erase >>= fun p => pure (0, routeValue blocks p.1 p.2)) := by
  rw [routedFlat, flat_bind]
  simp only [route_tree]

private theorem route_feedback (blocks i : Nat) (env : Env α) (v : Value α) :
    region instr (extend env v) (compLSubst (routeExit blocks) (fun _ => iterationDispatch) i) =
      pure (packedTreeTransfer blocks (i, v)) := by
  rw [route_comp_dispatch]
  by_cases h : i < blocks <;>
    simp [h, region, term, term_packedExitArg, packedTreeTransfer, splitTransfer,
      packedTreeInput, packedTreeOutput]

theorem routedFlat_feedback_tree {labels n : Nat} (blocks : Nat) (r : Flat Φ labels n)
    (env : Env α) :
    region instr env (iterationBody (routedFlat blocks r)) =
      (region instr env r.erase >>= fun p => pure (packedTreeTransfer blocks p)) := by
  rw [iterationBody, routedFlat, lsubst_comp, flat_bind]
  simp only [route_feedback]

private theorem unpackExits_subst_tree {τ : Type x} [TypeFormers τ] (L : LCtx τ)
    {i : Nat} (hi : i < L.length) (k : Nat → Region Φ) (env : Env α) (v : Value α) :
    region instr (extend env (packedExitValue i v)) ((unpackExits L).lsubst k) =
      region instr (extend (extend env (packedExitValue i v)) v) (k i) := by
  induction L generalizing i k env with
  | nil => simp at hi
  | cons A L ih =>
    cases i with
    | zero =>
      change region instr (extend env (.inl v))
        (.case (.var 0) (compLSubst labelId k 0) _) = _
      simp only [region, term, Semantics.extend_zero, pure_bind, compLSubst_id_left, packedExitValue]
    | succ i =>
      have htail : i < L.length := Nat.lt_of_succ_lt_succ hi
      rw [unpackExits, packedExitValue, Region.lsubst, lsubst_renameLabels]
      simp only [region, term, Semantics.extend_zero, pure_bind]
      rw [ih htail]
      exact region_lifted instr k (i + 1) _ _ v

section Dispatcher

variable {τ : Type x} [TypeFormers τ] [HasTy Φ τ]
  {blocks exits : Nat} {R : Fin blocks → τ} {E : Fin exits → τ}
  {n : Nat} {β : BoundCtx τ n} {g : FiniteCFG Φ blocks exits n}

theorem packedBlock_tree (hg : FiniteCFG.HasType β R E g) (i : Fin blocks)
    (env : Env α) (v : Value α) :
    region instr (extend env (packedExitValue i.val v)) (packedDispatcherRegion hg) =
      (region instr (extend env v) (g.block i).erase >>= fun p => pure (0, routeValue blocks p.1 p.2)) := by
  have hi : i.val < (List.ofFn R).length := by simp
  unfold packedDispatcherRegion
  rw [show ∀ k : Nat → Region Φ,
    compLSubst (fun _ => unpackExits (List.ofFn R)) k 0 =
      (unpackExits (List.ofFn R)).lsubst (liftLSubstVars k) from fun _ => rfl]
  rw [unpackExits_subst_tree instr _ hi, region_lifted instr]
  simpa only [compLSubst, routeFamily, List.length_ofFn, blockFamily, ContinuationFamily.ofTyped,
    dite_eq_left i.isLt, liftLSubstVars_routeExit, routedFlat] using
      routedFlat_tree instr blocks (g.block i) (extend env v)

theorem packedBlock_feedback_tree (hg : FiniteCFG.HasType β R E g) (i : Fin blocks)
    (env : Env α) (v : Value α) :
    region instr (extend env (packedExitValue i.val v)) (iterationBody (packedDispatcherRegion hg)) =
      (region instr (extend env v) (g.block i).erase >>= fun p => pure (packedTreeTransfer blocks p)) := by
  rw [iterationBody_packedDispatcher]
  have hi : i.val < (List.ofFn R).length := by simp
  change region instr (extend env (packedExitValue i.val v))
      ((unpackExits (List.ofFn R)).lsubst (liftLSubstVars (packedBlockContinuations hg))) = _
  rw [unpackExits_subst_tree instr _ hi, region_lifted instr, packedBlockContinuations_at hg i.isLt]
  exact routedFlat_feedback_tree instr blocks (g.block i) (extend env v)

end Dispatcher

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecution
