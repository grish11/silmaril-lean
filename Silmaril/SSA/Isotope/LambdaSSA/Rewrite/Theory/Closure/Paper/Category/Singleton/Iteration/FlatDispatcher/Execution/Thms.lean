module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecutionArrow
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecutionFinite

/-! # Whole finite execution of the packed flat CFG -/

public section

universe u v w x

namespace Silmaril.Isotope.LambdaSSA.FiniteCFG

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope (Value)
open Region Region.Paper.TypeCategory
open Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {blocks exits : Nat} {R : Fin blocks → τ} {E : Fin exits → τ}
  {g : FiniteCFG Φ blocks exits 0}
  {α : Type w} {σ : Type x} {instr : Φ → Value α → σ → Value α → σ → Prop}

local notation "S" => packedExitType (List.ofFn R)
local notation "Y" => packedExitType (List.ofFn E)

/-- The shared entry context is retained by the guarded, single-label dispatcher. -/
theorem packedExecution_context_valueBranches {n : Nat} {β : BoundCtx τ n} {g : FiniteCFG Φ blocks exits n}
    (hg : HasType β R E g) :
    ValueBranches β.toList (packedExecutionRegion hg) [Y] :=
  FlatExecution.packedExecution_context_valueBranches hg

theorem packedExecution_closed (hg : HasType .nil R E g) :
    ValueBranches [] (packedExecutionRegion hg) [Y] :=
  packedExecution_context_valueBranches hg

/-- The guarded singleton representative has an unused unit input. -/
theorem packedExecution_valueBranches (hg : HasType .nil R E g) :
    ValueBranches [Silmaril.unit] ((packedExecutionRegion hg).renameVars Nat.succ) [Y] :=
  (packedExecution_closed hg).renameVars (SSA.Ren.wk [] Silmaril.unit)

/-- The packed body is the existing dispatcher, in exact sum coordinates. -/
theorem packedDispatcher_ofRegion (hg : HasType .nil R E g) :
    packedDispatcher hg = ofRegion (packedDispatcher_valueBranches hg) ≫ (sumIso Y S).hom :=
  FlatExecution.packedDispatcher_ofRegion hg

/-- The literal packed CFG represents the written entry followed by dispatcher
feedback in the existing guarded Paper quotient. -/
theorem packedExecution_ofRegion (hg : HasType .nil R E g) :
    packedExecution hg = ofRegion (packedExecution_valueBranches hg) :=
  FlatExecution.packedExecution_ofRegion hg

/-- Tail-first elimination computes the same entry and feedback arrow. -/
theorem packedExecution_eliminateBlocks (hg : HasType .nil R E g) :
    packedExecution hg =
      packedEntry hg ≫ coprod.desc (𝟙 (ofType Y)) (eliminateBlocks (List.ofFn R) (packedDispatcher hg)) := by
  rw [eliminateBlocks_eq_iterate]
  rfl

/-- The written entry and every finite sequence of internal transfers preserve
the original exit index, payload and final primitive state under packing. -/
theorem packedExecution_eval_iff (hg : HasType .nil R E g)
    {env : Semantics.Env α} {start finish : σ} {label : Nat} {out : Value α} :
    Semantics.Region.Eval instr env (packedExecutionRegion hg) start label out finish ↔
      ∃ e v, Semantics.Region.Eval instr env g.erase start e v finish ∧
        label = 0 ∧ out = packedExitValue e v :=
  FlatExecution.packedExecution_eval hg

/-- At a specified exit and payload, the packed run is equivalent to the
original one at exactly the same initial and final primitive states. -/
theorem packedExecution_eval_at (hg : HasType .nil R E g)
    {env : Semantics.Env α} {start finish : σ} {e : Nat} {v : Value α} :
    Semantics.Region.Eval instr env (packedExecutionRegion hg) start 0 (packedExitValue e v) finish ↔
      Semantics.Region.Eval instr env g.erase start e v finish :=
  FlatExecution.packedExecution_eval_at hg

/-- Observe the exact singleton representative used by the quotient equation.
Extending the environment with the dummy input leaves the original run intact. -/
theorem packedExecution_representative_eval_iff (hg : HasType .nil R E g)
    {env : Semantics.Env α} {dummy : Value α} {start finish : σ} {label : Nat} {out : Value α} :
    Semantics.Region.Eval instr (Semantics.extend env dummy)
        ((packedExecutionRegion hg).renameVars Nat.succ) start label out finish ↔
      ∃ e v, Semantics.Region.Eval instr env g.erase start e v finish ∧
        label = 0 ∧ out = packedExitValue e v :=
  (Semantics.Region.Eval.renameVars_iff (fun _ => rfl)).trans (packedExecution_eval_iff hg)

end Silmaril.Isotope.LambdaSSA.FiniteCFG
