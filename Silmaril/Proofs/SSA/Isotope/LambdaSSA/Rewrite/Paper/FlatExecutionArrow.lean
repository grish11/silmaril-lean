module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.Thms

/-! # The packed CFG denotes the entry followed by feedback in Paper -/

public section

universe u v

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecution

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.FiniteCFG
open Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory
open Silmaril.DeBruijn (lift)
open SyntacticCategory (iterateRegion iterationBody iterationDispatch)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {blocks exits : Nat} {R : Fin blocks → τ} {E : Fin exits → τ}
  {g : FiniteCFG Φ blocks exits 0}

local notation "S" => packedExitType (List.ofFn R)
local notation "Y" => packedExitType (List.ofFn E)
local notation "T" => Silmaril.coprod Y S

private theorem iterationBody_values {Γ : VCtx τ} {p : Region Φ}
    (hp : ValueBranches Γ p [T]) : ValueBranches Γ (iterationBody p) [S, Y] :=
  hp.lsubst (fun _ _ hi =>
    (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸
      SyntacticCategory.iterationDispatch_valueBranches S Y)

theorem packedExecution_context_valueBranches {n : Nat} {β : BoundCtx τ n} {g : FiniteCFG Φ blocks exits n}
    (hg : FiniteCFG.HasType β R E g) :
    ValueBranches β.toList (packedExecutionRegion hg) [Y] :=
  .cfg (fun _ : Fin 1 => S) (iterationBody_values (entry_context_valueBranches hg))
    (fun _ => iterationBody_values (packedDispatcher_valueBranches hg))

theorem packedDispatcher_ofRegion (hg : FiniteCFG.HasType .nil R E g) :
    packedDispatcher hg = ofRegion (packedDispatcher_valueBranches hg) ≫ (sumIso Y S).hom := rfl

private theorem packedExecution_closed_eq (hg : FiniteCFG.HasType .nil R E g) :
    CfgEta.Eqv [] (packedExecutionRegion hg)
      ((routedFlat blocks g.entry).lsubst (fun _ =>
        .case (.var 0) (.br 0 (.var 0))
          ((iterateRegion S (packedDispatcherRegion hg)).renameVars (lift Nat.succ)))) [Y] := by
  have entry := entry_closed_valueBranches hg
  have body := packedDispatcher_valueBranches hg
  refine (CfgEta.seqCont entry (SyntacticCategory.iterationDispatch_valueBranches S Y)
    (iterationBody_values body)).trans (CfgEta.lsubst_congr entry ?_)
  intro i A hi
  cases List.mem_singleton.mp (List.mem_of_getElem? hi)
  exact .native (SyntacticCategory.iterationDispatch_cfg body)

set_option backward.isDefEq.respectTransparency false in
theorem packedExecution_ofRegion (hg : FiniteCFG.HasType .nil R E g) :
    packedExecution hg = ofRegion ((packedExecution_context_valueBranches hg).renameVars (SSA.Ren.wk [] Silmaril.unit)) := by
  have body := packedDispatcher_valueBranches hg
  have hiter : Region.Paper.TypeCategory.iterate (packedDispatcher hg) =
      ofRegion (SyntacticCategory.iterateRegion_valueBranches body) := by
    rw [packedDispatcher_ofRegion]
    change iterateSum ((ofRegion body ≫ (sumIso Y S).hom) ≫ (sumIso Y S).inv) = _
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id, iterateSum_ofRegion]
  rw [packedExecution, packedEntry, hiter, Category.assoc, ← ofRegion_id (Φ := Φ) Y,
    coprod_desc_ofRegion]
  let route := CfgEta.TypeCategory.caseValueBranches
    (show ValueBranches [Y] (.br 0 (.var 0) : Region Φ) [Y] from .br rfl (.var rfl))
    (SyntacticCategory.iterateRegion_valueBranches body)
  let decode := Region.case (.var 0) (.br 0 (.var 0))
    ((iterateRegion S (packedDispatcherRegion hg)).renameVars (lift Nat.succ))
  have incoming : LSubst.ValueFamily [] [Silmaril.unit] [T]
      (fun _ => (routedFlat blocks g.entry).renameVars Nat.succ) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ entry_valueBranches hg
  have outgoing : LSubst.ValueFamily [] [T] [Y] (fun _ => decode) :=
    fun _ _ hi => (List.mem_singleton.mp (List.mem_of_getElem? hi)).symm ▸ route
  have values := (incoming.comp outgoing) (show At [Silmaril.unit] 0 (Silmaril.unit : τ) from rfl)
  rw [ofRegion_comp (entry_valueBranches hg) route values, ofRegion_eq_iff]
  apply Region.Paper.Eqv.cfgEta
  have eq := (packedExecution_closed_eq hg).renameVars (SSA.Ren.wk [] Silmaril.unit)
  rw [renameVars_lsubst] at eq
  exact eq.symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecution
