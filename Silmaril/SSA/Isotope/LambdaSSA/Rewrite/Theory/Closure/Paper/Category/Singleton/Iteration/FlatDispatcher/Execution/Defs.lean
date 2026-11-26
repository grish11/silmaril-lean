module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Reflection.Thms

/-! # The guarded entry and packed execution of a flat CFG -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.FiniteCFG

open CategoryTheory CategoryTheory.Limits
open Region Region.Paper.TypeCategory
open SyntacticCategory (iterationBody)

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {blocks exits : Nat} {R : Fin blocks → τ} {E : Fin exits → τ}
  {g : FiniteCFG Φ blocks exits 0}

local notation "S" => packedExitType (List.ofFn R)
local notation "Y" => packedExitType (List.ofFn E)

theorem entry_context_valueBranches {n : Nat} {β : BoundCtx τ n} {g : FiniteCFG Φ blocks exits n}
    (hg : HasType β R E g) :
    ValueBranches β.toList (routedFlat blocks g.entry) [Silmaril.coprod Y S] := by
  have entry : Region.HasType β.toList g.entry.erase (List.ofFn R ++ List.ofFn E) := by
    simpa using hg.entry.erase
  have routed := entry.bindBranchArguments.lsubst
    (routeFamily (List.ofFn R) (List.ofFn E) β.toList).property
  simpa only [routedFlat, routeFamily, List.length_ofFn] using routed

theorem entry_closed_valueBranches (hg : HasType .nil R E g) :
    ValueBranches [] (routedFlat blocks g.entry) [Silmaril.coprod Y S] :=
  entry_context_valueBranches hg

/-- The written entry supplies its own inputs. The singleton unit input
serves only to give a closed entry an arrow out of a singleton object. -/
theorem entry_valueBranches (hg : HasType .nil R E g) :
    ValueBranches [Silmaril.unit] ((routedFlat blocks g.entry).renameVars Nat.succ)
      [Silmaril.coprod Y S] :=
  (entry_closed_valueBranches hg).renameVars (SSA.Ren.wk [] Silmaril.unit)

/-- Run the written entry, returning an external payload or a packed block
state in the exact order of the dispatcher's coproduct. -/
noncomputable def packedEntry (hg : HasType .nil R E g) :
    ofType (Φ := Φ) (Silmaril.unit : τ) ⟶ ofType Y ⨿ ofType S :=
  ofRegion (entry_valueBranches hg) ≫ (sumIso Y S).hom

section WithEntryContext

variable {n : Nat} {β : BoundCtx τ n} {g : FiniteCFG Φ blocks exits n}

/-- The literal dispatcher shares the graph's typed entry context with its
blocks. A transfer supplies just the selected block's local argument. -/
def packedDispatcherRegion (hg : HasType β R E g) : Region Φ :=
  compLSubst (fun _ => unpackExits (List.ofFn R))
    (compLSubst (blockFamily hg).val (routeFamily (List.ofFn R) (List.ofFn E) β.toList).val) 0

theorem packedDispatcher_valueBranches (hg : HasType β R E g) :
    ValueBranches (S :: β.toList) (packedDispatcherRegion hg) [Silmaril.coprod Y S] :=
  ((unpackExits_valueFamily β.toList (List.ofFn R)).comp
    ((blockFamily hg).property.comp (routeFamily (List.ofFn R) (List.ofFn E) β.toList).property))
    (show At [S] 0 S from rfl)

/-- Close the packed recurrence leg with a single local label.
An external transfer from the entry leaves the CFG directly. -/
def packedExecutionRegion (hg : HasType β R E g) : Region Φ :=
  .cfg (iterationBody (routedFlat blocks g.entry)) 1 (fun _ =>
    iterationBody (packedDispatcherRegion hg))

end WithEntryContext

/-- Execute the entry once, feeding a packed state to the dispatcher only
when the entry selects an internal label. -/
noncomputable def packedExecution (hg : HasType .nil R E g) :
    ofType (Φ := Φ) (Silmaril.unit : τ) ⟶ ofType Y :=
  packedEntry hg ≫ coprod.desc (𝟙 (ofType Y)) (Region.Paper.TypeCategory.iterate (packedDispatcher hg))

end Silmaril.Isotope.LambdaSSA.FiniteCFG
