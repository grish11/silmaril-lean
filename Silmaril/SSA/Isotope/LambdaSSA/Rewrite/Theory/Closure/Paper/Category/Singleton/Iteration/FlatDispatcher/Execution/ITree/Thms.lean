module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.ITree.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecutionITreeRouting
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecutionITree

/-!
# Weak interaction-tree preservation for the packed flat CFG

The equality is in the repository's weak interaction-tree model, where
`tau t = t`, but infinite silent computation has no visible root.
In the free instance `Semantics.Interaction.request` both sides expose the same
opcode and evaluated operand, with equal continuations at every reply.
The theorems also allow an arbitrary shared primitive tree interpretation.
-/

public section

universe u v w x

namespace Silmaril.Isotope.LambdaSSA.FiniteCFG

open Silmaril.Isotope (Value)
open Semantics (Env extend)
open Semantics.Interaction
open Region.SyntacticCategory (iterationBody)
open Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {F : Type w → Type w} {Φ : Type v} {α : Type u} (instr : Primitive F Φ α)

/-- The literal routing used by the entry changes only its returned transfer. -/
theorem routedFlat_tree {labels n : Nat} (blocks : Nat) (r : Flat Φ labels n)
    (env : Env α) :
    region instr env (routedFlat blocks r) =
      (region instr env r.erase >>= fun p => pure (0, routeValue blocks p.1 p.2)) :=
  FlatExecution.routedFlat_tree instr blocks r env

/-- The feedback entry runs the original flat code once. Its continuation is
a pure retagging of the original transfer. -/
theorem routedFlat_feedback_tree {labels n : Nat} (blocks : Nat) (r : Flat Φ labels n)
    (env : Env α) :
    region instr env (iterationBody (routedFlat blocks r)) =
      (region instr env r.erase >>= fun p => pure (packedTreeTransfer blocks p)) :=
  FlatExecution.routedFlat_feedback_tree instr blocks r env

variable {τ : Type x} [TypeFormers τ] [HasTy Φ τ]
  {blocks exits : Nat} {R : Fin blocks → τ} {E : Fin exits → τ}
  {n : Nat} {β : BoundCtx τ n} {g : FiniteCFG Φ blocks exits n}

/-- The literal one-step dispatcher executes the original block selected
by the packed tag. Its sum-valued return carries the original payload. -/
theorem packedBlock_tree (hg : HasType β R E g) (i : Fin blocks)
    (env : Env α) (v : Value α) :
    region instr (extend env (Region.packedExitValue i.val v)) (packedDispatcherRegion hg) =
      (region instr (extend env v) (g.block i).erase >>= fun p => pure (0, routeValue blocks p.1 p.2)) :=
  FlatExecution.packedBlock_tree instr hg i env v

/-- Unpacking selects the original written block at the same payload.
The only postprocessing is pure retagging of its transfer. -/
theorem packedBlock_feedback_tree (hg : HasType β R E g) (i : Fin blocks)
    (env : Env α) (v : Value α) :
    region instr (extend env (Region.packedExitValue i.val v))
        (iterationBody (packedDispatcherRegion hg)) =
      (region instr (extend env v) (g.block i).erase >>= fun p => pure (packedTreeTransfer blocks p)) :=
  FlatExecution.packedBlock_feedback_tree instr hg i env v

/-- Whole-program weak ITree equality for the actual literal one-label CFG.
The outward label and payload are related by the original positional packing.
The proof lifts the entry and block equations through weak ITree iteration. -/
theorem packedExecution_tree (hg : HasType β R E g) (env : Env α) :
    region instr env (packedExecutionRegion hg) =
      (region instr env g.erase >>= fun p => pure (packedTreeOutput p)) :=
  FlatExecution.packedExecution_tree instr hg env

/-- The unused input of the guarded singleton representative emits no event. -/
theorem packedExecution_representative_tree {closed : FiniteCFG Φ blocks exits 0}
    (hg : HasType .nil R E closed) (env : Env α) (dummy : Value α) :
    region instr (extend env dummy) ((packedExecutionRegion hg).renameVars Nat.succ) =
      (region instr env closed.erase >>= fun p => pure (packedTreeOutput p)) :=
  (region_renameVars instr (packedExecutionRegion hg) (fun _ => rfl)).trans
    (packedExecution_tree instr hg env)

end Silmaril.Isotope.LambdaSSA.FiniteCFG
