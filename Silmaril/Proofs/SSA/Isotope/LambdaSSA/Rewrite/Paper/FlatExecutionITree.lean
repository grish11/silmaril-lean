module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.FlatDispatcher.Execution.ITree.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecutionITreeRouting

/-! # Transport through the actual CFG feedback -/

public section

universe u v w x

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecution

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.FiniteCFG
open Semantics (Env extend)
open Semantics.Interaction
open Region.SyntacticCategory (iterationBody)
open Silmaril.Elgot (liftPure mapReturn)
open Silmaril.Elgot.ITree

variable {F : Type w → Type w} {Φ : Type v} {α : Type u} (instr : Primitive F Φ α)
  {τ : Type x} [TypeFormers τ] [HasTy Φ τ]
  {blocks exits : Nat} {R : Fin blocks → τ} {E : Fin exits → τ}
  {n : Nat} {β : BoundCtx τ n} {g : FiniteCFG Φ blocks exits n}

private theorem split_packedTreeTransfer (p : Transfer α) :
    splitTransfer 1 (packedTreeTransfer blocks p) =
      Sum.map packedTreeOutput packedTreeInput (splitTransfer blocks p) := by
  unfold packedTreeTransfer
  cases splitTransfer blocks p <;> simp [splitTransfer, packedTreeInput, packedTreeOutput]

/-- Output packing is naturality, and state packing is pure uniformity. -/
private theorem pack_iterate {A B C D : Type u} (f : A → Tree F (B ⊕ A))
    (g : C → Tree F (D ⊕ C)) (output : B → D) (input : A → C)
    (square : ∀ a, (f a >>= fun s => pure (Sum.map output input s)) = g (input a)) (a : A) :
    (iterate f a >>= fun b => pure (output b)) = iterate g (input a) := by
  let f' := mapReturn f (fun b => pure (output b))
  have commute : (f' >=> liftPure (Sum.map id input)) = (liftPure input >=> g) := by
    funext a
    simp only [f', mapReturn, Bind.kleisliRight, liftPure, Function.comp_apply, bind_assoc, pure_bind]
    rw [← square a]
    congr 1
    funext s
    cases s <;> simp
  calc
    _ = iterate f' a := congrFun (iterate_naturality f (fun b => pure (output b))) a
    _ = _ := by
      change Silmaril.Elgot.iter f' a = Silmaril.Elgot.iter g (input a)
      simpa [Bind.kleisliRight, liftPure] using congrFun (iterate_uniformity f' g input commute) a

theorem packedExecution_tree (hg : FiniteCFG.HasType β R E g) (env : Env α) :
    region instr env (packedExecutionRegion hg) =
      (region instr env g.erase >>= fun p => pure (packedTreeOutput p)) := by
  let source : BlockInput α blocks → Tree F (Transfer α ⊕ BlockInput α blocks) :=
    fun p => region instr (extend env p.2) (g.block p.1).erase >>= fun out =>
      pure (splitTransfer blocks out)
  let target : BlockInput α 1 → Tree F (Transfer α ⊕ BlockInput α 1) :=
    fun p => region instr (extend env p.2) (iterationBody (packedDispatcherRegion hg)) >>= fun out =>
      pure (splitTransfer 1 out)
  have loop (p : BlockInput α blocks) :
      (iterate source p >>= fun b => pure (packedTreeOutput b)) = iterate target (packedTreeInput p) := by
    apply pack_iterate
    rintro ⟨i, v⟩
    simp only [target, source, packedTreeInput, packedBlock_feedback_tree instr hg, bind_assoc, pure_bind]
    congr 1
    funext p
    rw [split_packedTreeTransfer]
  change (region instr env (iterationBody (routedFlat blocks g.entry)) >>= fun out =>
      Sum.elim pure (iterate target) (splitTransfer 1 out)) =
    ((region instr env g.entry.erase >>= fun out =>
      Sum.elim pure (iterate source) (splitTransfer blocks out)) >>= fun p => pure (packedTreeOutput p))
  simp only [routedFlat_feedback_tree instr, bind_assoc, pure_bind]
  congr 1
  funext p
  rw [split_packedTreeTransfer]
  cases splitTransfer blocks p with
  | inl p => simp
  | inr p => exact (loop p).symm

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FlatExecution
