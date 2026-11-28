module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Thms
import Silmaril.SSA.LambdaRTL.CFG.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Split

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local
open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph Block Row Pending assign execute)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan Checked)
open Silmaril.Elgot.ITree (Tree)
open LambdaSSA.Semantics.Interaction (Primitive)
open LambdaSSA.FiniteCFG (packedTreeOutput)

universe u v
variable {V W K J α : Type (u + 1)} {F : Type v} {E : Type u → Type u}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J]
variable (plan : Plan V W K J) (instr : Primitive E F α)

/-- The first right transfer names the forwarding block on the split edge. -/
def routed (p : Pending V K (Value α)) : Pending W J (Value α) :=
  (match p.1 with
   | .returned value => .returned value
   | .jump pred target =>
       .jump (pred.map plan.label)
         (if plan.selected pred target then plan.forward else plan.label target),
   plan.renameStore p.2)

/-- The right transfer after the optional forwarding hop. -/
def aligned (p : Pending V K (Value α)) : Pending W J (Value α) :=
  (match p.1 with
   | .returned value => .returned value
   | .jump pred target => .jump (plan.rekey target pred) (plan.label target),
   plan.renameStore p.2)

omit [DecidableEq J] in
private theorem execute_routed (pred : Option K) (body : CFG.Body V (Option K) F)
    (store : V → Value α) :
    execute (treeModel instr) (pred.map plan.label) (plan.renameBody (plan.route pred) body)
        (plan.renameStore store) =
      routed plan <$> execute (treeModel instr) pred body store := by
  unfold execute
  rw [plan.exec_rename, CFG.Body.exec_eq_evalRTL, CFG.Body.exec_eq_evalRTL]
  simp only [← bind_pure_comp, bind_assoc, pure_bind]
  congr 1
  funext result
  obtain ⟨key, value, nextStore⟩ := result
  cases key <;> simp [routed, Plan.route]

omit [DecidableEq J] in
theorem entry_routed (source : Graph V K F) (store : V → Value α) :
    entryTree instr (plan.rewrite source) (plan.renameStore store) =
      Sum.map id (routed plan) <$> entryTree instr source store := by
  simp only [entryTree, Plan.rewrite]
  have renamed := execute_routed plan instr none source.entry store
  simp only [Option.map_none] at renamed
  rw [renamed]
  simp [Functor.map_map]

theorem step_aligned (source : Graph V K F) (p : Pending V K (Value α)) :
    stepTree instr (plan.rewrite source) (aligned plan p) =
      Sum.map id (routed plan) <$> stepTree instr source p := by
  obtain ⟨control, store⟩ := p
  cases control with
  | returned value => simp [aligned, step_return]
  | jump pred target =>
    cases old : source.blocks.lookup target with
    | none =>
      have missing : (plan.rewrite source).blocks.lookup (plan.label target) = none := by
        rw [plan.lookup_renamed, old]
        rfl
      simp [aligned, stepTree, Elgot.mapReturn, CFG.Cyclic.Phi.step, old, missing,
        treeExitNumber, treeNumber, packedTreeOutput]
    | some block =>
      have new : (plan.rewrite source).blocks.lookup (plan.label target) =
          some (plan.renameBlock target block) := by
        rw [plan.lookup_renamed, old]
        rfl
      simp only [aligned, step_jump instr source pred target store old, step_jump instr _ _ _ _ new,
        Plan.renameBlock, plan.assign_rename]
      have renamed := execute_routed plan instr (some target) block.body
        (assign (treeModel instr) pred store block.rows store)
      simp only [Option.map_some] at renamed
      rw [renamed]
      simp [Functor.map_map]

omit [DecidableEq V] in
theorem step_forward (source : Graph V K F) (checked : plan.hasEdge source = true)
    (store : V → Value α) :
    stepTree instr (plan.rewrite source) (.jump (plan.predecessor.map plan.label) plan.forward,
      plan.renameStore store) =
      pure (.inr (.jump (some plan.forward) (plan.label plan.header), plan.renameStore store)) := by
  rw [step_jump instr _ _ _ _ (plan.lookup_forward source checked)]
  simp [Plan.forwardBlock, assign, execute, CFG.Body.exec, CFG.Term.exec, CFG.Cyclic.Phi.br]

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Split
