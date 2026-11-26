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

omit [DecidableEq K] [DecidableEq J] in
private theorem update {β : Type (u + 1)} (store : V → β) (x : V) (value : β) :
    upd (plan.renameStore store) (plan.register x) value =
      plan.renameStore (upd store x value) := by
  funext y
  obtain ⟨y, rfl⟩ := plan.register.surjective y
  simp [Plan.renameStore, upd]

omit [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J] in
private theorem val_eval (store : V → Value α) (value : Val V) :
    (value.rename plan.register).eval (treeModel instr) (plan.renameStore store) =
      value.eval (treeModel instr) store := by
  induction value with
  | var x => simp [Val.rename, Val.eval, Plan.renameStore]
  | unit => rfl
  | pair a b ihA ihB => simp only [Val.rename, Val.eval, ihA, ihB]

omit [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J] in
private theorem op_eval (store : V → Value α) (op : Op V F) :
    (op.rename plan.register).eval (treeModel instr) (plan.renameStore store) =
      op.eval (treeModel instr) store := by
  cases op <;> simp [Op.rename, Op.eval, val_eval]

omit [DecidableEq K] [DecidableEq J] in
private theorem term_exec {β : Type (u + 1)} (route : Option K → Option J)
    (next : Option J → Value α → (W → Value α) → Tree E β)
    (term : CFG.Term V (Option K) F) (store : V → Value α) :
    (plan.renameTerm route term).exec (treeModel instr) next (plan.renameStore store) =
      term.exec (treeModel instr) (fun k a s => next (route k) a (plan.renameStore s)) store := by
  induction term generalizing store with
  | br key value => simp [Plan.renameTerm, CFG.Term.exec, val_eval]
  | case op x left y right ihL ihR =>
    simp only [Plan.renameTerm, CFG.Term.exec, op_eval, update]
    congr 1
    funext branch
    cases branch <;> simp [ihL, ihR]

omit [DecidableEq K] [DecidableEq J] in
private theorem body_exec {β : Type (u + 1)} (route : Option K → Option J)
    (next : Option J → Value α → (W → Value α) → Tree E β)
    (body : CFG.Body V (Option K) F) (store : V → Value α) :
    (plan.renameBody route body).exec (treeModel instr) next (plan.renameStore store) =
      body.exec (treeModel instr) (fun k a s => next (route k) a (plan.renameStore s)) store := by
  induction body generalizing store with
  | term term => exact term_exec plan instr route next term store
  | let1 x op body ih => simp [Plan.renameBody, CFG.Body.exec, op_eval, update, ih]
  | let2 x y op body ih => simp [Plan.renameBody, CFG.Body.exec, op_eval, update, ih]

omit [DecidableEq J] in
private theorem execute_routed (pred : Option K) (body : CFG.Body V (Option K) F)
    (store : V → Value α) :
    execute (treeModel instr) (pred.map plan.label) (plan.renameBody (plan.route pred) body)
        (plan.renameStore store) =
      routed plan <$> execute (treeModel instr) pred body store := by
  unfold execute
  rw [body_exec, CFG.Body.exec_eq_evalRTL, CFG.Body.exec_eq_evalRTL]
  simp only [← bind_pure_comp, bind_assoc, pure_bind]
  congr 1
  funext result
  obtain ⟨key, value, nextStore⟩ := result
  cases key <;> simp [routed, Plan.route]

private theorem assigned (target : K) (pred : Option K) (rows : List (Row V K))
    (snapshot store : V → Value α) :
    assign (treeModel instr) (plan.rekey target pred) (plan.renameStore snapshot)
        (rows.map (plan.renameRow target)) (plan.renameStore store) =
      plan.renameStore (assign (treeModel instr) pred snapshot rows store) := by
  induction rows generalizing store with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.map_cons, assign, Plan.operand_rename, val_eval]
    change assign (treeModel instr) _ _ _ (upd (plan.renameStore store) (plan.register row.dst) _) = _
    rw [update, ih]

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
        Plan.renameBlock, assigned]
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
