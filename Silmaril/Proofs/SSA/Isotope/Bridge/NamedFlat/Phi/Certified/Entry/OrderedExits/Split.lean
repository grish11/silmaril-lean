module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Thms
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split.Defs
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.Thms
public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split.Thms
import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits.Thms
import Silmaril.SSA.LambdaRTL.CFG.Thms
import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split

open Silmaril.Isotope
open Silmaril.Isotope.Bridge
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry (Captures)
open Silmaril.Isotope.Bridge.NamedFlat
open Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits
open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi (Graph br)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.OrderedExits
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan)
open Silmaril.Elgot (mapReturn)
open Silmaril.Elgot.ITree (Tree resume iterate_naturality)
open LambdaSSA.Semantics.Interaction (Primitive)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open NamedFlat.Entry.Record (Input)

universe u v
variable {V W K J α : Type (u + 1)} {F : Type v} {E : Type u → Type u}
  [DecidableEq V] [DecidableEq W] [DecidableEq K] [DecidableEq J]
variable (plan : Plan V W K J) (instr : Primitive E F α) (source : Graph V K F)

private def renameExit (p : Option K × Value α) : Option J × Value α :=
  (p.1.map plan.label, p.2)

private def routed (p : Pending V K (Value α)) : Pending W J (Value α) :=
  (p.1.map plan.label, plan.route p.1 p.2.1, p.2.2.1, plan.renameStore p.2.2.2)

-- Arrival after the optional forwarding hop. Internal branch payloads are
-- ignored by φ entry, but an external payload must be retained exactly.
private def aligned (p : Pending V K (Value α)) : Pending W J (Value α) :=
  match p with
  | (pred, some target, value, store) =>
    (plan.rekey target pred, some (plan.label target),
      if plan.selected pred target then .unit else value, plan.renameStore store)
  | (pred, none, value, store) => (pred.map plan.label, none, value, plan.renameStore store)

omit [DecidableEq J] in
private theorem execute_routed (pred : Option K) (body : CFG.Body V (Option K) F)
    (store : V → Value α) :
    execute (treeModel instr) (pred.map plan.label) (plan.renameBody (plan.route pred) body)
        (plan.renameStore store) =
      routed plan <$> execute (treeModel instr) pred body store := by
  unfold execute
  rw [plan.exec_rename, CFG.Body.exec_eq_evalRTL, CFG.Body.exec_eq_evalRTL]
  simp only [← bind_pure_comp, bind_assoc, pure_bind]
  rfl

private theorem step_aligned (header : (source.blocks.lookup plan.header).isSome = true)
    (p : Pending V K (Value α)) :
    step (treeModel instr) (plan.rewrite source) (aligned plan p) =
      Sum.map id (routed plan) <$> mapReturn (step (treeModel instr) source)
        (fun exit => pure (renameExit plan exit)) p := by
  obtain ⟨pred, target, value, store⟩ := p
  cases target with
  | none => simp [step, aligned, lookup, mapReturn, renameExit]
  | some key =>
    cases old : source.blocks.lookup key with
    | none =>
      have other : ¬ plan.selected pred key := by
        rintro ⟨_, rfl⟩
        simp [old] at header
      simp [step, aligned, lookup, plan.lookup_renamed, old, mapReturn, renameExit, other]
    | some block =>
      simp only [step, aligned, lookup, Option.bind_some, plan.lookup_renamed, old, Option.map_some,
        Plan.renameBlock, plan.assign_rename]
      have renamed := execute_routed plan instr (some key) block.body
        (CFG.Cyclic.Phi.assign (treeModel instr) pred store block.rows store)
      simp only [Option.map_some] at renamed
      rw [renamed]
      simp [step, lookup, old, mapReturn, ← bind_pure_comp, bind_assoc]

omit [DecidableEq V] in
private theorem hop (edge : plan.hasEdge source = true) (p : Pending V K (Value α)) :
    routed plan p = aligned plan p ∨
      step (treeModel instr) (plan.rewrite source) (routed plan p) = pure (.inr (aligned plan p)) := by
  obtain ⟨pred, target, value, store⟩ := p
  cases target with
  | none => exact .inl rfl
  | some key =>
    by_cases selected : plan.selected pred key
    · obtain ⟨rfl, rfl⟩ := selected
      right
      simp [routed, aligned, Plan.route, Plan.rekey, Plan.selected, step, lookup,
        plan.lookup_forward source edge, Plan.forwardBlock, CFG.Cyclic.Phi.assign,
        execute, CFG.Body.exec, br, CFG.Term.exec, Val.eval, treeModel]
    · exact .inl (by simp [routed, aligned, Plan.route, Plan.rekey, selected])

theorem run_rewrite (edge : plan.hasEdge source = true)
    (header : (source.blocks.lookup plan.header).isSome = true) (store : V → Value α) :
    CFG.Cyclic.Phi.OrderedExits.run (treeModel instr) source store >>= (fun exit => pure (exit.1.map plan.label, exit.2)) =
      CFG.Cyclic.Phi.OrderedExits.run (treeModel instr) (plan.rewrite source) (plan.renameStore store) := by
  have entry := execute_routed plan instr none source.entry store
  simp only [Option.map_none] at entry
  have sim := Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split.resume_eq_of_hop (routed plan) (aligned plan)
    (hop plan instr source edge) (step_aligned plan instr source header)
    (show Sum.inr <$> execute (treeModel instr) none (plan.rewrite source).entry (plan.renameStore store) =
        Sum.map id (routed plan) <$> (Sum.inr <$> execute (treeModel instr) none source.entry store) by
      change Sum.inr <$> execute (treeModel instr) none (plan.renameBody (plan.route none) source.entry) _ = _
      rw [entry]
      simp only [Functor.map_map]
      rfl)
  rw [CFG.Cyclic.Phi.OrderedExits.run, CFG.Cyclic.Phi.OrderedExits.run, bind_assoc]
  change (_ >>= (Silmaril.Elgot.iter (step (treeModel instr) source) >=> _)) = _
  rw [iterate_naturality]
  simpa only [resume, ← bind_pure_comp, bind_assoc, pure_bind, Sum.elim_inr, renameExit] using sim

section Entry

open LambdaSSA (FiniteCFG)

variable {κ Reg : Type (u + 1)} [AtomValues κ]
  {P : FlatInstitution.Signature.{u, v} κ} {I : NamedFlat.Entry.Interface κ Reg (Option K)}
  {fields : Option K → List (Reg × Ty κ)} {C : Captures V I.context}

omit [DecidableEq V] [DecidableEq W] in
private theorem ordered_number (plan : Plan V W K K) {keys : List (Option K)}
    (exits : keys.map (Option.map plan.label) = keys) (exit : Option K × Value α) :
    treeExitNumber keys (renameExit plan exit) = treeExitNumber keys exit := by
  have injective := Option.map_injective plan.label.injective
  suffices idx :
      keys.findIdx? (fun key => @BEq.beq _ instBEqOfDecidableEq (exit.1.map plan.label) key) =
      keys.findIdx? (fun key => @BEq.beq _ instBEqOfDecidableEq exit.1 key) by
    simpa only [treeExitNumber, treeNumber, renameExit, ← List.findIdx?_eq_map_findFinIdx?_val]
      using congrArg (fun idx => (idx.getD keys.length, exit.2)) idx
  conv_lhs => rw [← exits, List.findIdx?_map]
  congr 1
  funext key
  exact Bool.eq_iff_iff.mpr (by
    simp only [Function.comp_apply, beq_iff_eq]
    exact ⟨fun eq => injective eq, congrArg _⟩)

theorem observe_eq (plan : Plan V W K K) (a : Admission P I fields C)
    (b : Admission P I fields (C.rename plan.register)) (checked : CheckedSplit plan a.source b.source)
    (exits : I.exits.map (Option.map plan.label) = I.exits)
    (M : LambdaSSA.Semantics.Interaction.Typed.Ordered.Model (κ := κ) E P.Instr) (record : Input I.context) :
    a.observe M record = b.observe M record := by
  simp only [Admission.observe, checked.rewritten, Captures.store_rename]
  change (_ >>= _) = (CFG.Cyclic.Phi.OrderedExits.run (treeModel M.raw) (plan.rewrite a.source)
    (plan.renameStore (C.store record)) >>= _)
  rw [← run_rewrite plan M.raw a.source checked.edge checked.header, bind_assoc]
  apply bind_congr
  intro exit
  rw [pure_bind]
  exact congrArg (fun p => pure (FiniteCFG.packedTreeOutput p)) (ordered_number plan exits exit).symm

end Entry

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Split
