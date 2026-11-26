module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms
import Silmaril.SSA.SeaOfNodes.GCM.Corridor.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopForest.Thms
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Cfg Edge Frame Terminator)
open Silmaril.MLIR.Pure (Code Operands)
open Silmaril.MLIR.SCF.For (renameOperands)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header
open Loop.MLIR.CF (Program TargetOp evalOp lower model lower_run)

variable {Input Γ Δ args : List Width} {carried result w : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {index : Nat} {cut : Point (SourceLabel carried result)}
variable {out : Cfg TargetOp (SourceLabel carried result) Input [result]}

private theorem renameOperands_eval (rename : Rename Γ Δ) (source : Env Γ) (target : Env Δ)
    (agree : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref)
    (operands : Operands Γ args) :
    (renameOperands rename operands).eval target = operands.eval source := by
  induction operands with
  | nil => rfl
  | cons _ _ ih => simp only [renameOperands, Operands.eval, agree, ih]

private theorem renameEdge_eval (rename : Rename Γ Δ) (source : Env Γ) (target : Env Δ)
    (agree : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref)
    (edge : Edge (SourceLabel carried result) Γ) :
    (renameEdge rename edge).eval target = edge.eval source := by
  simp only [renameEdge, Edge.eval, renameOperands_eval rename source target agree]

private theorem renameTerm_eval (rename : Rename Γ Δ) (source : Env Γ) (target : Env Δ)
    (agree : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref)
    (term : Terminator (SourceLabel carried result) [result] Γ) :
    (renameTerm rename term).eval target = term.eval source := by
  cases term <;> simp only [renameTerm, Terminator.eval, agree, renameEdge_eval rename source target agree,
    renameOperands_eval rename source target agree]

private theorem renameSuffix_eval (code : Block TargetOp (SourceLabel carried result) Γ [result])
    (rename : Rename Γ Δ) (source : Env Γ) (target : Env Δ)
    (agree : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref) :
    (renameSuffix rename code).eval evalOp (fun term env => term.eval env) target =
      code.eval evalOp (fun term env => term.eval env) source := by
  induction code generalizing Δ with
  | terminator term => exact renameTerm_eval rename source target agree term
  | letOp op operands rest ih =>
    simp only [renameSuffix, Code.eval, renameOperands_eval rename source target agree]
    apply ih
    intro _ ref
    cases ref with
    | here => rfl
    | there ref => exact agree ref

private theorem capture_eval (operands : Operands (w :: Γ) args) {early : Operands Γ args}
    (caught : capture? operands = some early) (env : Env Γ) (value : BitVec w.val) :
    early.eval env = operands.eval (.cons value env) := by
  induction operands with
  | nil =>
    cases caught
    rfl
  | cons ref rest ih =>
    cases ref with
    | here => cases caught
    | there ref =>
      obtain ⟨tail, translated, rfl⟩ := Option.map_eq_some_iff.mp caught
      simp only [Operands.eval, Env.get, ih translated]

theorem swapAt?_eval {insertion : Nat}
    {before after : Block TargetOp (SourceLabel carried result) Γ [result]}
    (swapped : swapAt? insertion before = some after) (env : Env Γ) :
    after.eval evalOp (fun term vals => term.eval vals) env =
      before.eval evalOp (fun term vals => term.eval vals) env := by
  induction insertion generalizing Γ with
  | zero =>
    cases before with
    | terminator => cases swapped
    | letOp firstOp firstArgs rest =>
      cases rest with
      | terminator => cases swapped
      | letOp secondOp secondArgs rest =>
        cases caught : capture? secondArgs with
        | none => simp [swapAt?, caught] at swapped
        | some earlierArgs =>
          simp [swapAt?, caught] at swapped
          subst after
          simp only [Code.eval]
          have firstEval :
              (renameOperands Var.there firstArgs).eval
                  (.cons (evalOp secondOp (earlierArgs.eval env)) env) = firstArgs.eval env :=
            renameOperands_eval Var.there env _ (fun _ => rfl) firstArgs
          have secondEval := capture_eval secondArgs caught env (evalOp firstOp (firstArgs.eval env))
          rw [firstEval, secondEval]
          apply renameSuffix_eval
          intro _ ref
          cases ref with
          | here => rfl
          | there ref => cases ref <;> rfl
  | succ insertion ih =>
    cases before with
    | terminator => cases swapped
    | letOp op operands rest =>
      obtain ⟨body, swappedRest, rfl⟩ := Option.map_eq_some_iff.mp swapped
      exact ih swappedRest (.cons (evalOp op (operands.eval env)) env)

theorem pickAndEmit?_spec
    {emit : Cfg TargetOp (SourceLabel carried result) Input [result] →
      Nat → Point (SourceLabel carried result) →
      Option (Cfg TargetOp (SourceLabel carried result) Input [result])}
    (picked : pickAndEmit? g index emit = some (cut, out)) :
    (∃ (saved : Width) (binding : Binding Input (carried :: Input) saved carried result),
      findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨saved, binding⟩ ∧
      chooseCut? g binding.operands binding.uses = some cut) ∧
    emit (lower g) index cut = some out := by
  unfold pickAndEmit? at picked
  obtain ⟨⟨saved, binding⟩, found, chosen⟩ := Option.bind_eq_some_iff.mp picked
  obtain ⟨point, selected, emitted⟩ := Option.bind_eq_some_iff.mp chosen
  obtain ⟨cfg, rewritten, eq⟩ := Option.bind_eq_some_iff.mp emitted
  cases eq
  exact ⟨⟨saved, binding, found, selected⟩, rewritten⟩

private theorem moved_spec {cfg : Cfg TargetOp (SourceLabel carried result) Input [result]}
    (moved : moveAt? cfg index cut = some out) :
    cut.block = headerId ∧ afterRemoval index cut.cut + 1 = index ∧
    ∃ header, swapAt? (afterRemoval index cut.cut) (cfg.block .header) = some header ∧
      out = withHeader cfg header := by
  by_cases atInsertion : cut.block = headerId ∧ afterRemoval index cut.cut + 1 = index
  · simp only [moveAt?, ite_eq_left atInsertion] at moved
    obtain ⟨header, rewritten, rfl⟩ := Option.map_eq_some_iff.mp moved
    exact ⟨atInsertion.1, atInsertion.2, header, rewritten, rfl⟩
  · simp [moveAt?, atInsertion] at moved

theorem chooseCut_sound {operands : List (Point (SourceLabel carried result))}
    {uses : List (Use (SourceLabel carried result))}
    (selected : chooseCut? g operands uses = some cut) :
    cut ∈ candidateCuts (lower g) blocks ∧ Legal (lower g) operands uses cut := by
  let _ : DecidableEq (Target (SourceLabel carried result)) := sourceTargetDecEq carried result
  unfold chooseCut? at selected
  rw [Silmaril.SSA.SeaOfNodes.GCM.Corridor.chooseSynthesized?_eq] at selected
  obtain ⟨tree, _, ranked⟩ := Option.bind_eq_some_iff.mp selected
  exact LoopForest.choosePlacement_sound ranked

theorem pickAndMove?_placement (picked : pickAndMove? g index = some (cut, out)) :
    cut.block = headerId ∧ cut.cut + 1 = index ∧ afterRemoval index cut.cut = cut.cut ∧
    cut ∈ candidateCuts (lower g) blocks ∧
    ∃ (saved : Width) (binding : Binding Input (carried :: Input) saved carried result),
      findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨saved, binding⟩ ∧
      chooseCut? g binding.operands binding.uses = some cut ∧
      Legal (lower g) binding.operands binding.uses cut := by
  obtain ⟨⟨saved, binding, found, selected⟩, moved⟩ := pickAndEmit?_spec picked
  obtain ⟨atHeader, atInsertion, _⟩ := moved_spec moved
  have translates : afterRemoval index cut.cut = cut.cut := by
    unfold afterRemoval at atInsertion ⊢
    split at atInsertion <;> rename_i relation
    · omega
    · simp [relation]
  obtain ⟨candidate, legal⟩ := chooseCut_sound selected
  exact ⟨atHeader, translates ▸ atInsertion, translates, candidate, saved, binding, found, selected, legal⟩

theorem pickAndMove?_refuses (outside : ¬ (cut.block = headerId ∧
    afterRemoval index cut.cut + 1 = index))
    {saved : Width} {binding : Binding Input (carried :: Input) saved carried result}
    (found : findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨saved, binding⟩)
    (selected : chooseCut? g binding.operands binding.uses = some cut) :
    pickAndMove? g index = none := by
  simp [pickAndMove?, pickAndEmit?, found, selected, moveAt?, outside]

section HeaderReplacement

variable {cfg : Cfg TargetOp (SourceLabel carried result) Input [result]}
variable {header : Block TargetOp (SourceLabel carried result) (carried :: Input) [result]}
variable (agrees : ∀ env, header.eval evalOp (fun term vals => term.eval vals) env =
  (cfg.block .header).eval evalOp (fun term vals => term.eval vals) env)
include agrees

theorem withHeader_frames (input : Env Input) :
    (withHeader cfg header).entry = cfg.entry ∧
    ∀ frame : Frame (SourceLabel carried result),
      ((withHeader cfg header).block frame.label).eval evalOp (fun term env => term.eval env)
          (frame.args.append input) =
        (cfg.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) := by
  refine ⟨rfl, ?_⟩
  rintro ⟨label, args⟩
  cases label with
  | header => exact agrees (args.append input)
  | exit => rfl

theorem withHeader_run_eq (input : Env Input) (fuel : Nat) :
    (withHeader cfg header).run evalOp fuel input = cfg.run evalOp fuel input := by
  obtain ⟨entry, block⟩ := withHeader_frames agrees input
  have runs (fuel : Nat) (frame : Frame (SourceLabel carried result)) :
      (withHeader cfg header).runFrom evalOp fuel input frame = cfg.runFrom evalOp fuel input frame := by
    induction fuel generalizing frame with
    | zero => rfl
    | succ fuel ih =>
      simp only [Cfg.runFrom, Cfg.runBlock, block frame]
      cases (cfg.block frame.label).eval evalOp (fun term env => term.eval env)
          (frame.args.append input) with
      | inl next => exact ih next
      | inr _ => rfl
  cases fuel with
  | zero => rfl
  | succ fuel =>
    simp only [Cfg.run, Cfg.runBlock, entry]
    cases cfg.entry.eval evalOp (fun term env => term.eval env) input with
    | inl next => exact runs fuel next
    | inr _ => rfl

theorem withHeader_denotePart (input : Env Input) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (withHeader cfg header)).denotePart evalOp input =
      (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed cfg).denotePart evalOp input := by
  open Silmaril.MLIR.CF.SwitchAssert in
  apply Part.ext
  intro outcome
  simp only [Cfg.mem_denotePart_iff, Cfg.embed_run, withHeader_run_eq agrees]

end HeaderReplacement

theorem pickAndMove?_frames (picked : pickAndMove? g index = some (cut, out))
    (input : Env Input) :
    out.entry = (lower g).entry ∧
    ∀ frame : Frame (SourceLabel carried result),
      (out.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) =
        ((lower g).block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) := by
  obtain ⟨_, _, _, swapped, rfl⟩ := moved_spec (pickAndEmit?_spec picked).2
  exact withHeader_frames (swapAt?_eval swapped) input

theorem pickAndMove?_run_eq (picked : pickAndMove? g index = some (cut, out))
    (input : Env Input) (fuel : Nat) :
    out.run evalOp fuel input = (lower g).run evalOp fuel input := by
  obtain ⟨_, _, _, swapped, rfl⟩ := moved_spec (pickAndEmit?_spec picked).2
  exact withHeader_run_eq (swapAt?_eval swapped) input fuel

theorem pickAndMove?_budget (picked : pickAndMove? g index = some (cut, out))
    (input : Env Input) (budget : Nat) :
    out.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  (pickAndMove?_run_eq picked input _).trans (lower_run g input budget)

theorem pickAndMove?_denotePart (picked : pickAndMove? g index = some (cut, out))
    (input : Env Input) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed out).denotePart evalOp input =
      (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower g)).denotePart evalOp input := by
  obtain ⟨_, _, _, swapped, rfl⟩ := moved_spec (pickAndEmit?_spec picked).2
  exact withHeader_denotePart (swapAt?_eval swapped) input

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header
