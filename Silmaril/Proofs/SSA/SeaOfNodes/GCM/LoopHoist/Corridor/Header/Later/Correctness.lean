module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Thms
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Cfg Frame)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor (sourceTargetDecEq)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header
  (afterRemoval swapAt? withHeader swapAt?_eval withHeader_frames withHeader_run_eq withHeader_denotePart)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier (Operation operations swapAt?_order)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later
open Loop.MLIR.CF (Program TargetOp evalOp lower model lower_run)

variable {Input Γ : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {index : Nat} {cut : Point (SourceLabel carried result)}
variable {cfg out : Cfg TargetOp (SourceLabel carried result) Input [result]}
variable {before after : Block TargetOp (SourceLabel carried result) Γ [result]}

theorem moveLater?_order {extraSteps : Nat}
    (moved : moveLater? index extraSteps before = some after) :
    ∃ (prefixOps crossed : List Operation) (chosen : Operation) (suffixOps : List Operation),
      prefixOps.length = index ∧ crossed.length = extraSteps + 1 ∧
      operations before = prefixOps ++ (chosen :: (crossed ++ suffixOps)) ∧
      operations after = prefixOps ++ crossed ++ (chosen :: suffixOps) := by
  induction extraSteps generalizing index before with
  | zero =>
    obtain ⟨prefixOps, chosen, neighbor, suffixOps, length, beforeOrder, afterOrder⟩ :=
      swapAt?_order moved
    exact ⟨prefixOps, [neighbor], chosen, suffixOps, length, rfl, beforeOrder,
      by simpa only [List.append_assoc, List.singleton_append] using afterOrder⟩
  | succ extraSteps ih =>
    obtain ⟨middle, swapped, remaining⟩ := Option.bind_eq_some_iff.mp moved
    obtain ⟨prefixOps, firstChosen, neighbor, firstSuffix, shortLength, original, intermediate⟩ :=
      swapAt?_order swapped
    obtain ⟨longPrefix, crossed, chosen, suffixOps, longLength, crossedLength, rest, final⟩ :=
      ih remaining
    have middleOrder : (prefixOps ++ [neighbor]) ++ (firstChosen :: firstSuffix) =
        longPrefix ++ (chosen :: (crossed ++ suffixOps)) := by
      simpa only [List.append_assoc, List.singleton_append] using intermediate.symm.trans rest
    obtain ⟨samePrefix, sameTail⟩ := List.append_inj middleOrder (by simp [shortLength, longLength])
    obtain ⟨sameChosen, sameSuffix⟩ := List.cons.inj sameTail
    refine ⟨prefixOps, neighbor :: crossed, chosen, suffixOps, shortLength,
      by simp [crossedLength], ?_, ?_⟩
    · simpa only [sameChosen, sameSuffix, List.cons_append] using original
    · simpa only [← samePrefix, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using final

theorem moveLater?_eval {extraSteps : Nat} (moved : moveLater? index extraSteps before = some after)
    (env : Env Γ) : after.eval evalOp (fun term vals => term.eval vals) env =
      before.eval evalOp (fun term vals => term.eval vals) env := by
  induction extraSteps generalizing index before with
  | zero => exact swapAt?_eval moved env
  | succ _ ih =>
    obtain ⟨_, swapped, remaining⟩ := Option.bind_eq_some_iff.mp moved
    exact (ih remaining).trans (swapAt?_eval swapped env)

private theorem emitted_spec (moved : moveCfgAt? cfg index cut = some out) :
    checkCfgDestination cfg index cut = true ∧
    ∃ header, moveLater? index (afterRemoval index cut.cut - index - 1)
        (cfg.block .header) = some header ∧
      out = withHeader cfg header := by
  cases checked : checkCfgDestination cfg index cut with
  | false => simp [moveCfgAt?, checked] at moved
  | true =>
    simp only [moveCfgAt?, checked, ite_true] at moved
    obtain ⟨header, emitted, rfl⟩ := Option.map_eq_some_iff.mp moved
    exact ⟨rfl, header, emitted, rfl⟩

theorem checkBindingCut_sound (checked : checkBindingCut cfg index cut = true) :
    ∃ (saved : Width) (binding : Binding Input (carried :: Input) saved carried result),
      findBinding index 0 headerOrigins (cfg.block .header) = some ⟨saved, binding⟩ ∧
      Legal cfg binding.operands binding.uses cut := by
  let _ : DecidableEq (Target (SourceLabel carried result)) := sourceTargetDecEq carried result
  unfold checkBindingCut at checked
  obtain ⟨⟨saved, binding⟩, found, accepted⟩ := (Option.any_eq_true _ _).mp checked
  exact ⟨saved, binding, found, (Dominance.Placement.checkCut_iff.mp accepted).2⟩

theorem moveCfgAt?_checked (moved : moveCfgAt? cfg index cut = some out) :
    checkBindingCut cfg index cut = true :=
  (Bool.and_eq_true_iff.mp (emitted_spec moved).1).2

theorem moveCfgAt?_header (moved : moveCfgAt? cfg index cut = some out) :
    ∃ header, out = withHeader cfg header ∧
      ∀ env, header.eval evalOp (fun term vals => term.eval vals) env =
        (cfg.block .header).eval evalOp (fun term vals => term.eval vals) env := by
  obtain ⟨_, header, emitted, eq⟩ := emitted_spec moved
  exact ⟨header, eq, moveLater?_eval emitted⟩

theorem checkDestination_sound (checked : checkDestination g index cut = true) :
    cut.block = headerId ∧ index + 1 < cut.cut ∧ afterRemoval index cut.cut = cut.cut - 1 ∧
    ∃ (saved : Width) (binding : Binding Input (carried :: Input) saved carried result),
      findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨saved, binding⟩ ∧
      Legal (lower g) binding.operands binding.uses cut := by
  let _ : DecidableEq (Target (SourceLabel carried result)) := sourceTargetDecEq carried result
  unfold checkDestination checkCfgDestination at checked
  obtain ⟨supported, checkedSites⟩ := Bool.and_eq_true_iff.mp checked
  obtain ⟨atHeader, later⟩ := of_decide_eq_true supported
  have beforeCut : index < cut.cut := later.trans_le (Nat.sub_le _ _)
  have translation : afterRemoval index cut.cut = cut.cut - 1 := by simp [afterRemoval, beforeCut]
  rw [translation] at later
  exact ⟨atHeader, by omega, translation, checkBindingCut_sound checkedSites⟩

theorem moveAt?_placement (moved : moveAt? g index cut = some out) :
    cut.block = headerId ∧ index + 1 < cut.cut ∧ afterRemoval index cut.cut = cut.cut - 1 ∧
    ∃ (saved : Width) (binding : Binding Input (carried :: Input) saved carried result),
      findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨saved, binding⟩ ∧
      Legal (lower g) binding.operands binding.uses cut :=
  checkDestination_sound (emitted_spec moved).1

theorem moveAt?_refuses_lateUse {saved : Width}
    {binding : Binding Input (carried :: Input) saved carried result}
    (found : findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨saved, binding⟩)
    {use : Use (SourceLabel carried result)} {read : Point (SourceLabel carried result)}
    (member : use ∈ binding.uses) (resolved : use.point? (lower g) = some read)
    (sameBlock : cut.block = read.block) (passed : read.cut < cut.cut) :
    moveAt? g index cut = none := by
  let _ : DecidableEq (Target (SourceLabel carried result)) := sourceTargetDecEq carried result
  have refused : Dominance.Placement.checkCut (lower g) blocks binding.operands binding.uses cut = false := by
    cases checked : Dominance.Placement.checkCut (lower g) blocks binding.operands binding.uses cut with
    | false => rfl
    | true =>
      have legal := (Dominance.Placement.checkCut_iff.mp checked).2
      obtain ⟨point, pointFound, _, available⟩ := legal.uses_available use member
      have samePoint := Option.some.inj (pointFound.symm.trans resolved)
      subst point
      exact (Nat.not_le_of_gt passed (available.local_order sameBlock)).elim
  simp [moveAt?, moveCfgAt?, checkCfgDestination, checkBindingCut, found, refused]

theorem moveCfgAt?_order (moved : moveCfgAt? cfg index cut = some out) :
    ∃ (prefixOps crossed : List Operation) (chosen : Operation) (suffixOps : List Operation),
      prefixOps.length = index ∧ prefixOps.length + crossed.length = afterRemoval index cut.cut ∧
      operations (cfg.block .header) = prefixOps ++ (chosen :: (crossed ++ suffixOps)) ∧
      operations (out.block .header) = prefixOps ++ crossed ++ (chosen :: suffixOps) := by
  obtain ⟨checked, _, emitted, rfl⟩ := emitted_spec moved
  let _ : DecidableEq (Target (SourceLabel carried result)) := sourceTargetDecEq carried result
  unfold checkCfgDestination at checked
  have later := (of_decide_eq_true (Bool.and_eq_true_iff.mp checked).1).2
  obtain ⟨prefixOps, crossed, chosen, suffixOps, prefixLength, count, beforeOrder, afterOrder⟩ :=
    moveLater?_order emitted
  exact ⟨prefixOps, crossed, chosen, suffixOps, prefixLength, by omega, beforeOrder, afterOrder⟩

theorem moveAt?_order (moved : moveAt? g index cut = some out) :
    ∃ (prefixOps crossed : List Operation) (chosen : Operation) (suffixOps : List Operation),
      prefixOps.length = index ∧ prefixOps.length + crossed.length = cut.cut - 1 ∧
      operations ((lower g).block .header) = prefixOps ++ (chosen :: (crossed ++ suffixOps)) ∧
      operations (out.block .header) = prefixOps ++ crossed ++ (chosen :: suffixOps) := by
  obtain ⟨_, _, translation, _⟩ := moveAt?_placement moved
  obtain ⟨pre, crossed, chosen, suf, len, dest, beforeOrder, afterOrder⟩ := moveCfgAt?_order moved
  exact ⟨pre, crossed, chosen, suf, len, translation ▸ dest, beforeOrder, afterOrder⟩

theorem moveAt?_frames (moved : moveAt? g index cut = some out) (input : Env Input) :
    out.entry = (lower g).entry ∧
    ∀ frame : Frame (SourceLabel carried result),
      (out.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) =
        ((lower g).block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) := by
  obtain ⟨_, rfl, agrees⟩ := moveCfgAt?_header moved
  exact withHeader_frames agrees input

theorem moveAt?_run_eq (moved : moveAt? g index cut = some out) (input : Env Input)
    (fuel : Nat) : out.run evalOp fuel input = (lower g).run evalOp fuel input := by
  obtain ⟨_, rfl, agrees⟩ := moveCfgAt?_header moved
  exact withHeader_run_eq agrees input fuel

theorem moveAt?_budget (moved : moveAt? g index cut = some out) (input : Env Input) (budget : Nat) :
    out.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  (moveAt?_run_eq moved input _).trans (lower_run g input budget)

theorem moveAt?_denotePart (moved : moveAt? g index cut = some out) (input : Env Input) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed out).denotePart evalOp input =
      (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower g)).denotePart evalOp input := by
  obtain ⟨_, rfl, agrees⟩ := moveCfgAt?_header moved
  exact withHeader_denotePart agrees input

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later
