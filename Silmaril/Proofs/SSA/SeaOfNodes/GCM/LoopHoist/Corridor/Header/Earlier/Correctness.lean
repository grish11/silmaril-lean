module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Thms
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Cfg Frame)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header
  (afterRemoval swapAt? withHeader pickAndEmit?_spec chooseCut_sound swapAt?_eval
    withHeader_frames withHeader_run_eq withHeader_denotePart)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier
open Loop.MLIR.CF (Program TargetOp evalOp lower model lower_run)

variable {Input Γ Δ : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {index : Nat} {cut : Point (SourceLabel carried result)}
variable {cfg out : Cfg TargetOp (SourceLabel carried result) Input [result]}
variable {before after : Block TargetOp (SourceLabel carried result) Γ [result]}

variable {Labels : List Width → Type} {Result : List Width}

private theorem renameSuffix_operations (rename : Rename Γ Δ)
    (code : Block TargetOp Labels Γ Result) :
    operations (Header.Typed.renameSuffix rename code) = operations code := by
  induction code generalizing Δ with
  | terminator => rfl
  | letOp _ _ _ ih => simp only [Header.Typed.renameSuffix, operations, ih]

theorem swapAt_typed_order {target : Nat} {before after : Block TargetOp Labels Γ Result}
    (swapped : Header.Typed.swapAt? target before = some after) :
    ∃ (prefixOps : List Operation) (left right : Operation) (suffixOps : List Operation),
      prefixOps.length = target ∧
      operations before = prefixOps ++ (left :: right :: suffixOps) ∧
      operations after = prefixOps ++ (right :: left :: suffixOps) := by
  induction target generalizing Γ with
  | zero =>
    cases before with
    | terminator => cases swapped
    | letOp left leftArgs rest =>
      cases rest with
      | terminator => cases swapped
      | letOp right rightArgs suffix =>
        cases caught : capture? rightArgs with
        | none => simp [Header.Typed.swapAt?, caught] at swapped
        | some earlierArgs =>
          simp [Header.Typed.swapAt?, caught] at swapped
          subst after
          exact ⟨[], ⟨_, _, left⟩, ⟨_, _, right⟩, operations suffix, rfl, rfl,
            by simp only [operations, List.nil_append, renameSuffix_operations]⟩
  | succ target ih =>
    cases before with
    | terminator => cases swapped
    | letOp op operands rest =>
      obtain ⟨body, swappedRest, rfl⟩ := Option.map_eq_some_iff.mp swapped
      obtain ⟨prefixOps, left, right, suffixOps, length, kept, moved⟩ := ih swappedRest
      exact ⟨⟨_, _, op⟩ :: prefixOps, left, right, suffixOps,
        by simp [length], by simp only [operations, kept, List.cons_append],
        by simp only [operations, moved, List.cons_append]⟩

theorem swapAt?_order {target : Nat} (swapped : swapAt? target before = some after) :
    ∃ (prefixOps : List Operation) (left right : Operation) (suffixOps : List Operation),
      prefixOps.length = target ∧
      operations before = prefixOps ++ (left :: right :: suffixOps) ∧
      operations after = prefixOps ++ (right :: left :: suffixOps) :=
  swapAt_typed_order ((Header.Typed.swapAt?_source target before).trans swapped)

theorem moveEarlier?_order {target extraSteps : Nat}
    (moved : moveEarlier? target extraSteps before = some after) :
    ∃ (prefixOps crossed : List Operation) (chosen : Operation) (suffixOps : List Operation),
      prefixOps.length = target ∧ crossed.length = extraSteps + 1 ∧
      operations before = prefixOps ++ crossed ++ (chosen :: suffixOps) ∧
      operations after = prefixOps ++ (chosen :: (crossed ++ suffixOps)) := by
  induction extraSteps generalizing before with
  | zero =>
    obtain ⟨prefixOps, left, right, suffixOps, length, kept, moved⟩ := swapAt?_order moved
    exact ⟨prefixOps, [left], right, suffixOps, length, rfl,
      by simpa only [List.append_assoc, List.singleton_append] using kept, moved⟩
  | succ extraSteps ih =>
    obtain ⟨middle, swapped, slid⟩ := Option.bind_eq_some_iff.mp moved
    obtain ⟨longPrefix, neighbor, firstChosen, firstSuffix, longLength, original, intermediate⟩ :=
      swapAt?_order swapped
    obtain ⟨prefixOps, crossed, chosen, suffixOps, shortLength, crossedLength, remaining, final⟩ :=
      ih slid
    obtain ⟨samePrefix, sameTail⟩ := List.append_inj (intermediate.symm.trans remaining)
      (by simp [longLength, shortLength, crossedLength, Nat.add_assoc])
    obtain ⟨sameChosen, sameSuffix⟩ := List.cons.inj sameTail
    refine ⟨prefixOps, crossed ++ [neighbor], firstChosen, firstSuffix, shortLength,
      by simp [crossedLength], ?_, ?_⟩
    · simpa only [samePrefix, List.append_assoc, List.singleton_append] using original
    · simpa only [← sameChosen, ← sameSuffix, List.append_assoc, List.singleton_append] using final

theorem moveEarlier?_eval {target extraSteps : Nat}
    (moved : moveEarlier? target extraSteps before = some after) (env : Env Γ) :
    after.eval evalOp (fun term vals => term.eval vals) env =
      before.eval evalOp (fun term vals => term.eval vals) env := by
  induction extraSteps generalizing before with
  | zero => exact swapAt?_eval moved env
  | succ _ ih =>
    obtain ⟨_, swapped, slid⟩ := Option.bind_eq_some_iff.mp moved
    exact (ih slid).trans (swapAt?_eval swapped env)

private theorem moved_spec (moved : moveAt? cfg index cut = some out) :
    cut.block = headerId ∧ cut.cut < index ∧ afterRemoval index cut.cut = cut.cut ∧
    ∃ header, moveEarlier? cut.cut (index - cut.cut - 1) (cfg.block .header) = some header ∧
      out = withHeader cfg header := by
  by_cases supported : cut.block = headerId ∧ afterRemoval index cut.cut < index
  · have earlier : cut.cut < index := by
      have small := supported.2
      unfold afterRemoval at small
      split at small <;> omega
    have translates : afterRemoval index cut.cut = cut.cut :=
      by simp [afterRemoval, Nat.not_lt.mpr (Nat.le_of_lt earlier)]
    simp only [moveAt?, ite_eq_left supported, translates] at moved
    obtain ⟨header, emitted, rfl⟩ := Option.map_eq_some_iff.mp moved
    exact ⟨supported.1, earlier, translates, header, emitted, rfl⟩
  · simp [moveAt?, supported] at moved

theorem moveAt?_header (moved : moveAt? cfg index cut = some out) :
    ∃ header, out = withHeader cfg header ∧
      ∀ env, header.eval evalOp (fun term vals => term.eval vals) env =
        (cfg.block .header).eval evalOp (fun term vals => term.eval vals) env := by
  obtain ⟨_, _, _, header, emitted, eq⟩ := moved_spec moved
  exact ⟨header, eq, moveEarlier?_eval emitted⟩

theorem moveAt?_adjacent (adjacent : afterRemoval index cut.cut + 1 = index) :
    moveAt? cfg index cut = Header.moveAt? cfg index cut := by
  have earlier : afterRemoval index cut.cut < index := by omega
  have noExtra : index - afterRemoval index cut.cut - 1 = 0 := by omega
  by_cases atHeader : cut.block = headerId
  · simp only [moveAt?, Header.moveAt?, ite_eq_left (And.intro atHeader earlier),
      ite_eq_left (And.intro atHeader adjacent), noExtra, moveEarlier?]
  · have left : ¬ (cut.block = headerId ∧ afterRemoval index cut.cut < index) :=
      fun supported => atHeader supported.1
    have right : ¬ (cut.block = headerId ∧ afterRemoval index cut.cut + 1 = index) :=
      fun supported => atHeader supported.1
    simp only [moveAt?, Header.moveAt?, ite_eq_right left, ite_eq_right right]

theorem pickAndMove?_placement (picked : pickAndMove? g index = some (cut, out)) :
    cut.block = headerId ∧ cut.cut < index ∧ afterRemoval index cut.cut = cut.cut ∧
    cut ∈ candidateCuts (lower g) blocks ∧
    ∃ (saved : Width) (binding : Binding Input (carried :: Input) saved carried result),
      findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨saved, binding⟩ ∧
      chooseCut? g binding.operands binding.uses = some cut ∧
      Legal (lower g) binding.operands binding.uses cut := by
  obtain ⟨⟨saved, binding, found, selected⟩, moved⟩ := pickAndEmit?_spec picked
  obtain ⟨atHeader, earlier, translates, _⟩ := moved_spec moved
  obtain ⟨candidate, legal⟩ := chooseCut_sound selected
  exact ⟨atHeader, earlier, translates, candidate, saved, binding, found, selected, legal⟩

theorem moveAt?_order (moved : moveAt? cfg index cut = some out) :
    ∃ (prefixOps crossed : List Operation) (chosen : Operation) (suffixOps : List Operation),
      prefixOps.length = afterRemoval index cut.cut ∧ prefixOps.length + crossed.length = index ∧
      operations (cfg.block .header) = prefixOps ++ crossed ++ (chosen :: suffixOps) ∧
      operations (out.block .header) = prefixOps ++ (chosen :: (crossed ++ suffixOps)) := by
  obtain ⟨_, earlier, translated, _, emitted, rfl⟩ := moved_spec moved
  obtain ⟨pre, crossed, chosen, suffix, length, distance, beforeOrder, afterOrder⟩ := moveEarlier?_order emitted
  exact ⟨pre, crossed, chosen, suffix, translated.symm ▸ length, by omega, beforeOrder, afterOrder⟩

theorem pickAndMove?_order (picked : pickAndMove? g index = some (cut, out)) :
    ∃ (prefixOps crossed : List Operation) (chosen : Operation) (suffixOps : List Operation),
      prefixOps.length = cut.cut ∧ crossed.length = index - cut.cut ∧
      operations ((lower g).block .header) = prefixOps ++ crossed ++ (chosen :: suffixOps) ∧
      operations (out.block .header) = prefixOps ++ (chosen :: (crossed ++ suffixOps)) := by
  have moved := (pickAndEmit?_spec picked).2
  obtain ⟨_, _, translated, _⟩ := moved_spec moved
  obtain ⟨pre, crossed, chosen, suffix, length, distance, beforeOrder, afterOrder⟩ := moveAt?_order moved
  exact ⟨pre, crossed, chosen, suffix, translated ▸ length, by omega, beforeOrder, afterOrder⟩

theorem pickAndMove?_frames (picked : pickAndMove? g index = some (cut, out)) (input : Env Input) :
    out.entry = (lower g).entry ∧
    ∀ frame : Frame (SourceLabel carried result),
      (out.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) =
        ((lower g).block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) := by
  obtain ⟨_, _, _, _, moved, rfl⟩ := moved_spec (pickAndEmit?_spec picked).2
  exact withHeader_frames (moveEarlier?_eval moved) input

theorem pickAndMove?_run_eq (picked : pickAndMove? g index = some (cut, out)) (input : Env Input)
    (fuel : Nat) : out.run evalOp fuel input = (lower g).run evalOp fuel input := by
  obtain ⟨_, _, _, _, moved, rfl⟩ := moved_spec (pickAndEmit?_spec picked).2
  exact withHeader_run_eq (moveEarlier?_eval moved) input fuel

theorem pickAndMove?_budget (picked : pickAndMove? g index = some (cut, out)) (input : Env Input)
    (budget : Nat) :
    out.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  (pickAndMove?_run_eq picked input _).trans (lower_run g input budget)

theorem pickAndMove?_denotePart (picked : pickAndMove? g index = some (cut, out)) (input : Env Input) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed out).denotePart evalOp input =
      (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower g)).denotePart evalOp input := by
  obtain ⟨_, _, _, _, moved, rfl⟩ := moved_spec (pickAndEmit?_spec picked).2
  exact withHeader_denotePart (moveEarlier?_eval moved) input

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier
