module

public import Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LatePlacement.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.EarlyPlacement

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (OpSignature)
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.Dominance (checkClosed)
open Silmaril.SSA.SeaOfNodes.GCM.EarlyPlacement
open Silmaril.SSA.SeaOfNodes.GCM.LatePlacement (lateBound? lateBound?_spec legal_iff_lateBound)

variable {Op : OpSignature} {Label : List Width → Type} {Input Result : List Width}
variable {cfg : Cfg Op Label Input Result} {tree : DominatorTree cfg}
variable {operands : List (Point Label)} {early : BlockId Label}

private theorem valid_iff (complete : tree.Complete) (point : Point Label) :
    point.valid? tree = true ↔ point.Valid cfg := by
  simp only [Point.valid?, Bool.and_eq_true, decide_eq_true_eq, Point.Valid]
  exact and_congr_left fun _ => ⟨tree.reachable_sound, complete.reachable_complete⟩

private theorem entry_dominates (tree : DominatorTree cfg) {block : BlockId Label}
    (reachable : Reachable cfg block) :
    Dominates cfg none block :=
  tree.prefix_sound reachable (by simp [tree.entry_address])

theorem earlyBound?_spec (complete : tree.Complete)
    (found : earlyBound? tree operands = some early) :
    Reachable cfg early ∧ (∀ operand ∈ operands, operand.Valid cfg) ∧
      ∀ block, Reachable cfg block →
        (Dominates cfg early block ↔ ∀ operand ∈ operands, Dominates cfg operand.block block) := by
  cases choice : operands.maxOn? (fun operand => (tree.address operand.block).length) with
  | none =>
    have empty : operands = [] := by
      cases operands with
      | nil => rfl
      | cons => simp [List.maxOn?_cons_eq_some_maxOn] at choice
    have root : none = early := by simpa [earlyBound?, choice] using found
    subst early
    subst operands
    refine ⟨⟨[none], .entry⟩, by simp, fun block reachable => ?_⟩
    simp [entry_dominates tree reachable]
  | some deepest =>
    by_cases allValid : (operands.all fun operand => operand.valid? tree &&
        (tree.address operand.block).isPrefixOf (tree.address deepest.block)) = true
    · have selected : deepest.block = early := by
        simpa [earlyBound?, choice, allValid] using found
      subst early
      have member := List.maxOn?_mem choice
      have facts (operand) (present : operand ∈ operands) :
          operand.Valid cfg ∧ List.IsPrefix (tree.address operand.block)
            (tree.address deepest.block) := by
        have checked := List.all_eq_true.mp allValid operand present
        simp only [Bool.and_eq_true] at checked
        exact ⟨(valid_iff complete operand).mp checked.1, List.isPrefixOf_iff_prefix.mp checked.2⟩
      have reachable := (facts deepest member).1.1
      refine ⟨reachable, fun operand present => (facts operand present).1,
        fun block readReachable => ⟨?_, fun dom => dom deepest member⟩⟩
      intro dom operand present
      exact tree.prefix_sound readReachable
        ((facts operand present).2.trans (complete.prefix_complete readReachable dom))
    · simp [earlyBound?, choice, allValid] at found

theorem earlyBound?_isSome_iff (complete : tree.Complete) :
    (earlyBound? tree operands).isSome = true ↔
      (∀ operand ∈ operands, operand.Valid cfg) ∧
        ∃ block, Reachable cfg block ∧ ∀ operand ∈ operands, Dominates cfg operand.block block := by
  constructor
  · intro someBound
    obtain ⟨bound, found⟩ := Option.isSome_iff_exists.mp someBound
    obtain ⟨reachable, valid, exactBound⟩ := earlyBound?_spec complete found
    exact ⟨valid, bound, reachable, (exactBound bound reachable).mp
      (tree.prefix_sound reachable ⟨[], by simp⟩)⟩
  · rintro ⟨valid, block, reachable, dom⟩
    cases choice : operands.maxOn? (fun operand => (tree.address operand.block).length) with
    | none => simp [earlyBound?, choice]
    | some deepest =>
      have deepPrefix := complete.prefix_complete reachable (dom deepest (List.maxOn?_mem choice))
      have guard : (operands.all fun operand => operand.valid? tree &&
          (tree.address operand.block).isPrefixOf (tree.address deepest.block)) = true := by
        apply List.all_eq_true.mpr
        intro operand present
        have depth : (tree.address operand.block).length ≤ (tree.address deepest.block).length := by
          have maximum := List.le_apply_get_maxOn?_of_mem
            (f := fun operand => (tree.address operand.block).length) present
          simpa [choice] using maximum
        rw [Bool.and_eq_true]
        exact ⟨(valid_iff complete operand).mpr (valid operand present),
          List.isPrefixOf_iff_prefix.mpr (List.prefix_of_prefix_length_le
            (complete.prefix_complete reachable (dom operand present)) deepPrefix depth)⟩
      simp [earlyBound?, choice, guard]

variable [DecidableEq (Target Label)]
variable {blocks : List (Target Label)} {uses : List (Use Label)}
variable {late : BlockId Label} {candidate : Point Label}

theorem legal_iff_bounds (complete : tree.Complete) (closed : checkClosed cfg blocks = true)
    (earlyFound : earlyBound? tree operands = some early)
    (lateFound : lateBound? tree blocks uses = some late) :
    Legal cfg operands uses candidate ↔
      candidate.Valid cfg ∧ Dominates cfg early candidate.block ∧
      Dominates cfg candidate.block late ∧
      (∀ operand ∈ operands, operand.block = candidate.block → operand.cut ≤ candidate.cut) ∧
      ∀ use ∈ uses, ∀ read, use.point? cfg = some read →
        candidate.block = read.block → candidate.cut ≤ read.cut := by
  rw [legal_iff_lateBound complete closed lateFound operands candidate]
  obtain ⟨_, operandValid, earlyExact⟩ := earlyBound?_spec complete earlyFound
  constructor
  · rintro ⟨valid, available, beforeLate, readOrder⟩
    refine ⟨valid, (earlyExact candidate.block valid.1).mpr (fun operand member =>
      (available operand member).2.dominates), beforeLate, ?_, readOrder⟩
    exact fun operand member => (available operand member).2.local_order
  · rintro ⟨valid, afterEarly, beforeLate, operandOrder, readOrder⟩
    have dominated := (earlyExact candidate.block valid.1).mp afterEarly
    exact ⟨valid, fun operand member =>
      ⟨operandValid operand member, dominated operand member, operandOrder operand member⟩,
      beforeLate, readOrder⟩

theorem early_dominates_late_of_legal (complete : tree.Complete)
    (closed : checkClosed cfg blocks = true)
    (earlyFound : earlyBound? tree operands = some early)
    (lateFound : lateBound? tree blocks uses = some late)
    (legal : Legal cfg operands uses candidate) : Dominates cfg early late := by
  have ⟨valid, afterEarly, beforeLate, _⟩ :=
    (legal_iff_bounds complete closed earlyFound lateFound).mp legal
  have reachable := (lateBound?_spec complete closed lateFound).1
  exact tree.prefix_sound reachable ((complete.prefix_complete valid.1 afterEarly).trans
    (complete.prefix_complete reachable beforeLate))

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.EarlyPlacement
