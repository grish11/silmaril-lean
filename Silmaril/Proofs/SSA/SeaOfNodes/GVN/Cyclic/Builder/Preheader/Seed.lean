module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Defs
import Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Intern.Thms
import Silmaril.SSA.SeaOfNodes.GVN.WordNumber.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader

open Silmaril.SSA.SeaOfNodes
open Diamond (Ty ValueSort dataPorts)
open GVN.Cyclic.Activation (Inputs inputSlot)
open GVN.Cyclic.Builder (argumentPorts)
open GVN.Cyclic.Builder.Preheader
open GVN.WordNumber (Key entryKeys numbering)
open GVN.WordNumber.Intern (Agrees entryIds)
open Pure.SubZero (model word)
open Silmaril.SSA.RVSDG (Port)
open scoped Pure.WordNormalize

variable {inputs carried : List (ValueSort Unit)} {entrySigs headerSigs : List (List (Ty Unit))}
variable {out : ValueSort Unit} {loop : Native inputs carried entrySigs headerSigs out}

theorem number_agrees (loop : Native inputs carried entrySigs headerSigs out) :
    let bank := number loop
    bank.table.Nodup ∧ Agrees bank.table bank.entry bank.locals (entryKeys inputs)
      (loop.preheader.eval (numbering (dataPorts inputs)) (entryKeys inputs) PUnit.unit) :=
  let ⟨unique, agrees⟩ := GVN.WordNumber.Intern.entry_spec inputs
  let ⟨_, uniqueAfter, final⟩ := GVN.WordNumber.Intern.eval_spec loop.preheader agrees
  ⟨uniqueAfter unique, final⟩

theorem equal_lane_ids (lhs rhs : Port carried word) (same : laneId loop (number loop) lhs = laneId loop (number loop) rhs)
    (input : Inputs model inputs) :
    (loop.initial model input).get (inputSlot lhs) = (loop.initial model input).get (inputSlot rhs) := by
  obtain ⟨unique, agrees⟩ := number_agrees loop
  let leftWire := (loop.phiInputs .entry).get (inputSlot lhs)
  let rightWire := (loop.phiInputs .entry).get (inputSlot rhs)
  have sameKey := (GVN.WordNumber.Intern.Decodes.id_eq_iff unique (agrees leftWire) (agrees rightWire)).mp same
  have read_eq := congrArg (Key.eval input) sameKey
  have reads := GVN.WordNumber.eval_agrees loop.preheader (GVN.WordNumber.entry_read_agrees input)
  let locals := loop.preheader.eval model input PUnit.unit
  have left := loop.latch_get model .entry input locals (inputSlot lhs)
  have right := loop.latch_get model .entry input locals (inputSlot rhs)
  exact left.trans ((reads leftWire).symm.trans (read_eq.trans ((reads rightWire).trans right.symm)))

private theorem mem_argumentPorts {sort : ValueSort Unit} (lane : Port carried sort) :
    lane ∈ argumentPorts sort carried := by
  induction lane with
  | head => simp [argumentPorts]
  | @tail resultSort head rest inner ih =>
    have member := List.mem_map_of_mem (f := fun p => Port.tail (s := head) p) ih
    by_cases same : head = resultSort
    · rw [argumentPorts, dite_eq_left same]
      exact List.mem_cons_of_mem _ member
    · simpa only [argumentPorts, dite_eq_right same] using member

private theorem canonical_id (loop : Native inputs carried entrySigs headerSigs out) (bank : Bank inputs entrySigs)
    (lane : Port carried word) :
    laneId loop bank (canonicalLane loop bank lane) = laneId loop bank lane := by
  simp only [canonicalLane]
  cases found : (argumentPorts word carried).find? (fun other => decide (laneId loop bank other = laneId loop bank lane)) with
  | none => rfl
  | some chosen =>
    exact of_decide_eq_true (List.find?_some
      (p := fun other => decide (laneId loop bank other = laneId loop bank lane)) found)

theorem canonical_word_iff (bank : Bank inputs entrySigs) (lhs rhs : Port carried word) :
    canonicalLane loop bank lhs = canonicalLane loop bank rhs ↔ laneId loop bank lhs = laneId loop bank rhs := by
  constructor
  · intro same
    exact (canonical_id loop bank lhs).symm.trans ((congrArg (laneId loop bank) same).trans (canonical_id loop bank rhs))
  · intro same
    simp only [canonicalLane, same]
    cases found : (argumentPorts word carried).find? (fun other => decide (laneId loop bank other = laneId loop bank rhs)) with
    | some _ => rfl
    | none => exact False.elim ((List.find?_eq_none.mp found rhs (mem_argumentPorts rhs)) (by simp))

theorem canonical_value (input : Inputs model inputs) {sort : ValueSort Unit} (lane : Port carried sort) :
    (loop.initial model input).get (inputSlot (canonicalLane loop (number loop) lane)) =
      (loop.initial model input).get (inputSlot lane) := by
  cases sort with
  | predicate => rfl
  | data singleton =>
    cases singleton
    exact equal_lane_ids _ _ (canonical_id loop (number loop) lane) input

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader
