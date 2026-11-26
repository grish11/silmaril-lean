module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Defs
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Correctness
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Execution
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.WellFormed

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Proofs

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.SSA.SeaOfNodes.Diamond (read)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)

variable {captures bank old new : Nat} {entrySigs sigs : List (List PortTy)}

theorem feedback_args (p : Source captures bank entrySigs sigs) (side : Bool) :
    ((dispatch p).term.args)[(feedbackSlot side).val]? = some (1, emitColumn (p.column side)) := by
  cases side <;> rfl

private theorem map_row (mapping : InputMap old new) (p : Source old bank entrySigs sigs) (side : Bool) :
    (mapCaptures mapping p).row side = Width.mapCaptures mapping (p.row side) := by
  cases side <;> rfl

theorem step_mapCaptures (mapping : InputMap old new) (p : Source old bank entrySigs sigs)
    (input : WordTuple new) (carried : WordTuple bank) :
    (mapCaptures mapping p).step input carried = p.step (mapping.pull input) carried := by
  have selector := Width.Proofs.header_read_mapCaptures mapping p.primary model input carried p.selector
  have side : (mapCaptures mapping p).side input carried = p.side (mapping.pull input) carried :=
    congrArg (fun (value : Word) => decide (value ≠ 0)) selector
  let selected := p.side (mapping.pull input) carried
  have same := (congrArg (fun g : Width.Source new bank entrySigs sigs => g.step model input carried)
    (map_row mapping p selected)).trans
      (Width.Proofs.step_mapCaptures mapping (p.row selected) model input carried)
  rw [Source.step, Source.step, side]
  let tag : Word ⊕ WordTuple bank → Word ⊕ (Bool × WordTuple bank)
    | .inl value => .inl value
    | .inr next => .inr (selected, next)
  exact congrArg tag same

theorem lowerChecked_sound (mapping : InputMap old new) (p : Source old old entrySigs sigs)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog) :
    (∀ side, ∃ before, Table.lowerChecked (p.row side) = some before) ∧
    prog = lowerRTL (mapCaptures mapping p) ∧ prog.WellFormed ∧
    (prog.func? 0).map (·.sig.params) = some new := by
  obtain ⟨left, leftOk, afterLeft⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨right, rightOk, afterRight⟩ := Option.bind_eq_some_iff.mp afterLeft
  dsimp only at afterRight
  split at afterRight
  · rename_i wf
    cases Option.some.inj afterRight
    refine ⟨fun side => ?_, rfl, ?_, rfl⟩
    · cases side
      · exact ⟨right, rightOk⟩
      · exact ⟨left, leftOk⟩
    · intro fn member
      have eq : fn = lowerFunc (mapCaptures mapping p) := List.mem_singleton.mp member
      exact eq.symm ▸ wf
  · cases afterRight

/-- The checked entry uses the new capture count and latches the common entry column. -/
theorem entry_packet (mapping : InputMap old new) (p : Source old old entrySigs sigs)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (mem : Memory) :
    let start : State Reg := ⟨⟨0, 0, 0⟩, bindWords 0 Frame.empty input, [], mem⟩
    prog.start 0 (words input) mem = some start ∧
      ∃ latched, StepsNWithin prog [] (entrySigs.length + 1) start
        ⟨⟨0, 1, 0⟩, latched, [], mem⟩ ∧
        ArgsMatch latched (appendTuple (p.primary.initial model (mapping.pull input)) input) := by
  obtain ⟨rows, rfl, _, _⟩ := lowerChecked_sound mapping p accepted
  obtain ⟨before, beforeOk⟩ := rows true
  have primaryOk : Table.lowerChecked p.primary = some before := beforeOk
  obtain ⟨plan, found, _, _⟩ := Table.lowerChecked_sound primaryOk
  have arithmetic : Table.supported p.primary.preheader = true := by
    obtain ⟨rfl, graphEq⟩ := Table.recognize_sound found
    exact graphEq ▸ plan.arithmetic
  dsimp only
  constructor
  · change ((Frame.empty.writeAll (paramRegs 0 new) (words input)).map
      (fun regs => (⟨⟨0, 0, 0⟩, regs⟩ : Point × Frame Reg))).map
      (fun entered => (⟨entered.1, entered.2, [], mem⟩ : State Reg)) = _
    rw [bindWords_write]
    rfl
  · rw [← Width.Proofs.initial_mapCaptures mapping p.primary model input]
    exact Width.Proofs.entry_packet_at (Width.mapCaptures mapping p.primary)
      (lowerRTL (mapCaptures mapping p)) (block := header (mapCaptures mapping p)) rfl rfl rfl input _ mem
      ((Width.Proofs.supported_mapFlow mapping p.primary.preheader).trans arithmetic) (bindWords_args input)

private theorem row_step (p : Source captures bank entrySigs sigs) (side : Bool)
    (input : WordTuple captures) (carried : WordTuple bank) :
    (p.row side).step model input carried =
      let args := appendTuple carried input
      let locals := p.primary.header.eval model args PUnit.unit
      if (read model p.primary.predicate args locals).down then .inr ((p.column side).read args locals)
      else .inl (read model p.primary.result args locals) := by
  cases side <;> rfl

/-- Run the shared header and the selected occurrence of the actual RTL
dispatcher. The selected values are read as a packet before any bank write. -/
theorem activation (p : Source captures bank entrySigs sigs) (input : WordTuple captures)
    (carried : WordTuple bank) (fr : Frame Reg) (mem : Memory)
    (agree : ArgsMatch fr (appendTuple carried input)) :
    Activation p (lowerRTL p) input fr mem (p.step input carried) := by
  unfold Activation
  have found : (lowerRTL p).block? 0 1 = some (header p) := rfl
  obtain ⟨ready, path, reads⟩ :=
    Width.Proofs.header_producers_at p.primary (lowerRTL p) found rfl input carried fr mem agree
  have headerLen : (header p).ops.length = sigs.length := Width.Proofs.header_ops_length p.primary
  have fetched : (lowerRTL p).fetch ⟨0, 1, sigs.length⟩ = some (.term (header p).term) :=
    headerLen ▸ Prog.fetch_term found
  let args := appendTuple carried input
  let locals := p.primary.header.eval model args PUnit.unit
  let side := p.side input carried
  have guard : ready.get (register p.primary.predicate.address) =
      some (if (read model p.primary.predicate args locals).down then 1 else 0) := reads p.primary.predicate
  have selectedStep := row_step p side input carried
  rw [Source.step]
  dsimp only
  rw [selectedStep]
  dsimp only
  cases taken : (read model p.primary.predicate args locals).down with
  | false =>
    let value : Word := read model p.primary.result args locals
    have resultRead : ready.get (register p.primary.result.address) = some value := reads p.primary.result
    have exit : (lowerRTL p).block? 0 2 = some exitBlock := rfl
    have leave : step (lowerRTL p) ⟨⟨0, 1, sigs.length⟩, ready, [], mem⟩ =
        .running ⟨⟨0, 2, 0⟩, ready.set .phi value, [], mem⟩ := by
      simp [step, fetched, header, guard, taken, transfer, Frame.readAll, resultRead, exit, exitBlock]
      rfl
    have ret : step (lowerRTL p) ⟨⟨0, 2, 0⟩, ready.set .phi value, [], mem⟩ = .returned [value] mem := by
      simp [step, Prog.fetch, exit, exitBlock, Frame.readAll]
    simp only [Bool.false_eq_true, ite_false]
    exact ⟨_, Width.Proofs.append_step path leave, ret⟩
  | true =>
    have dispatchFound : (lowerRTL p).block? 0 3 = some (dispatch p) := rfl
    have enterDispatch : step (lowerRTL p) ⟨⟨0, 1, sigs.length⟩, ready, [], mem⟩ =
        .running ⟨⟨0, 3, 0⟩, ready, [], mem⟩ := by
      simp only [step, fetched, header, guard, taken, ite_true,
        show (1 : Word) ≠ 0 by decide, ite_false, transfer, dispatchFound]
      rfl
    let values := (p.column side).read args locals
    have packet : ready.readAll (emitColumn (p.column side)) = some (words values) :=
      readColumn_eq (p.column side) args locals ready (fun wire => reads wire)
    have fetchDispatch : (lowerRTL p).fetch ⟨0, 3, 0⟩ = some (.term (dispatch p).term) :=
      Prog.fetch_term dispatchFound
    have selector : ready.get (register p.selector.address) = some (read model p.selector args locals) :=
      reads p.selector
    let selected : Word := read model p.selector args locals
    have choice : (if selected = 0 then emitColumn (p.column false) else emitColumn (p.column true)) =
        emitColumn (p.column side) := by
      change _ = emitColumn (p.column (decide (selected ≠ 0)))
      by_cases zero : selected = (0 : Word)
      · have test : decide (selected ≠ (0 : Word)) = false := decide_eq_false (fun ne => ne zero)
        rw [ite_eq_left zero, test]
      · have test : decide (selected ≠ (0 : Word)) = true := decide_eq_true zero
        rw [ite_eq_right zero, test]
    have latch : step (lowerRTL p) ⟨⟨0, 3, 0⟩, ready, [], mem⟩ =
        .running ⟨⟨0, 1, 0⟩, bindWords captures ready values, [], mem⟩ := by
      simp only [step, fetchDispatch, dispatch, selector, ite_self]
      change transfer (lowerRTL p) _ 1
        (if selected = 0 then emitColumn (p.column false) else emitColumn (p.column true)) = _
      simp only [choice, transfer, packet, found, header, Width.header, bindWords_write]
    have readyArgs : ArgsMatch ready args := fun port => reads (.arg port)
    simp only [ite_true]
    have selectedSlot : (ready.get (register p.selector.address)).map
        (fun value => feedbackSlot (decide (value ≠ (0 : Word)))) = some (feedbackSlot side) := by
      rw [selector]
      rfl
    exact ⟨_, _, Width.Proofs.append_step path enterDispatch, fetchDispatch, selectedSlot,
      feedback_args p side, packet, latch, bank_matches_at (input_matches_at readyArgs) values⟩

theorem checked_activation (mapping : InputMap old new) (p : Source old old entrySigs sigs)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (carried : WordTuple old) (fr : Frame Reg) (mem : Memory)
    (agree : ArgsMatch fr (appendTuple carried input)) :
    Activation (mapCaptures mapping p) prog input fr mem (p.step (mapping.pull input) carried) := by
  obtain ⟨_, rfl, _, _⟩ := lowerChecked_sound mapping p accepted
  rw [← step_mapCaptures mapping p input carried]
  exact activation (mapCaptures mapping p) input carried fr mem agree

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Proofs
