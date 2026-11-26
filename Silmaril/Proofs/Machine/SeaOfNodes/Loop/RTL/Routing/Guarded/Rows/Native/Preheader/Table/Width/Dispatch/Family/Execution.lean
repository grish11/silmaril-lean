module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Defs
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Correctness
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Execution
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.WellFormed
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Route

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Proofs

open Silmaril.Machine.Lir (Word Memory)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.SSA.SeaOfNodes.Diamond (read)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)

variable {captures bank old new tests : Nat} {entrySigs sigs : List (List PortTy)}

private theorem map_column (mapping : InputMap old new) (rows : Choices old bank sigs tests)
    (slot : Fin (tests + 1)) :
    (rows.mapCaptures mapping).column slot = mapColumn (fun p => Width.headerPort mapping p) (rows.column slot) := by
  induction rows with
  | last _ => rfl
  | test _ _ _ ih =>
    refine Fin.cases rfl (fun i => ?_) slot
    exact ih i

private theorem map_select (mapping : InputMap old new) (rows : Choices old bank sigs tests)
    (before : HeaderWord old bank sigs → Word) (after : HeaderWord new bank sigs → Word)
    (agree : ∀ w, after (mapOrigin (fun p => Width.headerPort mapping p) w) = before w) :
    (rows.mapCaptures mapping).select after = rows.select before := by
  induction rows with
  | last _ => rfl
  | test w _ tail ih =>
    change (if after (mapOrigin (fun p => Width.headerPort mapping p) w) = 0 then _ else _) =
      (if before w = 0 then _ else _)
    rw [agree w, ih]

theorem step_mapCaptures (mapping : InputMap old new) (p : Source old bank entrySigs sigs tests)
    (input : WordTuple new) (carried : WordTuple bank) :
    (mapCaptures mapping p).step input carried = p.step (mapping.pull input) carried := by
  have selected : (mapCaptures mapping p).select input carried = p.select (mapping.pull input) carried :=
    map_select mapping p.rows _ _ (Width.Proofs.header_read_mapCaptures mapping p.primary model input carried)
  let slot := p.select (mapping.pull input) carried
  have row : (mapCaptures mapping p).row slot = Width.mapCaptures mapping (p.row slot) := by
    change withFeedback (Width.mapCaptures mapping p.primary) ((p.rows.mapCaptures mapping).column slot) = _
    rw [map_column]
    rfl
  have same := (congrArg (fun g : Width.Source new bank entrySigs sigs => g.step model input carried) row).trans
    (Width.Proofs.step_mapCaptures mapping (p.row slot) model input carried)
  rw [Source.step, Source.step, selected]
  let tag : Word ⊕ WordTuple bank → Word ⊕ (Fin (tests + 1) × WordTuple bank)
    | .inl value => .inl value
    | .inr next => .inr (slot, next)
  exact congrArg tag same

theorem admitsRows_iff (p : Source old old entrySigs sigs tests) :
    admitsRows p = true ↔ ∀ slot, ∃ prior, Table.lowerChecked (p.row slot) = some prior := by
  rw [admitsRows, List.all_eq_true]
  constructor
  · intro ok slot
    have checked := ok slot (List.mem_finRange slot)
    cases h : Table.lowerChecked (p.row slot) with
    | none => rw [h] at checked; cases checked
    | some target => exact ⟨target, rfl⟩
  · intro ok slot _
    obtain ⟨prior, checked⟩ := ok slot
    rw [checked]
    rfl

theorem lowerChecked_sound (mapping : InputMap old new) (p : Source old old entrySigs sigs tests)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog) :
    (∀ slot, ∃ prior, Table.lowerChecked (p.row slot) = some prior) ∧
    prog = lowerRTL (mapCaptures mapping p) ∧ prog.WellFormed ∧
    (prog.func? 0).map (·.sig.params) = some new := by
  unfold lowerChecked at accepted
  split at accepted
  · rename_i rows
    dsimp only at accepted
    split at accepted
    · rename_i wf
      cases Option.some.inj accepted
      refine ⟨(admitsRows_iff p).mp rows, rfl, ?_, rfl⟩
      intro fn member
      have eq : fn = lowerFunc (mapCaptures mapping p) := List.mem_singleton.mp member
      exact eq.symm ▸ wf
    · cases accepted
  · cases accepted

theorem entry_packet (mapping : InputMap old new) (p : Source old old entrySigs sigs tests)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (mem : Memory) :
    let start : State Reg := ⟨⟨0, 0, 0⟩, bindWords 0 Frame.empty input, [], mem⟩
    prog.start 0 (words input) mem = some start ∧
      ∃ latched, StepsNWithin prog [] (entrySigs.length + 1) start
        ⟨⟨0, 1, 0⟩, latched, [], mem⟩ ∧
        ArgsMatch latched (appendTuple (p.primary.initial model (mapping.pull input)) input) := by
  obtain ⟨rows, rfl, _, _⟩ := lowerChecked_sound mapping p accepted
  obtain ⟨prior, checked⟩ := rows 0
  obtain ⟨plan, found, _, _⟩ := Table.lowerChecked_sound checked
  have arithmetic : Table.supported p.primary.preheader = true := by
    change Table.supported (p.row 0).preheader = true
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

private theorem row_step (p : Source captures bank entrySigs sigs tests) (slot : Fin (tests + 1))
    (input : WordTuple captures) (carried : WordTuple bank) :
    (p.row slot).step model input carried =
      let args := appendTuple carried input
      let locals := p.primary.header.eval model args PUnit.unit
      if (read model p.primary.predicate args locals).down then .inr ((p.rows.column slot).read args locals)
      else .inl (read model p.primary.result args locals) :=
  rfl

theorem selected_column (p : Source captures bank entrySigs sigs tests)
    (input : WordTuple captures) (carried : WordTuple bank) (slot : Fin (tests + 1))
    (values : WordTuple bank) (taken : p.step input carried = .inr (slot, values)) :
    slot = p.select input carried ∧ values =
      (p.rows.column slot).read (appendTuple carried input)
        (p.primary.header.eval model (appendTuple carried input) PUnit.unit) := by
  have row := row_step p (p.select input carried) input carried
  unfold Source.step at taken
  dsimp only at taken
  rw [row] at taken
  dsimp only at taken
  cases guard : (read model p.primary.predicate (appendTuple carried input)
      (p.primary.header.eval model (appendTuple carried input) PUnit.unit)).down with
  | false => simp [guard] at taken
  | true =>
    simp only [guard, ite_true, Sum.inr.injEq, Prod.mk.injEq] at taken
    refine ⟨taken.1.symm, ?_⟩
    rw [← taken.1]
    exact taken.2.symm

private theorem first_block (rows : Choices captures bank sigs tests) :
    ∃ b, (rows.blocks 3)[0]? = some b ∧ b.params = [] := by
  cases rows <;> exact ⟨_, rfl, rfl⟩

theorem activation (p : Source captures bank entrySigs sigs tests) (input : WordTuple captures)
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
  let slot := p.select input carried
  have guard : ready.get (register p.primary.predicate.address) =
      some (if (read model p.primary.predicate args locals).down then 1 else 0) := reads p.primary.predicate
  have selectedStep := row_step p slot input carried
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
    have enters : step (lowerRTL p) ⟨⟨0, 1, sigs.length⟩, ready, [], mem⟩ =
        .running ⟨⟨0, 3, 0⟩, ready, [], mem⟩ := by
      obtain ⟨b, first, params⟩ := first_block p.rows
      have atStart : (lowerRTL p).block? 0 3 = some b := (chain_block p 0).trans first
      simp only [step, fetched, header, guard, taken, ite_true, show (1 : Word) ≠ 0 by decide,
        ite_false, transfer, show ready.readAll [] = some [] from rfl, atStart, params, Frame.writeAll]
    obtain ⟨b, inspected, hb, operand, packet, latch⟩ := route p.rows (lowerRTL p) 3
      (chain_block p) ⟨header p, found, rfl⟩ args locals ready mem (fun w => reads w)
    have readyArgs : ArgsMatch ready args := fun port => reads (.arg port)
    simp only [ite_true]
    exact ⟨_, _, b, append_paths (Width.Proofs.append_step path enters) inspected, hb, operand,
      packet, latch, bank_matches_at (input_matches_at readyArgs) ((p.rows.column slot).read args locals)⟩

theorem checked_activation (mapping : InputMap old new) (p : Source old old entrySigs sigs tests)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (carried : WordTuple old) (fr : Frame Reg) (mem : Memory)
    (agree : ArgsMatch fr (appendTuple carried input)) :
    Activation (mapCaptures mapping p) prog input fr mem (p.step (mapping.pull input) carried) := by
  obtain ⟨_, rfl, _, _⟩ := lowerChecked_sound mapping p accepted
  rw [← step_mapCaptures mapping p input carried]
  exact activation (mapCaptures mapping p) input carried fr mem agree

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Proofs
