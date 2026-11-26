module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Defs
import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.WellFormed
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Correctness

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg WordOp model)
open Silmaril.SSA.RVSDG (Origin extend)
open Silmaril.SSA.SeaOfNodes.Diamond (Dataflow read)
open Silmaril.SSA.SeaOfNodes.Loop (Graph appendTuple)

variable {captures bank : Nat} {entrySigs sigs : List (List PortTy)}

private theorem supported_mapFlow {arity new : Nat} (mapping : InputMap arity new)
    {past : List (List PortTy)} (flow : Dataflow WordOp (wordPorts arity) past sigs) :
    Table.supported (mapFlow (fun p => mapping.port p) flow) = Table.supported flow := by
  induction flow with
  | nil => rfl
  | cons op args rest ih => cases op <;> simp [mapFlow, Table.supported, ih]

private theorem append_step {program : Prog Reg} {n : Nat} {start middle finish : State Reg}
    (path : StepsNWithin program [] n start middle) (last : step program middle = .running finish) :
    StepsNWithin program [] (n + 1) start finish := by
  induction path with
  | refl => exact .head ⟨last, List.nil_suffix⟩ .refl
  | head next _ ih => exact .head next (ih last)

private theorem entry_packet (g : Source captures bank entrySigs sigs)
    (input : WordTuple captures) (fr : Frame Reg) (mem : Memory)
    (supported : Table.supported g.preheader = true) (capturesMatch : ArgsMatch fr input) :
    ∃ latched, StepsNWithin (lowerRTL g) [] (entrySigs.length + 1) ⟨⟨0, 0, 0⟩, fr, [], mem⟩
      ⟨⟨0, 1, 0⟩, latched, [], mem⟩ ∧ ArgsMatch latched (appendTuple (g.initial model input) input) := by
  have found : (lowerRTL g).block? 0 0 = some (preheader g) := rfl
  obtain ⟨ready, path, capturesReady, reads⟩ :=
    Table.entry_block_at (captures + bank) g.preheader (lowerRTL g) (preheader g)
      found input mem supported (Nat.le_add_right _ _) rfl fr capturesMatch
  have readsWire (wire : Origin (wordPorts captures) (extend [] entrySigs) wordPort) :
      ready.get (entryReg captures bank wire.address) =
        some (read model wire input (g.preheader.eval model input PUnit.unit)) := by
    cases wire with
    | arg p => exact reads (.arg p)
    | output i p => exact reads (.output i p)
  have readsBank : ready.readAll ((g.phiInputs .entry).addresses.map (entryReg captures bank)) =
      some (words (g.initial model input)) :=
    readColumnWith_eq (entryReg captures bank) (g.phiInputs .entry) input _ ready readsWire
  have fetchJump : (lowerRTL g).fetch ⟨0, 0, entrySigs.length⟩ = some (.term (preheader g).term) :=
    preheader_ops_length g ▸ Prog.fetch_term found
  let bankValues := g.initial model input
  have jump : step (lowerRTL g) ⟨⟨0, 0, entrySigs.length⟩, ready, [], mem⟩ =
      .running ⟨⟨0, 1, 0⟩, bindWords captures ready bankValues, [], mem⟩ := by
    have target : (lowerRTL g).block? 0 1 = some (header g) := rfl
    simp only [step, fetchJump, preheader, transfer, readsBank, target, header, bindWords_write, bankValues]
  exact ⟨_, append_step path jump, bank_matches_at capturesReady bankValues⟩

/-- The ordinary checked source supplies the arithmetic admission for the resized entry. -/
theorem checked_entry_packet {old new : Nat} (mapping : InputMap old new)
    {g : SourceWithEntry old entrySigs sigs} {before : Checked.Phi.Targets}
    (accepted : Table.lowerChecked g = some before) (input : WordTuple new) (mem : Memory) :
    let program := lowerRTL (mapCaptures mapping g)
    let start : State Reg := ⟨⟨0, 0, 0⟩, bindWords 0 Frame.empty input, [], mem⟩
    program.start 0 (words input) mem = some start ∧
      ∃ latched, StepsNWithin program [] (entrySigs.length + 1) start
        ⟨⟨0, 1, 0⟩, latched, [], mem⟩ ∧
        ArgsMatch latched (appendTuple (g.initial model (mapping.pull input)) input) := by
  obtain ⟨p, recognized, _, _⟩ := Table.lowerChecked_sound accepted
  have supported : Table.supported g.preheader = true := by
    obtain ⟨rfl, rfl⟩ := Table.recognize_sound recognized
    exact p.arithmetic
  have mapped : Table.supported (mapCaptures mapping g).preheader = true :=
    (supported_mapFlow mapping g.preheader).trans supported
  dsimp only
  constructor
  · change ((Frame.empty.writeAll (paramRegs 0 new) (words input)).map
      (fun regs => (⟨⟨0, 0, 0⟩, regs⟩ : Point × Frame Reg))).map
      (fun entered => (⟨entered.1, entered.2, [], mem⟩ : State Reg)) = _
    rw [bindWords_write]
    rfl
  · rw [← initial_mapCaptures mapping g model input]
    exact entry_packet _ input _ mem mapped (bindWords_args input)

/-- Execute the backedge transfer once the actual header operands have been read.
The bank is rebound from the predecessor frame and the capture prefix stays live. -/
private theorem feedback_transfer (g : Source captures bank entrySigs sigs) (input : WordTuple captures)
    (fr : Frame Reg) (mem : Memory) (values : WordTuple bank)
    (capturesMatch : ArgsMatch fr input)
    (reads : fr.readAll (emitColumn (g.phiInputs .backedge)) = some (words values)) :
    transfer (lowerRTL g) ⟨⟨0, 1, sigs.length⟩, fr, [], mem⟩ 1 (emitColumn (g.phiInputs .backedge)) =
      .running ⟨⟨0, 1, 0⟩, bindWords captures fr values, [], mem⟩ ∧
    ArgsMatch (bindWords captures fr values) (appendTuple values input) := by
  have found : (lowerRTL g).block? 0 1 = some (header g) := rfl
  exact ⟨by simp only [transfer, reads, found, header, bindWords_write],
    bank_matches_at capturesMatch values⟩

/-- If the header's emitted producer registers match the native reads, its actual
conditional exits with the selected word or simultaneously transfers the old-frame
feedback column. Both paths preserve the entire memory. -/
theorem header_terminator (g : Source captures bank entrySigs sigs) (input : WordTuple captures)
    (old : WordTuple bank) (fr : Frame Reg) (mem : Memory) (capturesMatch : ArgsMatch fr input)
    (guard : fr.get (register g.predicate.address) = some
      (if (read model g.predicate (appendTuple old input)
        (g.header.eval model (appendTuple old input) PUnit.unit)).down then 1 else 0))
    (wordsMatch : ∀ wire : Origin (wordPorts captures ++ wordPorts bank) (extend [] sigs) wordPort,
      fr.get (register wire.address) = some
        (read model wire (appendTuple old input) (g.header.eval model (appendTuple old input) PUnit.unit))) :
    match g.step model input old with
    | .inl value =>
      step (lowerRTL g) ⟨⟨0, 1, sigs.length⟩, fr, [], mem⟩ =
        .running ⟨⟨0, 2, 0⟩, fr.set .phi value, [], mem⟩ ∧
      step (lowerRTL g) ⟨⟨0, 2, 0⟩, fr.set .phi value, [], mem⟩ = .returned [value] mem
    | .inr next =>
      step (lowerRTL g) ⟨⟨0, 1, sigs.length⟩, fr, [], mem⟩ =
        .running ⟨⟨0, 1, 0⟩, bindWords captures fr next, [], mem⟩ ∧
      ArgsMatch (bindWords captures fr next) (appendTuple next input) := by
  have found : (lowerRTL g).block? 0 1 = some (header g) := rfl
  have fetch : (lowerRTL g).fetch ⟨0, 1, sigs.length⟩ = some (.term (header g).term) :=
    header_ops_length g ▸ Prog.fetch_term found
  cases h : (read model g.predicate (appendTuple old input)
      (g.header.eval model (appendTuple old input) PUnit.unit)).down with
  | false =>
    have exit : (lowerRTL g).block? 0 2 = some exitBlock := rfl
    have valueRead := wordsMatch g.result
    simp only [Graph.step, h, Bool.false_eq_true, ite_false]
    constructor
    · simp [step, fetch, header, h, guard, transfer, Frame.readAll, valueRead, exit, exitBlock]
      rfl
    · simp [step, Prog.fetch, exit, exitBlock, Frame.readAll]
      rfl
  | true =>
    have reads := readColumn_eq (g.phiInputs .backedge) (appendTuple old input) _ fr wordsMatch
    have back := feedback_transfer g input fr mem
      (g.latch model .backedge (appendTuple old input)
        (g.header.eval model (appendTuple old input) PUnit.unit)) capturesMatch reads
    simpa only [Graph.step, h, ite_true, step, fetch, header, guard, Bool.true_eq,
      show (1 : Word) ≠ 0 by decide, ite_false] using back

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Proofs
