module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Phi.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Thms
public import Silmaril.SSA.PhiView.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Phi.Execution
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Phi.Observations

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Phi

open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA (Region)
open Silmaril.Isotope.LambdaSSA.Semantics (Env)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)
open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame Opcode packValues packValues_injective)
open Silmaril.Machine.RTL.SSA (Block Func Prog StepsNWithin step toLambdaSSA toLambdaSSA_hasType)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)

variable {tests old new : Nat} {fn : Func Reg}
variable {entrySigs sigs : List (List PortTy)}

/-- A successful flat word packet check preserves the exact ordered RTL operands. -/
theorem checkPacket_registers {scope regs : List Reg} {width : Nat} {packet : Packet scope width}
    (checked : checkPacket scope width regs = some packet) : packet.registers = regs :=
  Proofs.checkPacket_registers checked

/-- A shared header label never identifies two incoming occurrences. -/
theorem key_injective : Function.Injective (@key tests) :=
  Proofs.key_injective

/-- Each extracted branch has precisely the packed header parameter type. -/
theorem branch_hasType (checked : Checked fn tests) (i : Incoming tests) :
    (checked.terms i).HasType (params fn.allDefs.length)
      [Silmaril.unit, Silmaril.SSA.PhiView.packedType (params (fn.paramCount 1))] :=
  .br rfl (Silmaril.SSA.PhiView.packTerm_hasType (checked.column i).arguments)

/-- Reifying a column recovers the exact original operand list at its RTL successor occurrence. -/
theorem readColumn_roundTrip (checked : Checked fn tests) (i : Incoming tests) :
    ∃ block, fn.block? (key i).1 = some block ∧
      block.term.args[(key i).2]? = some (1, (checked.column i).registers) :=
  Proofs.readColumn_roundTrip checked i

/-- Decoding the actual explicit-Φ column reproduces the machine successor, including its operand order. -/
theorem reemit_roundTrip (checked : Checked fn tests) (i : Incoming tests) :
    (fn.block? (key i).1).bind (fun block => block.term.args[(key i).2]?) = checked.reemit i :=
  Proofs.reemit_roundTrip checked i

/-- The ordinary RTL checker supplies operand availability and arity for each existing header successor. -/
theorem extract_of_incoming (wf : fn.WellFormed)
    (incoming : ∀ i : Incoming tests, ∃ block regs,
      fn.block? (key i).1 = some block ∧ block.term.args[(key i).2]? = some (1, regs)) :
    (extract fn tests).isSome :=
  Proofs.extract_of_incoming wf incoming

/-- Every emitted family has an extractable entry and every positional feedback column. -/
theorem extract_family (p : Source new old entrySigs sigs tests) :
    (extract (lowerFunc p) tests).isSome :=
  Proofs.extract_family p

/-- The typed Φ view reads the entire RTL packet from the same old frame. -/
theorem latch_agrees (checked : Checked fn tests) (i : Incoming tests) (frame : Frame Reg)
    (values : List Word) (read : frame.readAll (checked.column i).registers = some values) :
    Silmaril.SSA.PhiView.latch checked.view (checked.edge i) (snapshot fn.allDefs frame) =
      packValues values :=
  Proofs.latch_agrees checked i frame values read

/-- The actual dispatch reaches the chosen occurrence, where the typed branch and machine rebinding agree. -/
theorem selected (mapping : InputMap old new) (p : Source old old entrySigs sigs tests)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (checked : Checked (lowerFunc (mapCaptures mapping p)) tests)
    (input : WordTuple new) (carried : WordTuple old) (frame : Frame Reg) (mem : Memory)
    (matchFrame : ArgsMatch frame (appendTuple carried input))
    (slot : Fin (tests + 1)) (values : WordTuple old)
    (taken : p.step (mapping.pull input) carried = .inr (slot, values)) :
    let i := slot.succ
    ∃ ready latched,
      StepsNWithin prog [] (sigs.length + 1 + slot.val)
        ⟨⟨0, 1, 0⟩, frame, [], mem⟩ ⟨⟨0, (key i).1, 0⟩, ready, [], mem⟩ ∧
      (checked.column i).registers = emitColumn ((mapCaptures mapping p).rows.column slot) ∧
      Eval (Opcode.step (sigs := []) prog.oracle) (snapshot (lowerFunc (mapCaptures mapping p)).allDefs ready)
        (.br 1 (checked.edge i).argument) mem 1 (packValues (words values)) mem ∧
      step prog ⟨⟨0, (key i).1, 0⟩, ready, [], mem⟩ =
        .running ⟨⟨0, 1, 0⟩, latched, [], mem⟩ ∧
      ArgsMatch latched (appendTuple values input) :=
  Proofs.selected mapping p accepted checked input carried frame mem matchFrame slot values taken

/-- The canonical RTL translator emits a typed λSSA region at the resized ABI. -/
theorem region_hasType (p : Source new old entrySigs sigs tests) :
    Region.HasType [Silmaril.Machine.RTL.packTy new] (toLambdaSSA [⟨new, 1⟩] (lowerFunc p))
      [Silmaril.Machine.RTL.packTy 1, Silmaril.Ty.unit] :=
  toLambdaSSA_hasType (lowerFunc_wellFormed p) (Proofs.callsMatch p)

/-- An exit-zero result is exactly the packed machine return and its full final memory. -/
theorem region_exit_iff (mapping : InputMap old new) (p : Source old old entrySigs sigs tests)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (env : Env Word) (entry : env 0 = packValues (words input))
    (initial final : Memory) (value : Value Word) :
    Eval (Opcode.step (sigs := [⟨new, 1⟩]) prog.oracle) env
      (toLambdaSSA [⟨new, 1⟩] (lowerFunc (mapCaptures mapping p))) initial 0 value final ↔
      ∃ returned, value = packValues returned ∧ prog.oracle 0 (words input) initial returned final :=
  Proofs.region_exit_iff mapping p accepted input env entry initial final value

/-- Finite returns of the actual translated CFG agree with machine returns, including all memory. -/
theorem region_return_iff (mapping : InputMap old new) (p : Source old old entrySigs sigs tests)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (env : Env Word) (entry : env 0 = packValues (words input))
    (initial final : Memory) (returned : List Word) :
    Eval (Opcode.step (sigs := [⟨new, 1⟩]) prog.oracle) env
      (toLambdaSSA [⟨new, 1⟩] (lowerFunc (mapCaptures mapping p))) initial 0 (packValues returned) final ↔
      prog.oracle 0 (words input) initial returned final := by
  simp [region_exit_iff mapping p accepted input env entry, packValues_injective.eq_iff]

/-- Absence quantifies over all return witnesses, with no identification of backend budgets. -/
theorem region_no_return_iff (mapping : InputMap old new) (p : Source old old entrySigs sigs tests)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (env : Env Word) (entry : env 0 = packValues (words input)) (initial : Memory) :
    (¬ ∃ value final, Eval (Opcode.step (sigs := [⟨new, 1⟩]) prog.oracle) env
      (toLambdaSSA [⟨new, 1⟩] (lowerFunc (mapCaptures mapping p))) initial 0 value final) ↔
    (¬ ∃ returned final, prog.oracle 0 (words input) initial returned final) := by
  simp only [region_exit_iff mapping p accepted input env entry]
  exact ⟨fun absent ⟨ret, final, run⟩ => absent ⟨packValues ret, final, ret, rfl, run⟩,
    fun absent ⟨_, final, ret, _, run⟩ => absent ⟨ret, final, run⟩⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Phi
