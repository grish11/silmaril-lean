module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Execution
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Loop
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.WellFormed

/-! The ordinary checker and exact activation of the resized feedback dispatcher. -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Prog State StepsNWithin)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (Atom LayoutMatch encodeTuple)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

variable {captures bank old new : Nat} {entrySigs sigs : List (List PortTy)}

/-- The ordinary SSA checker validates the emitted layout, including both dispatcher arms. -/
theorem lowerFunc_wellFormed (p : Source captures bank entrySigs sigs) : (lowerFunc p).WellFormed :=
  Proofs.lowerFunc_wellFormed p

/-- Both ordinary row admissions suffice for checked re-emission at the new input width. -/
theorem lowerChecked_of_accepted (mapping : InputMap old new)
    (p : Source old old entrySigs sigs) {left right : Checked.Phi.Targets}
    (primary : Table.lowerChecked (p.row true) = some left)
    (other : Table.lowerChecked (p.row false) = some right) :
    lowerChecked mapping p = some (lowerRTL (mapCaptures mapping p)) :=
  Proofs.lowerChecked_of_accepted mapping p primary other

/-- A successful check gives the admitted rows and the actual function at the resized ABI. -/
theorem lowerChecked_sound (mapping : InputMap old new) (p : Source old old entrySigs sigs)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog) :
    (∀ side, ∃ before, Table.lowerChecked (p.row side) = some before) ∧
    prog = lowerRTL (mapCaptures mapping p) ∧ prog.WellFormed ∧
    (prog.func? 0).map (·.sig.params) = some new :=
  Proofs.lowerChecked_sound mapping p accepted

/-- The dispatch arm names the corresponding successor slot and complete operand column. -/
theorem feedback_args (p : Source captures bank entrySigs sigs) (side : Bool) :
    ((dispatch p).term.args)[(feedbackSlot side).val]? = some (1, emitColumn (p.column side)) :=
  Proofs.feedback_args p side

/-- In the existing explicit-Φ view of the selected projection, the
feedback latch gives the native column read by the RTL dispatcher. -/
theorem phi_feedback (p : Source captures bank entrySigs sigs) (side : Bool)
    (input : WordTuple captures) (carried : WordTuple bank) {env : Env (Atom model)}
    (matched : LayoutMatch model (Generic.headerLayout (p.row side)) env (appendTuple carried input)
      ((p.row side).header.eval model (appendTuple carried input) PUnit.unit)) :
    Silmaril.SSA.PhiView.latch (Generic.phiView (p.row side)) (Generic.edge (p.row side) .backedge)
      (extend env .unit) =
      encodeTuple model ((p.column side).read (appendTuple carried input)
        ((p.row side).header.eval model (appendTuple carried input) PUnit.unit)) :=
  Generic.feedback_latch (p.row side) model input carried matched

/-- Source capture transport preserves the selected occurrence and the complete packet. -/
theorem step_mapCaptures (mapping : InputMap old new) (p : Source old bank entrySigs sigs)
    (input : WordTuple new) (carried : WordTuple bank) :
    (mapCaptures mapping p).step input carried = p.step (mapping.pull input) carried :=
  Proofs.step_mapCaptures mapping p input carried

/-- Entry starts at the new input width and binds the native initial bank at the pulled valuation. -/
theorem entry_packet (mapping : InputMap old new) (p : Source old old entrySigs sigs)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (mem : Memory) :
    let start : State Reg := ⟨⟨0, 0, 0⟩, bindWords 0 Frame.empty input, [], mem⟩
    prog.start 0 (words input) mem = some start ∧
      ∃ latched, StepsNWithin prog [] (entrySigs.length + 1) start
        ⟨⟨0, 1, 0⟩, latched, [], mem⟩ ∧
        ArgsMatch latched (appendTuple (p.primary.initial model (mapping.pull input)) input) :=
  Proofs.entry_packet mapping p accepted input mem

/-- The actual emitted steps implement one native visit at the pulled valuation.
Feedback preserves its successor index and binds the full old-frame packet. -/
theorem checked_activation (mapping : InputMap old new) (p : Source old old entrySigs sigs)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (carried : WordTuple old) (fr : Frame Reg) (mem : Memory)
    (agree : ArgsMatch fr (appendTuple carried input)) :
    Activation (mapCaptures mapping p) prog input fr mem (p.step (mapping.pull input) carried) :=
  Proofs.checked_activation mapping p accepted input carried fr mem agree

/-- Exact RTL instruction cost for a counted native return, with the entire memory preserved. -/
theorem rtl_runMain_fuel_iff (mapping : InputMap old new) (p : Source old old entrySigs sigs)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (initial final : Memory) (returned : List Word) (fuel : Nat) :
    prog.runMain fuel 0 (words input) initial = .returned returned final ↔
      ∃ count value, p.ReturnsAfter (mapping.pull input) count (p.primary.initial model (mapping.pull input)) value ∧
        rtlFuel entrySigs sigs count ≤ fuel ∧ returned = [value] ∧ final = initial :=
  Proofs.rtl_runMain_fuel_iff mapping p accepted input initial final returned fuel

/-- The actual RTL return and the native counted return have independent witnesses. -/
theorem rtl_return_iff (mapping : InputMap old new) (p : Source old old entrySigs sigs)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (initial final : Memory) (returned : List Word) :
    prog.oracle 0 (words input) initial returned final ↔
      ∃ count value, p.ReturnsAfter (mapping.pull input) count (p.primary.initial model (mapping.pull input)) value ∧
        returned = [value] ∧ final = initial :=
  Proofs.rtl_return_iff mapping p accepted input initial final returned

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch
