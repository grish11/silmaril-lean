module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Execution
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Loop
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.WellFormed

/-! Checked resized ABI, exact selected occurrences and finite RTL returns. -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Block Prog State StepsNWithin)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (Atom LayoutMatch encodeTuple)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)

variable {captures bank old new tests : Nat} {entrySigs sigs : List (List PortTy)}

/-- The ordinary RTL checker accepts the emitted chain and its bank layout. -/
theorem lowerFunc_wellFormed (p : Source captures bank entrySigs sigs tests) : (lowerFunc p).WellFormed :=
  Proofs.lowerFunc_wellFormed p

/-- Every slot goes through the ordinary source checker. -/
theorem lowerChecked_of_accepted (mapping : InputMap old new)
    (p : Source old old entrySigs sigs tests)
    (rows : ∀ slot, ∃ prior, Table.lowerChecked (p.row slot) = some prior) :
    lowerChecked mapping p = some (lowerRTL (mapCaptures mapping p)) :=
  Proofs.lowerChecked_of_accepted mapping p rows

/-- The checked target has the requested capture arity and a well-formed machine CFG. -/
theorem lowerChecked_sound (mapping : InputMap old new) (p : Source old old entrySigs sigs tests)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog) :
    (∀ slot, ∃ prior, Table.lowerChecked (p.row slot) = some prior) ∧
    prog = lowerRTL (mapCaptures mapping p) ∧ prog.WellFormed ∧
    (prog.func? 0).map (·.sig.params) = some new :=
  Proofs.lowerChecked_sound mapping p accepted

/-- Capture transport preserves the position of the chosen slot and the whole packet. -/
theorem step_mapCaptures (mapping : InputMap old new) (p : Source old bank entrySigs sigs tests)
    (input : WordTuple new) (carried : WordTuple bank) :
    (mapCaptures mapping p).step input carried = p.step (mapping.pull input) carried :=
  Proofs.step_mapCaptures mapping p input carried

/-- Select the existing explicit-Φ column of the corresponding native projection. -/
theorem phi_feedback (p : Source captures bank entrySigs sigs tests) (slot : Fin (tests + 1))
    (input : WordTuple captures) (carried : WordTuple bank) {env : Env (Atom model)}
    (matched : LayoutMatch model (Generic.headerLayout (p.row slot)) env (appendTuple carried input)
      ((p.row slot).header.eval model (appendTuple carried input) PUnit.unit)) :
    Silmaril.SSA.PhiView.latch (Generic.phiView (p.row slot)) (Generic.edge (p.row slot) .backedge)
      (extend env .unit) =
      encodeTuple model ((p.rows.column slot).read (appendTuple carried input)
        ((p.row slot).header.eval model (appendTuple carried input) PUnit.unit)) :=
  Generic.feedback_latch (p.row slot) model input carried matched

/-- The chosen RTL packet is compared with the typed Φ latch at the same native slot. -/
theorem selected_phi_packet (p : Source captures bank entrySigs sigs tests)
    (input : WordTuple captures) (carried : WordTuple bank) (slot : Fin (tests + 1))
    (values : WordTuple bank) (taken : p.step input carried = .inr (slot, values))
    {env : Env (Atom model)}
    (matched : LayoutMatch model (Generic.headerLayout (p.row slot)) env (appendTuple carried input)
      ((p.row slot).header.eval model (appendTuple carried input) PUnit.unit)) :
    Silmaril.SSA.PhiView.latch (Generic.phiView (p.row slot)) (Generic.edge (p.row slot) .backedge)
      (extend env .unit) = encodeTuple model values :=
  (phi_feedback p slot input carried matched).trans
    (congrArg (encodeTuple model) (Proofs.selected_column p input carried slot values taken).2.symm)

/-- The actual entry latches the native bank at the pulled valuation. -/
theorem entry_packet (mapping : InputMap old new) (p : Source old old entrySigs sigs tests)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (mem : Memory) :
    let start : State Reg := ⟨⟨0, 0, 0⟩, bindWords 0 Frame.empty input, [], mem⟩
    prog.start 0 (words input) mem = some start ∧
      ∃ latched, StepsNWithin prog [] (entrySigs.length + 1) start
        ⟨⟨0, 1, 0⟩, latched, [], mem⟩ ∧
        ArgsMatch latched (appendTuple (p.primary.initial model (mapping.pull input)) input) :=
  Proofs.entry_packet mapping p accepted input mem

/-- One actual activation preserves memory and reaches the selected occurrence before rebinding the bank. -/
theorem checked_activation (mapping : InputMap old new) (p : Source old old entrySigs sigs tests)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (carried : WordTuple old) (fr : Frame Reg) (mem : Memory)
    (agree : ArgsMatch fr (appendTuple carried input)) :
    Activation (mapCaptures mapping p) prog input fr mem (p.step (mapping.pull input) carried) :=
  Proofs.checked_activation mapping p accepted input carried fr mem agree

/-- Expose the producer frame, skipped dispatcher steps and exact rebound bank on a continuing visit. -/
theorem checked_feedback_cut (mapping : InputMap old new) (p : Source old old entrySigs sigs tests)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (carried : WordTuple old) (fr : Frame Reg) (mem : Memory)
    (agree : ArgsMatch fr (appendTuple carried input)) (slot : Fin (tests + 1)) (next : WordTuple old)
    (taken : p.step (mapping.pull input) carried = .inr (slot, next)) :
    ∃ ready latched block, FeedbackCut (mapCaptures mapping p) prog input carried fr ready latched mem slot next block :=
  Proofs.checked_feedback_cut mapping p accepted input carried fr mem agree slot next taken

/-- Expose the exact false-successor operands, exit frame and return of one
actual checked RTL header visit. -/
theorem checked_exit_cut (mapping : InputMap old new) (p : Source old old entrySigs sigs tests)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (carried : WordTuple old) (fr : Frame Reg) (mem : Memory)
    (agree : ArgsMatch fr (appendTuple carried input)) (value : Word)
    (taken : p.step (mapping.pull input) carried = .inl value) :
    ∃ ready, ExitCut (mapCaptures mapping p) prog input carried fr ready mem value :=
  Proofs.checked_exit_cut mapping p accepted input carried fr mem agree value taken

/-- Independent machine fuel and source slot sequences agree through their exact instruction cost. -/
theorem rtl_runMain_fuel_iff (mapping : InputMap old new) (p : Source old old entrySigs sigs tests)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (initial final : Memory) (returned : List Word) (fuel : Nat) :
    prog.runMain fuel 0 (words input) initial = .returned returned final ↔
      ∃ slots value, p.ReturnsAlong (mapping.pull input) slots (p.primary.initial model (mapping.pull input)) value ∧
        rtlFuel entrySigs sigs slots ≤ fuel ∧ returned = [value] ∧ final = initial :=
  Proofs.rtl_runMain_fuel_iff mapping p accepted input initial final returned fuel

/-- The finite-return witnesses agree on the returned word and full memory. -/
theorem rtl_return_iff (mapping : InputMap old new) (p : Source old old entrySigs sigs tests)
    {prog : Prog Reg} (accepted : lowerChecked mapping p = some prog)
    (input : WordTuple new) (initial final : Memory) (returned : List Word) :
    prog.oracle 0 (words input) initial returned final ↔
      ∃ slots value, p.ReturnsAlong (mapping.pull input) slots (p.primary.initial model (mapping.pull input)) value ∧
        returned = [value] ∧ final = initial :=
  Proofs.rtl_return_iff mapping p accepted input initial final returned

/-- Compose the initial producer steps, skipped rows and the selected transfer. -/
theorem FeedbackCut.path {p : Source captures bank entrySigs sigs tests}
    {prog : Prog Reg} {input : WordTuple captures} {carried values : WordTuple bank}
    {before ready latched : Frame Reg} {mem : Memory} {slot : Fin (tests + 1)} {block : Block Reg}
    (cut : FeedbackCut p prog input carried before ready latched mem slot values block) :
    StepsNWithin prog [] (sigs.length + 1 + (slot.val + 1))
      ⟨⟨0, 1, 0⟩, before, [], mem⟩ ⟨⟨0, 1, 0⟩, latched, [], mem⟩ :=
  Proofs.FeedbackCut.path cut

/-- The deterministic native selector and row step make the chosen slot
sequence of a finite return unique at a fixed input, carried bank and
returned word. -/
theorem returnsAlong_unique (p : Source captures bank entrySigs sigs tests) (input : WordTuple captures)
    {slots other : List (Fin (tests + 1))} {carried : WordTuple bank} {value : Word}
    (left : p.ReturnsAlong input slots carried value) (right : p.ReturnsAlong input other carried value) :
    slots = other :=
  Proofs.returnsAlong_unique p input left right

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family
