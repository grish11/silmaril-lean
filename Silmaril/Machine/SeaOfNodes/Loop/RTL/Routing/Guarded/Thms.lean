module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Agreement
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Execution

/-! # Exact guarded bank transfers and paired finite returns -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Prog StepsNWithin)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg model word)
open Silmaril.SSA
open Silmaril.SSA.SeaOfNodes.Loop (Incoming appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA
  (Atom LayoutMatch encodeTuple inputEnv instruction terminatorRegion)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

theorem recognize_eq_some_iff (g : Native) (p : Profile) :
    recognize g = some p ↔ g = graph p :=
  Proofs.recognize_eq_some_iff g p

theorem lowerChecked_eq_some_iff (g : Native) (targets : Checked.Phi.Targets) :
    lowerChecked g = some targets ↔
      (∃ p : Profile, g = graph p) ∧ (lowerBankFunc g).WellFormed ∧
        targets = (rtl g, Generic.lower g) :=
  Proofs.lowerChecked_eq_some_iff g targets

theorem lowerChecked_typed {g : Native} {targets : Checked.Phi.Targets}
    (accepted : lowerChecked g = some targets) :
    targets.1.WellFormed ∧ targets.2.HasType (Generic.inputContext (wordSorts 2))
      [Generic.packed [.value word]] := by
  obtain ⟨_, wf, rfl⟩ := (lowerChecked_eq_some_iff g targets).mp accepted
  exact ⟨by simpa [rtl, lowerBank, Prog.WellFormed] using wf, Generic.lower_hasType g⟩

/-- The RTL source block and successor ordinal select the same occurrence
as the corresponding slot of either explicit Φ presentation. -/
theorem incoming_alignment (p : Profile) (order : Fin 2 ≃ Generic.HeaderIncoming (graph p))
    (arrival : Incoming) :
    ((lowerBankFunc (graph p)).block? (RTL.incomingSlot arrival).1).bind
        (fun block => block.term.args[(RTL.incomingSlot arrival).2]?) =
      some (1, bankIncoming (graph p) arrival) ∧
    Generic.slotBranch (graph p) order (order.symm (Generic.headerIncoming (graph p) arrival)) =
      .br 0 (Generic.edge (graph p) arrival).argument :=
  ⟨by cases arrival <;> rfl, Generic.slot_branch_roundtrip (graph p) order
    (Generic.headerIncoming (graph p) arrival)⟩

/-- The second field reads the old first field in the same activation. -/
theorem feedback_latch (p : Profile) (input : WordTuple 2) (first second : Word) :
    let args := appendTuple (pair first second) input
    (graph p).latch model .backedge args ((graph p).header.eval model args PUnit.unit) =
      pair (p.update.eval first second) first :=
  Proofs.feedback_latch p input first second

theorem native_step (p : Profile) (input : WordTuple 2) (first second : Word) :
    (graph p).step model input (pair first second) =
      if p.guardWord first second = 0 then .inl second else .inr (pair (p.update.eval first second) first) :=
  Proofs.native_step p input first second

theorem header_activation (p : Profile) (fr : Frame Reg) (first second : Word) (mem : Memory)
    (hfirst : fr.get (.arg 2) = some first) (hsecond : fr.get (.arg 3) = some second) :
    StepsNWithin (rtl (graph p)) [] 4 ⟨⟨0, 1, 0⟩, fr, [], mem⟩ (successor p fr first second mem) :=
  Proofs.header_activation p fr first second mem hfirst hsecond

/-- Both actual headers take the same guard and transfer the same native
observation. Both preserve the entire memory. -/
theorem activation_agrees (p : Profile) (input : WordTuple 2) (first second : Word)
    (fr : Frame Reg) (mem : Memory)
    (hfirst : fr.get (.arg 2) = some first) (hsecond : fr.get (.arg 3) = some second) :
    let eval := Eval (instruction model) (extend (inputEnv model input) (encodeTuple model (pair first second)))
      (Generic.header (graph p)) mem
    StepsNWithin (rtl (graph p)) [] 4 ⟨⟨0, 1, 0⟩, fr, [], mem⟩ (successor p fr first second mem) ∧
      if p.guardWord first second = 0 then eval 1 (Generic.packResult model (out := word) second) mem
      else eval 0 (encodeTuple model (pair (p.update.eval first second) first)) mem :=
  Proofs.activation_agrees p input first second fr mem hfirst hsecond

/-- Read the exact full feedback packet in either positional order. -/
theorem feedback_slot_transfer_iff (p : Profile) (order : Fin 2 ≃ Generic.HeaderIncoming (graph p))
    (input : WordTuple 2) (first second : Word) {env : Env (Atom model)}
    (matched : let args := appendTuple (pair first second) input
      LayoutMatch model (Generic.headerLayout (graph p)) env args
        ((graph p).header.eval model args PUnit.unit))
    (start finish : Memory) (label : Nat) (payload : Value (Atom model)) :
    Eval (instruction model) (extend env .unit)
        (terminatorRegion (Generic.slotBranch (graph p) order
          (order.symm (Generic.headerIncoming (graph p) .backedge))))
        start label payload finish ↔
      label = 0 ∧ payload = encodeTuple model (pair (p.update.eval first second) first) ∧ finish = start :=
  Proofs.feedback_slot_transfer_iff p order input first second matched start finish label payload

theorem rtl_returns_iff (p : Profile) (input : WordTuple 2) (initial final : Memory)
    (returned : List Word) :
    (rtl (graph p)).oracle 0 (words input) initial returned final ↔
      ∃ value : Word, (graph p).Returns model input value ∧ returned = [value] ∧ final = initial :=
  Proofs.rtl_returns_iff p input initial final returned

/-- Finite returns agree in both directions on the word and whole memory. -/
theorem returns_iff {g : Native} {targets : Checked.Phi.Targets} (accepted : lowerChecked g = some targets)
    (input : WordTuple 2) (initial final : Memory) (returned : List Word) :
    targets.1.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, returned = [value] ∧
        Eval (instruction model) (inputEnv model input) targets.2
          initial 0 (Generic.packResult model (out := word) value) final :=
  Proofs.returns_iff accepted input initial final returned

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded
