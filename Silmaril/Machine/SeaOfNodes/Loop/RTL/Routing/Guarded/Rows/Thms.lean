module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex.Thms
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Agreement
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Execution

/-! # Shared guard decision, simultaneous transfer and exit projection -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows

open Silmaril.Machine.Lir (Memory)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (Prog Steps StepsNWithin)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg model word)
open Silmaril.SSA
open Silmaril.SSA.SeaOfNodes.Loop (Incoming appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA
  (Atom LayoutMatch encodeTuple inputEnv instruction terminatorRegion)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

theorem lowerChecked_eq_some_iff (arity : Nat) (spec : Spec) (targets : Checked.Phi.Targets) :
    lowerChecked arity spec = some targets ↔
      ∃ p, checkPlan arity spec = some p ∧ (lowerBankFunc p.graph).WellFormed ∧
        targets = (lowerBank p.graph, Generic.lower p.graph) :=
  Proofs.lowerChecked_eq_some_iff arity spec targets

theorem lowerChecked_typed {arity : Nat} {spec : Spec} {targets : Checked.Phi.Targets}
    (accepted : lowerChecked arity spec = some targets) :
    targets.1.WellFormed ∧ targets.2.HasType (Generic.inputContext (wordSorts arity))
      [Generic.packed [.value word]] := by
  obtain ⟨p, _, wf, rfl⟩ := (lowerChecked_eq_some_iff arity spec targets).mp accepted
  exact ⟨by simpa [lowerBank, Prog.WellFormed] using wf, Generic.lower_hasType p.graph⟩

theorem incoming_alignment {arity : Nat} (p : Plan arity) (order : Fin 2 ≃ Generic.HeaderIncoming p.graph)
    (arrival : Incoming) :
    ((lowerBankFunc p.graph).block? (RTL.incomingSlot arrival).1).bind
        (fun block => block.term.args[(RTL.incomingSlot arrival).2]?) =
      some (1, bankIncoming p.graph arrival) ∧
    Generic.slotBranch p.graph order (order.symm (Generic.headerIncoming p.graph arrival)) =
      .br 0 (Generic.edge p.graph arrival).argument :=
  ⟨by cases arrival <;> rfl, Generic.slot_branch_roundtrip p.graph order
    (Generic.headerIncoming p.graph arrival)⟩

/-- The guard tail leaves every operand of the simultaneous row intact. -/
theorem feedback_latch {arity : Nat} (p : Plan arity) (input old : WordTuple arity) :
    let args := appendTuple old input
    p.graph.latch model .backedge args (p.graph.header.eval model args PUnit.unit) = p.nextBank input old :=
  Proofs.feedback_latch p input old

/-- The emitted comparison reads the computed left operand and the selected right operand. -/
theorem guard_compare_operand {arity : Nat} (p : Plan arity) :
    (bankHeader p.graph).ops[p.compareIndex]? =
      some (.binary (.cmp p.comparison.target) (.node p.compareIndex) (.node p.guardIndex.val)
        (register p.guardRhsWire.address)) :=
  Proofs.guard_compare_operand p

/-- A computed RHS reads its own row result register. -/
theorem guard_compare_computed {arity : Nat} (p : Plan arity) (right : Fin p.updates.length)
    (selected : p.guardOperand = .computed right) :
    (bankHeader p.graph).ops[p.compareIndex]? =
      some (.binary (.cmp p.comparison.target) (.node p.compareIndex) (.node p.guardIndex.val) (.node right.val)) :=
  Proofs.guard_compare_computed p right selected

/-- The exit successor carries the selected old register or producer register. -/
theorem exit_operand {arity : Nat} (p : Plan arity) :
    (bankHeader p.graph).term.args[1]? = some (2, [register p.exitWire.address]) :=
  Proofs.exit_operand p

theorem native_step {arity : Nat} (p : Plan arity) (input old : WordTuple arity)
    (fr : Frame Reg) (agree : ArgsMatch fr (appendTuple old input)) :
    p.graph.step model input old =
      if p.guardWord old = 0 then .inl (p.exitValue old) else .inr (p.nextBank input old) :=
  Proofs.native_step p input old fr agree

theorem testFrame_args {arity : Nat} (p : Plan arity) (input old : WordTuple arity)
    (fr : Frame Reg) (agree : ArgsMatch fr (appendTuple old input)) :
    ArgsMatch (p.testFrame fr old) (appendTuple old input) :=
  Proofs.testFrame_args p input old fr agree

theorem header_activation_steps {arity : Nat} (p : Plan arity) (input old : WordTuple arity)
    (fr : Frame Reg) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    StepsNWithin (lowerBank p.graph) [] p.activationSteps ⟨⟨0, 1, 0⟩, fr, [], mem⟩ (p.successor input old fr mem) :=
  Proofs.header_activation_steps p input old fr mem agree

theorem header_activation {arity : Nat} (p : Plan arity) (input old : WordTuple arity)
    (fr : Frame Reg) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    Steps (lowerBank p.graph) ⟨⟨0, 1, 0⟩, fr, [], mem⟩ (p.successor input old fr mem) :=
  Proofs.header_activation p input old fr mem agree

/-- The actual RTL branch and typed λSSA header make the same decision.
Feedback binds the full old-bank row and exit observes the selected wire. -/
theorem activation_agrees {arity : Nat} (p : Plan arity) (input old : WordTuple arity)
    (fr : Frame Reg) (mem : Memory) (agree : ArgsMatch fr (appendTuple old input)) :
    let eval := Eval (instruction model) (extend (inputEnv model input) (encodeTuple model old))
      (Generic.header p.graph) mem
    Steps (lowerBank p.graph) ⟨⟨0, 1, 0⟩, fr, [], mem⟩ (p.successor input old fr mem) ∧
      if p.guardWord old = 0 then eval 1 (Generic.packResult model (out := word) (p.exitValue old)) mem
      else eval 0 (encodeTuple model (p.nextBank input old)) mem :=
  Proofs.activation_agrees p input old fr mem agree

/-- Read the whole feedback column through the same occurrence in any
predecessor order. -/
theorem feedback_slot_transfer_iff {arity : Nat} (p : Plan arity)
    (order : Fin 2 ≃ Generic.HeaderIncoming p.graph) (input old : WordTuple arity)
    {env : Env (Atom model)}
    (matched : let args := appendTuple old input
      LayoutMatch model (Generic.headerLayout p.graph) env args (p.graph.header.eval model args PUnit.unit))
    (start finish : Memory) (label : Nat) (payload : Value (Atom model)) :
    Eval (instruction model) (extend env .unit)
        (terminatorRegion (Generic.slotBranch p.graph order
          (order.symm (Generic.headerIncoming p.graph .backedge))))
        start label payload finish ↔
      label = 0 ∧ payload = encodeTuple model (p.nextBank input old) ∧ finish = start :=
  Proofs.feedback_slot_transfer_iff p order input old matched start finish label payload

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows
