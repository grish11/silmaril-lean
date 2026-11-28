module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Phi.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Thms
public import Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA.Generic.Reindex.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Checked.Phi.Agreement

/-! # Exact guard, edge occurrence and finite-return agreement -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Phi

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (StepsNWithin)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (Reg entry inputs model word)
open Silmaril.SSA
open Silmaril.SSA.SeaOfNodes.Loop (Incoming appendTuple)
open Silmaril.SSA.SeaOfNodes.Diamond (Val)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA
  (Atom LayoutMatch inputEnv instruction terminatorRegion)
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics (Env extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

theorem lowerChecked_eq_some_iff (g : WordLoop) (targets : Targets) :
    lowerChecked g = some targets ↔ Checked.lower g = some targets.1 ∧ targets.2 = Generic.lower g :=
  Proofs.lowerChecked_eq_some_iff g targets

theorem lowerChecked_typed {g : WordLoop} {targets : Targets} (ok : lowerChecked g = some targets) :
    targets.1.WellFormed ∧ targets.2.HasType (Generic.inputContext inputs) [Generic.packed [.value word]] := by
  obtain ⟨machine, ssa⟩ := (lowerChecked_eq_some_iff g targets).mp ok
  exact ⟨Checked.lower_wellFormed machine, ssa.symm ▸ Generic.lower_hasType g⟩

/-- Corresponding actual successor occurrences, with RTL's own branch
ordinal and either positional order of the explicit φ table. -/
theorem incoming_alignment (p : Profile) (order : Fin 2 ≃ Generic.HeaderIncoming p.graph)
    (arrival : Incoming) :
    ((p.lowerFunc.block? (incomingSlot arrival).1).bind
      fun block => block.term.args[(incomingSlot arrival).2]?) = some (1, [p.incomingRegister arrival]) ∧
    Generic.slotBranch p.graph order (order.symm (Generic.headerIncoming p.graph arrival)) =
      .br 0 (Generic.edge p.graph arrival).argument :=
  ⟨p.incoming_operand arrival, Generic.slot_branch_roundtrip p.graph order (Generic.headerIncoming p.graph arrival)⟩

/-- Both actual headers select the same runtime branch. The taken edge
carries the whole next word tuple, and the exit carries the old word. -/
theorem activation_agrees (p : Profile) (seed delta old : Word) (fr : Frame Reg) (mem : Memory)
    (hold : fr.get .phi = some old) (hdelta : fr.get (.arg 1) = some delta) :
    let after := p.headerFrame fr old delta
    let halt := p.guardWord old delta = 0
    let next := p.update.eval old delta
    let eval := Eval (instruction model)
      (extend (inputEnv model (entry seed delta)) (Generic.packResult model (out := word) old))
      (Generic.header p.graph) mem
    StepsNWithin p.lower [] 4 ⟨⟨0, 1, 0⟩, fr, [], mem⟩
      (if halt then ⟨⟨0, 2, 0⟩, after.set (.node 3) old, [], mem⟩
       else ⟨⟨0, 1, 0⟩, after.set .phi next, [], mem⟩) ∧
    (if halt then eval 1 (Generic.packResult model (out := word) old) mem
     else eval 0 (Generic.packResult model (out := word) next) mem) :=
  Proofs.activation_agrees p seed delta old fr mem hold hdelta

/-- Either positional order recovers the actual preheader jump and its
full initial packet. -/
theorem entry_slot_transfer_iff (p : Profile) (order : Fin 2 ≃ Generic.HeaderIncoming p.graph)
    (seed delta : Word) (start finish : Memory) (label : Nat) (payload : Value (Atom model)) :
    Eval (instruction model) (inputEnv model (entry seed delta))
        (terminatorRegion (Generic.slotBranch p.graph order (order.symm (Generic.headerIncoming p.graph .entry))))
        start label payload finish ↔
      label = 0 ∧ payload = Generic.packResult model (out := word) seed ∧ finish = start :=
  Proofs.entry_slot_transfer_iff p order seed delta start finish label payload

/-- The backedge slot reads the newly computed word from the scheduled old
activation before the carried parameter is rebound. -/
theorem feedback_slot_transfer_iff (p : Profile) (order : Fin 2 ≃ Generic.HeaderIncoming p.graph)
    (seed delta old : Word) {env : Env (Atom model)}
    (matched : let args := appendTuple (.cons (F := Val model.value) (t := .value word) old .nil) (entry seed delta)
      LayoutMatch model (Generic.headerLayout p.graph) env args
        (p.graph.header.eval model args PUnit.unit))
    (start finish : Memory) (label : Nat) (payload : Value (Atom model)) :
    Eval (instruction model) (extend env .unit)
        (terminatorRegion (Generic.slotBranch p.graph order (order.symm (Generic.headerIncoming p.graph .backedge))))
        start label payload finish ↔
      label = 0 ∧ payload = Generic.packResult model (out := word) (p.update.eval old delta) ∧ finish = start :=
  Proofs.feedback_slot_transfer_iff p order seed delta old matched start finish label payload

/-- The two accepted targets have the same finite word and whole-memory
observations. The source adequacy laws force final memory to equal initial. -/
theorem returns_iff {g : WordLoop} {targets : Targets}
    (accepted : lowerChecked g = some targets)
    (seed delta : Word) (initial final : Memory) (returned : List Word) :
    targets.1.oracle 0 [seed, delta] initial returned final ↔
      ∃ value : Word, returned = [value] ∧
        Eval (instruction model) (inputEnv model (entry seed delta)) targets.2
          initial 0 (Generic.packResult model (out := word) value) final :=
  Proofs.returns_iff accepted seed delta initial final returned

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Checked.Phi
