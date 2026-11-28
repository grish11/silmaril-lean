module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Institution.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Execution
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Recognition

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.RTL.SSA (StepsNWithin)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model word)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (Atom encodeTuple inputEnv instruction)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.LambdaSSA.Semantics (extend)
open Silmaril.Isotope.LambdaSSA.Semantics.Region (Eval)

variable {arity : Nat} {sigs : List (List PortTy)}
variable {g : BankGraph arity sigs} {spec : Spec} {p : Plan arity} {targets : Checked.Phi.Targets}

/-- The checked schedule reconstructs all typed source wires and operations. -/
theorem recognize_sound (recognized : recognize g = some spec) :
    ∃ p, Rows.checkPlan arity spec = some p ∧ ∃ eq : p.sigs = sigs, eq ▸ p.graph = g :=
  Proofs.recognize_sound recognized

/-- Both checked targets are the ordinary emissions of the source graph. -/
theorem lowerChecked_targets (accepted : lowerChecked g = some targets) :
    targets = (lowerBank g, Generic.lower g) :=
  Proofs.lowerChecked_targets accepted

/-- The actual machine branch and λSSA header consume the packet selected
by the native activation. The whole memory passes through either branch. -/
theorem activation_agrees
    (recognized : recognize g = some spec) (checked : Rows.checkPlan arity spec = some p)
    (input old : WordTuple arity) (frame : Frame Reg) (memory : Memory)
    (agree : ArgsMatch frame (appendTuple old input)) :
    let eval := Eval (instruction model) (extend (inputEnv model input) (encodeTuple model old))
      (Generic.header g) memory
    let after := p.testFrame frame old
    match g.step model input old with
    | .inl result =>
      StepsNWithin (lowerBank g) [] p.activationSteps ⟨⟨0, 1, 0⟩, frame, [], memory⟩
          ⟨⟨0, 2, 0⟩, after.set .phi result, [], memory⟩ ∧
        eval 1 (Generic.packResult model (out := word) result) memory
    | .inr next =>
      StepsNWithin (lowerBank g) [] p.activationSteps ⟨⟨0, 1, 0⟩, frame, [], memory⟩
          ⟨⟨0, 1, 0⟩, bindWords arity after next, [], memory⟩ ∧
        eval 0 (encodeTuple model next) memory :=
  Proofs.activation_agrees recognized checked input old frame memory agree

/-- Every finite RTL return has the native returned word and the full initial memory. -/
theorem rtl_return_iff (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (initial final : Memory) (returned : List Word) :
    targets.1.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, g.Returns model input value ∧ returned = [value] ∧ final = initial :=
  Proofs.rtl_return_iff accepted input initial final returned

/-- Every finite λSSA CFG return packs the native returned word and preserves memory. -/
theorem lambda_return_iff (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (initial final : Memory) (label : Nat) (payload : Value (Atom model)) :
    Eval (instruction model) (inputEnv model input) targets.2 initial label payload final ↔
      ∃ value : Word, g.Returns model input value ∧ label = 0 ∧
        payload = Generic.packResult model (out := word) value ∧ final = initial :=
  Proofs.lambda_return_iff accepted input initial final label payload

/-- Native undefinedness rules out finite returns in both targets, without a fuel bound. -/
theorem no_finite_return_iff (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (initial : Memory) :
    ((∀ returned final, ¬ targets.1.oracle 0 (words input) initial returned final) ↔
        g.denote model input = Part.none) ∧
    ((∀ label payload final, ¬ Eval (instruction model) (inputEnv model input)
        targets.2 initial label payload final) ↔ g.denote model input = Part.none) :=
  Proofs.no_finite_return_iff accepted input initial

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native
