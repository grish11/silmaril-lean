module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Fuel.Thms
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Institution.Thms
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Recognition

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Proofs

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

private theorem accepted_plan (accepted : lowerChecked g = some targets) :
    ∃ spec p, Rows.checkPlan arity spec = some p ∧ Rows.lowerChecked arity spec = some targets ∧
      ∃ eq : p.sigs = sigs, eq ▸ p.graph = g := by
  cases recognized : recognize g with
  | none => simp [lowerChecked, recognized] at accepted
  | some spec =>
    obtain ⟨p, checked, aligned⟩ := recognize_sound recognized
    exact ⟨spec, p, checked, by simpa only [lowerChecked, recognized, Option.bind_some] using accepted, aligned⟩

theorem lowerChecked_targets (accepted : lowerChecked g = some targets) :
    targets = (lowerBank g, Generic.lower g) := by
  obtain ⟨_, _, check, emitted, rfl, rfl⟩ := accepted_plan accepted
  obtain ⟨q, checked, _, same⟩ := (Rows.lowerChecked_eq_some_iff _ _ _).mp emitted
  cases Option.some.inj (checked.symm.trans check)
  exact same

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
        eval 0 (encodeTuple model next) memory := by
  obtain ⟨q, found, graph⟩ := recognize_sound recognized
  cases Option.some.inj (found.symm.trans checked)
  obtain ⟨rfl, rfl⟩ := graph
  have rtl := Rows.header_activation_steps p input old frame memory agree
  have typed := (Rows.activation_agrees p input old frame memory agree).2
  dsimp only
  rw [Rows.native_step p input old frame agree]
  by_cases exit : p.guardWord old = 0 <;>
    simpa only [exit, ite_true, ite_false, Plan.successor] using And.intro rtl typed

theorem rtl_return_iff (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (initial final : Memory) (returned : List Word) :
    targets.1.oracle 0 (words input) initial returned final ↔
      ∃ value : Word, g.Returns model input value ∧ returned = [value] ∧ final = initial := by
  obtain ⟨_, p, checked, emitted, rfl, rfl⟩ := accepted_plan accepted
  have reflect := Rows.rtl_return_iff checked emitted input initial final returned
  constructor
  · intro run
    obtain ⟨value, present, outputs, memory⟩ := reflect.mp run
    exact ⟨value, (p.graph.returns_iff_mem_denote model input value).mpr present, outputs, memory⟩
  · rintro ⟨value, source, outputs, memory⟩
    exact reflect.mpr ⟨value, (p.graph.returns_iff_mem_denote model input value).mp source, outputs, memory⟩

theorem lambda_return_iff (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (initial final : Memory) (label : Nat) (payload : Value (Atom model)) :
    Eval (instruction model) (inputEnv model input) targets.2 initial label payload final ↔
      ∃ value : Word, g.Returns model input value ∧ label = 0 ∧
        payload = Generic.packResult model (out := word) value ∧ final = initial := by
  obtain ⟨_, p, checked, emitted, rfl, rfl⟩ := accepted_plan accepted
  have reflect := Rows.lambda_return_iff checked emitted input initial final label payload
  constructor
  · intro run
    obtain ⟨value, present, exit, packet, memory⟩ := reflect.mp run
    exact ⟨value, (p.graph.returns_iff_mem_denote model input value).mpr present, exit, packet, memory⟩
  · rintro ⟨value, source, exit, packet, memory⟩
    exact reflect.mpr
      ⟨value, (p.graph.returns_iff_mem_denote model input value).mp source, exit, packet, memory⟩

theorem no_finite_return_iff (accepted : lowerChecked g = some targets) (input : WordTuple arity)
    (initial : Memory) :
    ((∀ returned final, ¬ targets.1.oracle 0 (words input) initial returned final) ↔
        g.denote model input = Part.none) ∧
    ((∀ label payload final, ¬ Eval (instruction model) (inputEnv model input)
        targets.2 initial label payload final) ↔ g.denote model input = Part.none) := by
  obtain ⟨_, _, checked, emitted, rfl, rfl⟩ := accepted_plan accepted
  exact Rows.no_finite_return_iff checked emitted input initial

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Proofs
