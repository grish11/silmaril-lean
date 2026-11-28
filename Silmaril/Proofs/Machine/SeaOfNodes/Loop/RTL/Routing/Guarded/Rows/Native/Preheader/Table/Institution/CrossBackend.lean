module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Defs
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Room
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.RTLBehavior

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Proofs

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL.SSA (Behavior)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy model word)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA (Atom encode_injective)
open Silmaril.SSA.SeaOfNodes.Diamond.LambdaSSA.Institution.Fiber (inputModel)
open Silmaril.SSA.SeaOfNodes.Loop.LambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.Institution.Observational (Observation ssaBeh)

variable {arity : Nat} {entrySigs sigs : List (List PortTy)}
variable {left : SourceWithEntry arity entrySigs sigs} {leftTargets : Checked.Phi.Targets}

private theorem singleton_rtl_iff (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity) (initial final : Memory) (value : Word) :
    Behavior.returned [value] final ∈ rtlBehaviors input initial leftTargets.1 ↔
      value ∈ left.denote model input ∧ final = initial := by
  refine (rtl_behavior_iff accepted input initial (.returned [value] final)).trans ?_
  constructor
  · rintro ⟨actual, present, outputs, state⟩
    cases List.singleton_inj.mp outputs
    exact ⟨present, state⟩
  · rintro ⟨present, state⟩
    exact ⟨value, present, rfl, state⟩

theorem rtl_room_observation_iff (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity)
    (observation : Silmaril.Isotope.Institution.Observational.Observation (Nat × Value (Atom model)) Memory) :
    observation ∈ ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory input) (scope accepted) ↔
    observation.Holds
      (fun initial (label, payload) final => ∃ value : Word,
        label = 0 ∧ payload = Generic.packResult model (out := word) value ∧ final = initial ∧
          Behavior.returned [value] final ∈ rtlBehaviors input initial leftTargets.1)
      (fun _ _ => False)
      (fun initial => Behavior.diverges ∈ rtlBehaviors input initial leftTargets.1) := by
  cases observation with
  | ret initial result final =>
    obtain ⟨label, payload⟩ := result
    refine (room_ret_iff accepted input initial final label payload).trans ?_
    simp only [Observation.Holds, singleton_rtl_iff accepted]
    exact exists_congr fun _ =>
      ⟨fun ⟨present, exit, packet, heap⟩ => ⟨exit, packet, heap, present, heap⟩,
        fun ⟨exit, packet, heap, present, _⟩ => ⟨present, exit, packet, heap⟩⟩
  | fault initial final => exact iff_false_intro (room_fault_absent accepted input initial final)
  | diverge initial =>
    exact (room_diverges_iff accepted input initial).trans (rtl_divOracle_iff accepted input initial).symm

theorem rtl_room_return_iff (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity) (initial final : Memory) (value : Word) :
    Behavior.returned [value] final ∈ rtlBehaviors input initial leftTargets.1 ↔
      Observation.ret initial (0, Generic.packResult model (out := word) value) final ∈
        ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory input) (scope accepted) := by
  refine (singleton_rtl_iff accepted input initial final value).trans ?_
  constructor
  · rintro ⟨present, state⟩
    exact (room_ret_iff accepted input initial final 0 _).mpr ⟨value, present, rfl, rfl, state⟩
  · intro returned
    obtain ⟨actual, present, _, payload, state⟩ := (room_ret_iff accepted input initial final 0 _).mp returned
    have same : value = actual := encode_injective model (Value.pair.inj payload).1
    exact ⟨same.symm ▸ present, state⟩

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Proofs
