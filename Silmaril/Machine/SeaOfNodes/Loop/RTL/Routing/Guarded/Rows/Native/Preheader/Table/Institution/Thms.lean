module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Defs
public import Silmaril.Logic.Institution.Observational.Sentence
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Satisfaction
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.Room
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.RTLBehavior
import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution.CrossBackend

/-! Satisfaction for RTL.SSA behaviours and the λSSA room in the concrete word model. -/

public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution

open CategoryTheory (Discrete)
open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL.SSA (Behavior)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy model word)
open Silmaril.SSA.SeaOfNodes
open Diamond.LambdaSSA (Atom)
open Diamond.LambdaSSA.Institution.Fiber (fiberRoom inputModel)
open Loop.LambdaSSA
open Silmaril.Isotope (Value)
open Silmaril.Isotope.Institution.Observational (Observation ssaBeh)
open Silmaril.Logic.Institution.Observational (Sentence)

variable {arity : Nat} {entrySigs sigs rightEntry rightSigs : List (List PortTy)}
variable {left : SourceWithEntry arity entrySigs sigs} {right : SourceWithEntry arity rightEntry rightSigs}
variable {leftTargets rightTargets : Checked.Phi.Targets}

/-- The room's return projection is the existing guarded-row λSSA observation. -/
theorem lambdaReturns_eq (input : WordTuple arity) (initial : Memory) (region : LambdaScope arity) :
    lambdaReturns input initial region = Rows.lambdaObservation region.val input initial :=
  Proofs.lambdaReturns_eq input initial region

/-- The target return sets contain exactly their native partial observation with full memory. -/
theorem observations_eq (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity) (initial : Memory) :
    Rows.rtlObservation leftTargets.1 input initial = {result | result ∈ nativeDenote left input initial} ∧
      lambdaReturns input initial (scope accepted) = {result | result ∈ nativeDenote left input initial} :=
  Proofs.observations_eq accepted input initial

/-- At a shared input and initial memory, both emitted observation equations
and the cross-backend comparison reflect native partial equality. -/
theorem equation_at_iff (leftChecked : lowerChecked left = some leftTargets)
    (rightChecked : lowerChecked right = some rightTargets)
    (input : WordTuple arity) (initial : Memory) :
    let native := left.denote model input = right.denote model input
    ((Sentence.eq leftTargets.1 rightTargets.1).Holds (fun target => Rows.rtlObservation target input initial)
        ↔ native) ∧
      ((Sentence.eq (scope leftChecked) (scope rightChecked)).Holds (lambdaReturns input initial) ↔ native) ∧
      (Rows.rtlObservation leftTargets.1 input initial = lambdaReturns input initial (scope rightChecked) ↔ native) :=
  Proofs.equation_at_iff leftChecked rightChecked input initial

/-- Native equation satisfaction is exactly satisfaction of each emitted
return-observation equation at all typed inputs, for any fixed initial memory. -/
theorem equation_holds_iff (leftChecked : lowerChecked left = some leftTargets)
    (rightChecked : lowerChecked right = some rightTargets) (initial : Memory) :
    let native := (Loop.Institution.Sentence.equation (equation left right)).Holds model
    ((∀ input : WordTuple arity, (Sentence.eq leftTargets.1 rightTargets.1).Holds
        (fun target => Rows.rtlObservation target input initial)) ↔ native) ∧
      ((∀ input : WordTuple arity, (Sentence.eq (scope leftChecked) (scope rightChecked)).Holds
        (lambdaReturns input initial)) ↔ native) ∧
      ((∀ input : WordTuple arity, Rows.rtlObservation leftTargets.1 input initial =
        lambdaReturns input initial (scope rightChecked)) ↔ native) :=
  Proofs.equation_holds_iff leftChecked rightChecked initial

/-- The native termination sentence holds exactly when each typed input
has a finite return on the corresponding emitted target. -/
theorem terminates_holds_iff (accepted : lowerChecked left = some leftTargets) (initial : Memory) :
    let native := (Loop.Institution.Sentence.terminates (program left)).Holds model
    ((∀ input : WordTuple arity, (Rows.rtlObservation leftTargets.1 input initial).Nonempty) ↔ native) ∧
      ((∀ input : WordTuple arity, (lambdaReturns input initial (scope accepted)).Nonempty) ↔ native) :=
  Proofs.terminates_holds_iff accepted initial

/-- Every room return exits at zero, packs a native word, and preserves all memory. -/
theorem room_ret_iff (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity) (initial final : Memory) (label : Nat) (payload : Value (Atom model)) :
    Observation.ret initial (label, payload) final ∈
      ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory input) (scope accepted) ↔
    ∃ value : Word, value ∈ left.denote model input ∧ label = 0 ∧
      payload = Generic.packResult model (out := word) value ∧ final = initial :=
  Proofs.room_ret_iff accepted input initial final label payload

/-- Internal header labels cannot escape as observable exits. -/
theorem room_other_exit_absent (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity) (initial final : Memory) (label : Nat) (payload : Value (Atom model))
    (unexpected : label ≠ 0) :
    Observation.ret initial (label, payload) final ∉
      ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory input) (scope accepted) :=
  fun member => unexpected ((room_ret_iff accepted input initial final label payload).mp member).choose_spec.2.1

/-- The concrete word model has no primitive fault, hence no region fault. -/
theorem room_fault_absent (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity) (initial final : Memory) :
    Observation.fault initial final ∉
      ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory input) (scope accepted) :=
  Proofs.room_fault_absent accepted input initial final

/-- With no finite native return, the actual header keeps taking backedges.
A finite return excludes divergence by determinism. -/
theorem room_diverges_iff (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity) (initial : Memory) :
    Observation.diverge initial ∈
      ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory input) (scope accepted) ↔
    left.denote model input = Part.none :=
  Proofs.room_diverges_iff accepted input initial

/-- The actual room compares returns, faults and divergence over all memories
at the given typed input. One initial memory suffices to reflect equality. -/
theorem room_equation_at_iff (leftChecked : lowerChecked left = some leftTargets)
    (rightChecked : lowerChecked right = some rightTargets) (input : WordTuple arity) (initial : Memory) :
    (fiberRoom Rows.wordSignature (wordSorts arity).length).Sat
      (Discrete.mk (inputModel (P := Rows.wordSignature) model Memory input))
      (Sentence.eq (scope leftChecked) (scope rightChecked)) ↔ left.denote model input = right.denote model input :=
  Proofs.room_equation_at_iff leftChecked rightChecked input initial

/-- Native equation satisfaction agrees with full λSSA room satisfaction
in the family of concrete models induced by all typed inputs. -/
theorem room_equation_holds_iff (leftChecked : lowerChecked left = some leftTargets)
    (rightChecked : lowerChecked right = some rightTargets) (initial : Memory) :
    (∀ input : WordTuple arity, (fiberRoom Rows.wordSignature (wordSorts arity).length).Sat
      (Discrete.mk (inputModel (P := Rows.wordSignature) model Memory input))
      (Sentence.eq (scope leftChecked) (scope rightChecked))) ↔
    (Loop.Institution.Sentence.equation (equation left right)).Holds model :=
  forall_congr' fun input => room_equation_at_iff leftChecked rightChecked input initial

/-- Function zero has a valid initial machine state at every typed input. -/
theorem rtl_start_exists (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity) (initial : Memory) :
    ∃ start, leftTargets.1.start 0 (words input) initial = some start :=
  Proofs.rtl_start_exists accepted input initial

/-- Native undefinedness corresponds to an infinite sequence of RTL instructions. -/
theorem rtl_divOracle_iff (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity) (initial : Memory) :
    leftTargets.1.divOracle 0 (words input) initial ↔ left.denote model input = Part.none :=
  Proofs.rtl_divOracle_iff accepted input initial

/-- Every actual RTL behaviour either returns exactly one native word with the
whole initial memory or diverges when the native denotation is undefined. -/
theorem rtl_behavior_iff (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity) (initial : Memory) (outcome : Behavior) :
    outcome ∈ rtlBehaviors input initial leftTargets.1 ↔
      match outcome with
      | .returned values final =>
        ∃ value : Word, value ∈ left.denote model input ∧ values = [value] ∧ final = initial
      | .diverges => left.denote model input = Part.none
      | .trapped _ | .stuck => False :=
  Proofs.rtl_behavior_iff accepted input initial outcome

/-- No execution from a typed start gets stuck or reaches a trap. -/
theorem rtl_no_fault (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity) (initial : Memory) :
    Behavior.stuck ∉ rtlBehaviors input initial leftTargets.1 ∧
      ∀ final, Behavior.trapped final ∉ rtlBehaviors input initial leftTargets.1 :=
  ⟨(rtl_behavior_iff accepted input initial .stuck).mp,
    fun final => (rtl_behavior_iff accepted input initial (.trapped final)).mp⟩

/-- A full RTL equation at one typed input and initial memory holds exactly
when the native partial denotations agree at that input. -/
theorem rtl_equation_at_iff (leftChecked : lowerChecked left = some leftTargets)
    (rightChecked : lowerChecked right = some rightTargets) (input : WordTuple arity) (initial : Memory) :
    (Sentence.eq leftTargets.1 rightTargets.1).Holds (rtlBehaviors input initial) ↔
      left.denote model input = right.denote model input :=
  Proofs.rtl_equation_at_iff leftChecked rightChecked input initial

/-- Native equation satisfaction agrees with full RTL equations at all
typed inputs, for any common initial memory. -/
theorem rtl_equation_holds_iff (leftChecked : lowerChecked left = some leftTargets)
    (rightChecked : lowerChecked right = some rightTargets) (initial : Memory) :
    (∀ input : WordTuple arity, (Sentence.eq leftTargets.1 rightTargets.1).Holds (rtlBehaviors input initial)) ↔
      (Loop.Institution.Sentence.equation (equation left right)).Holds model :=
  forall_congr' fun input => rtl_equation_at_iff leftChecked rightChecked input initial

/-- Compare a room observation with actual RTL outcomes at the initial memory
recorded by that observation. Returns agree on the word and the whole memory. -/
theorem rtl_room_observation_iff (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity)
    (observation : Silmaril.Isotope.Institution.Observational.Observation (Nat × Value (Atom model)) Memory) :
    observation ∈ ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory input) (scope accepted) ↔
    observation.Holds
      (fun initial (label, payload) final => ∃ value : Word,
        label = 0 ∧ payload = Generic.packResult model (out := word) value ∧ final = initial ∧
          Behavior.returned [value] final ∈ rtlBehaviors input initial leftTargets.1)
      (fun _ _ => False)
      (fun initial => Behavior.diverges ∈ rtlBehaviors input initial leftTargets.1) :=
  Proofs.rtl_room_observation_iff accepted input observation

/-- Query both emitted programs for an exact word and final memory. -/
theorem rtl_room_return_iff (accepted : lowerChecked left = some leftTargets)
    (input : WordTuple arity) (initial final : Memory) (value : Word) :
    Behavior.returned [value] final ∈ rtlBehaviors input initial leftTargets.1 ↔
      Observation.ret initial (0, Generic.packResult model (out := word) value) final ∈
        ssaBeh 1 (inputModel (P := Rows.wordSignature) model Memory input) (scope accepted) :=
  Proofs.rtl_room_return_iff accepted input initial final value

/-- At one typed input, the RTL equation at any common initial memory reflects
the full λSSA room equation, which quantifies over all memories. -/
theorem rtl_room_equation_at_iff (leftChecked : lowerChecked left = some leftTargets)
    (rightChecked : lowerChecked right = some rightTargets) (input : WordTuple arity) (initial : Memory) :
    (Sentence.eq leftTargets.1 rightTargets.1).Holds (rtlBehaviors input initial) ↔
    (fiberRoom Rows.wordSignature (wordSorts arity).length).Sat
      (Discrete.mk (inputModel (P := Rows.wordSignature) model Memory input))
      (Sentence.eq (scope leftChecked) (scope rightChecked)) :=
  (rtl_equation_at_iff leftChecked rightChecked input initial).trans
    (room_equation_at_iff leftChecked rightChecked input initial).symm

/-- The same checked equation holds at all typed inputs in RTL exactly when
it holds in the corresponding family of concrete λSSA room models. -/
theorem rtl_room_equation_holds_iff (leftChecked : lowerChecked left = some leftTargets)
    (rightChecked : lowerChecked right = some rightTargets) (initial : Memory) :
    (∀ input : WordTuple arity, (Sentence.eq leftTargets.1 rightTargets.1).Holds (rtlBehaviors input initial)) ↔
    (∀ input : WordTuple arity, (fiberRoom Rows.wordSignature (wordSorts arity).length).Sat
      (Discrete.mk (inputModel (P := Rows.wordSignature) model Memory input))
      (Sentence.eq (scope leftChecked) (scope rightChecked))) :=
  forall_congr' fun input => rtl_room_equation_at_iff leftChecked rightChecked input initial

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Institution
