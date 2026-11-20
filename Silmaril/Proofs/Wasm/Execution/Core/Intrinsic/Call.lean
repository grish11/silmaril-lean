module

public import Silmaril.Wasm.Execution.Core.Intrinsic.Call.Defs
import Silmaril.Wasm.Execution.Core.Intrinsic.Thms
public import Silmaril.Wasm.Execution.Core.Instantiation

public section

namespace Silmaril.Proofs.Wasm.Execution.Core.Intrinsic.Call

open Silmaril.Wasm Silmaril.Wasm.Validation Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Execution.Core.Intrinsic Silmaril.Wasm.Numerics

variable {H : Type} {context : Context} {caller : World H context}
  {parameters results locals suffix : List IntType} {profile : Profile} {host : HostSemantics H}

private theorem erase_length (values : Values locals) : values.erase.length = locals.length := by
  induction values with
  | nil => rfl
  | cons _ _ ih => simp [Values.erase, ih]

private theorem erase_append (left : Values locals) (right : Values suffix) :
    (left.append right).erase = left.erase ++ right.erase := by
  induction left with
  | nil => rfl
  | cons _ _ ih => simp [Values.append, Values.erase, ih]

private theorem defaults (module_ : ModuleInst) (types : List IntType) :
    (Values.zeros types).erase.map some =
      (rawIntTypes types).map (fun kind => defaultVal? ((liftVal kind).substAll (module_.types.map .dt))) := by
  induction types with
  | nil => rfl
  | cons _ _ ih =>
    simp [Values.zeros, Values.erase, rawIntTypes, liftVal, Ty.substAll, defaultVal?, ih]
    rfl

private theorem enter (call : DirectCall caller parameters results) (outer : Frame)
    (args : Values parameters) :
    Step profile host
      ⟨caller.store, outer, vals args.erase ++ [.ref (.func call.address), .callRefType call.instance_.type]⟩
      (call.wrap outer (call.start args).erase) := by
  have argsLen : args.erase.length = (Ty.ofList (parameters.map fun kind => (.num (.int kind) : CValType))).length := by
    simp [Ty.length, erase_length]
  have resLen : (Ty.ofList (stackTypes results)).length = results.length := by
    simp [Ty.length, stackTypes]
  have frameEq : (call.start args).frame.erase =
      Frame.forCall call.instance_.module args.erase (rawIntTypes call.declaredLocals) := by
    simp [DirectCall.start, LocalFrame.erase, DirectCall.world, Frame.forCall, erase_append]
    exact defaults call.instance_.module call.declaredLocals
  have step := Step.callRefFunc (P := profile) (host := host) (f := outer) (vs := args.erase)
    (c := .callRefType call.instance_.type) trivial call.resolveAddress call.signature argsLen call.codeEq
  rw [resLen] at step
  change Step profile host _ ⟨caller.store, outer,
    [.frame results.length (call.start args).frame.erase [.label results.length [] (expression call.body.erase)]]⟩
  rw [frameEq]
  exact step

theorem entry (call : DirectCall caller parameters results) (frame : LocalFrame caller locals)
    (args : Values parameters) :
    Steps profile host (call.source frame args) (call.suspend frame (call.start args).erase) := by
  have first : Step profile host (call.source frame args)
      ⟨caller.store, frame.erase, vals args.erase ++ [.ref (.func call.address), .callRefType call.instance_.type]⟩ := by
    have atomic := Step.call (P := profile) (host := host) (f := frame.erase)
      call.resolveIndex call.resolveAddress
    cases args with
    | nil => exact atomic
    | cons bits tail =>
      simpa only [DirectCall.source, List.append_nil] using Step.ctxtInstrs
        (vs := (Values.cons bits tail).erase) (rest := []) atomic (Or.inl (by simp [Values.erase]))
  exact (Relation.ReflTransGen.single first).tail (enter call frame.erase args)

private theorem wrap_steps (call : DirectCall caller parameters results) (outer : Frame)
    {before after : Config H} (steps : Steps profile host before after) :
    Steps profile host (call.wrap outer before) (call.wrap outer after) := by
  apply Relation.ReflTransGen.lift (call.wrap outer) _ before after steps
  intro start finish step
  exact Step.ctxtFrame (Step.ctxtLabel step)

private theorem finish (call : DirectCall caller parameters results) (outer : Frame)
    (args : Values parameters) (fuel : Nat) {answer : Option (Values results)}
    (returned : call.runFor args fuel = some answer) :
    Steps profile host (call.wrap outer (call.start args).erase)
      ⟨caller.store, outer, (match answer with
        | some values => vals values.erase.reverse
        | none => [.trap])⟩ := by
  let active := (call.start args).runFor fuel
  have run : Steps profile host (call.wrap outer (call.start args).erase) (call.wrap outer active.erase) :=
    wrap_steps call outer (State.runFor_sound fuel (call.start args))
  have shrink (result : Result) (found : active.result? = some result) : active.erase.code = result.toAdmin :=
    (State.result_sound (profile := profile) found).1
  have found : active.result? = some (match answer with
      | none => Result.trap | some values => .values values.erase.reverse) := by
    unfold State.result?
    rw [show active.control.result? = some answer from returned]
    cases answer <;> rfl
  cases answer with
  | none =>
    have term := shrink .trap found
    have exit₁ : Step profile host (call.wrap outer active.erase)
        ⟨caller.store, outer, [.frame results.length active.frame.erase [.trap]]⟩ := by
      change Step profile host ⟨caller.store, outer,
        [.frame results.length active.frame.erase [.label results.length [] active.erase.code]]⟩ _
      rw [term]
      exact .ctxtFrame .trapLabel
    exact (run.tail exit₁).tail .trapFrame
  | some values =>
    have term := shrink (.values values.erase.reverse) found
    have exit₁ : Step profile host (call.wrap outer active.erase)
        ⟨caller.store, outer, [.frame results.length active.frame.erase (vals values.erase.reverse)]⟩ := by
      change Step profile host ⟨caller.store, outer,
        [.frame results.length active.frame.erase [.label results.length [] active.erase.code]]⟩ _
      rw [term]
      exact .ctxtFrame .labelVals
    exact (run.tail exit₁).tail (.frameVals (by simp [erase_length]))

theorem run_sound (call : DirectCall caller parameters results) (frame : LocalFrame caller locals)
    (args : Values parameters) (fuel : Nat) {answer : Option (Values results)}
    (returned : call.runFor args fuel = some answer) :
    Steps profile host (call.source frame args)
      ⟨caller.store, frame.erase, (match answer with
        | some values => vals values.erase.reverse
        | none => [.trap])⟩ :=
  (entry call frame args).trans (finish call frame.erase args fuel returned)

theorem invoke_sound (call : DirectCall caller parameters results) (args : Values parameters)
    (fuel : Nat) {answer : Option (Values results)} (returned : call.runFor args fuel = some answer) :
    Steps profile host (invoke caller.store call.address args.erase)
      ⟨caller.store, {}, (match answer with
        | some values => vals values.erase.reverse
        | none => [.trap])⟩ := by
  have entered : Step profile host (invoke caller.store call.address args.erase)
      (call.wrap {} (call.start args).erase) := by
    unfold invoke
    rw [call.resolveAddress]
    exact enter call {} args
  exact (Relation.ReflTransGen.single entered).trans (finish call {} args fuel returned)

end Silmaril.Proofs.Wasm.Execution.Core.Intrinsic.Call
