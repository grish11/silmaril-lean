module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Consumer
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Invariant
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call (ClosureAt)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named (runs_at)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Outcome)
open Silmaril.Languages.Starlark.Modules.Loader (Session)

local notation "Value" => Lists.Value

private theorem copy_record {importName globals program env} {state middle : State} {source : Lowering.Resolve.SourceExpr}
    {rhs : Lowering.Expr} {value : Value} (copy : Copy importName source rhs)
    (evaluated : Body.Evaluates (block importName globals) state source rhs (.ok value middle))
    (live : Live importName program env state) :
    ∀ callee, copy.track env = some callee → ∃ address defining, value = .function address ∧
      callee.Linked program ∧ Nonempty (ClosureAt callee.site callee.id defining middle address) := by
  intro callee tracked
  cases copy with
  | forget => cases tracked
  | name name =>
    obtain ⟨address, defining, loaded, linked, record⟩ := read_live live tracked
    generalize outcome : (EStateM.Result.ok value middle : Outcome Value) = result at evaluated
    cases evaluated with
    | read resolution =>
      rw [State.read, loaded] at outcome
      cases outcome
      exact ⟨address, defining, rfl, linked, record⟩

private theorem assigned_step {program : Program} {manifest : Modules.Loader.Manifest} {active : List Nat}
    {s : Session} {id : Nat} {name : String} {code : Lowering.Expr} {out : Outcome Value}
    (exec : ExecExpr program (List.range program.size) s.runtime code out) :
    Modules.Loader.Runs program manifest active (.command id (.exec (.assignExpr name code))) s
      (Modules.Loader.liftResult id s (afterWrite name out)) := by
  cases out <;> exact .exec (code := .assignExpr name code) (.assignExpr exec)

theorem run_suite {source : List Modules.Resolve.Command} {seed : Program} {resolved : ResolvedModule}
    (checked : resolve source seed = .ok resolved)
    {manifest : Modules.Loader.Manifest} {active : List Nat} {id : Nat}
    {importName : String} {globals : List String} (separate : importName ∉ globals)
    (steps : List (Step importName globals)) {env : Environment} (admitted : ReadyFor env steps)
    (session : Session) (frame : Frame importName globals session.runtime)
    (live : Live importName resolved.program env session.runtime) :
    ∃ out, SuiteRuns session.runtime steps out ∧
      Modules.Loader.Runs resolved.program manifest active (.commands id (steps.map Step.code)) session
        (Modules.Loader.liftResult id session out) ∧
      ∀ reached, out = .ok () reached →
        Frame importName globals reached ∧ Live importName resolved.program (steps.foldl Step.advance env) reached := by
  induction steps generalizing env session with
  | nil => exact ⟨_, .done _, .done, fun _ same => by cases same; exact ⟨frame, live⟩⟩
  | cons head tail ih =>
    cases head with
    | @assign name declared source rhs reads operand copy =>
      have next : ReadyFor (update env name (copy.track env)) tail := admitted
      obtain ⟨result, ran, kept⟩ := Body.operand_total operand session.runtime
      have native : ExecExpr resolved.program (List.range resolved.program.size) session.runtime rhs result :=
        .evaluates (calls := fun _ _ _ => False) (fun _ _ _ no => no.elim)
          (Body.evaluates_with _ _ _ ran)
      have step := assigned_step (manifest := manifest) (active := active) (id := id) (name := name) native
      cases result with
      | error => exact ⟨_, .failed (.assign ran), .failed step, fun _ impossible => nomatch impossible⟩
      | ok value middle =>
        have arrived := keeps_frame frame kept
        have written := writes_frame arrived (globalSlot name) value
        have reached := writes_live arrived (keeps_live live kept) declared
          (fun same => separate (same ▸ declared)) value _ (copy_record copy ran live)
        obtain ⟨out, trace, nativeTail, finished⟩ :=
          ih next {session with runtime := middle.write (globalSlot name) value} written reached
        exact ⟨out, .next (.assign ran) trace, .step step nativeTail, finished⟩
    | invoke call =>
      obtain ⟨callee, tracked, remaining⟩ := admitted
      have next : ReadyFor (update env call.destination (callee.returned.map Callable.nested)) tail := by
        simpa [Step.advance, tracked] using remaining
      obtain ⟨address, defining, loaded, linked, ⟨record⟩⟩ := read_live live tracked
      have read := Body.Evaluates.read (state := session.runtime) (read_resolves call.declared).1
      change Body.Evaluates _ _ _ _ (session.runtime.read (.bound (readSlot importName call.callee))) at read
      rw [State.read, loaded] at read
      have permitted : callee.id ∈ List.range resolved.program.size :=
        List.mem_range.mpr (Array.getElem?_eq_some_iff.mp linked.1).choose
      obtain ⟨result, ran, native, _, kept⟩ :=
        runs_at callee.site callee.BodyRuns checked callee.id linked.1 _ permitted
          (enter_callable checked linked) (readSlot importName call.callee) read record
          call.operands call.keywords call.star call.mapping
      have step := assigned_step (manifest := manifest) (active := active) (id := id)
        (name := call.destination) (code := call.code) native
      cases result with
      | error => exact ⟨_, .failed (.invoke callee ran), .failed step, fun _ impossible => nomatch impossible⟩
      | ok value returned =>
        have arrived := keeps_frame frame kept
        have written := writes_frame arrived (globalSlot call.destination) value
        have records (child : Callable) (chosen : callee.returned.map Callable.nested = some child) :
            ∃ address defining, value = .function address ∧ child.Linked resolved.program ∧
              Nonempty (ClosureAt child.site child.id defining returned address) := by
          obtain ⟨address, defining, saved, closure⟩ := returned_record ran child chosen
          exact ⟨address, defining, saved, returned_linked linked child chosen, closure⟩
        have reached := writes_live arrived (keeps_live live kept) call.destinationGlobal
          (fun same => separate (same ▸ call.destinationGlobal)) value _ records
        obtain ⟨out, trace, nativeTail, finished⟩ :=
          ih next {session with runtime := returned.write (globalSlot call.destination) value} written reached
        refine ⟨out, .next (.invoke callee ran) trace, .step step nativeTail, ?_⟩
        simpa [Step.advance, tracked] using finished

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
