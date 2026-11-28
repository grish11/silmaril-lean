module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Defs
public import Silmaril.Languages.Starlark.Modules.Operational.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (globalSlot validateSource)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Functions (Program)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Lists (State)
open Silmaril.Languages.Starlark.Modules.Loader (Session)

theorem revalidate {producer consumer : Modules.Source} {earlier later : Program}
    (old : validateSource earlier producer = .ok ())
    (new : validateSource later consumer = .ok ()) :
    validateSource later producer = .ok () := by
  unfold validateSource at old new ⊢
  split at old
  · cases old
  · split at new
    · cases new
    · generalize h₁ : Functions.validate earlier (.total (.atomic .pass)) = x at old
      generalize h₂ : Functions.validate later (.total (.atomic .pass)) = y at new ⊢
      cases x with
      | error => cases old
      | ok result =>
        cases result
        cases y with
        | error => cases new
        | ok result => cases result; exact old

theorem observed_eq (id : Nat) (source : Modules.Source) (caller : State)
    (before : Session) (out : Modules.Result Unit) :
    observed id source caller before.cache out = Modules.Loader.finish id source caller (Modules.Loader.liftResult id before out) := by
  cases out with
  | error => rfl
  | ok value _ => cases value; rfl

theorem plan_executable {globals : List String} {env exports : Environment}
    {source : List Modules.Resolve.Command} {code : List Modules.Command} {linked final : Program}
    (profile : Plan globals env source linked code final exports) :
    ∀ command ∈ code, ∃ top, command = .exec top := by
  induction profile <;> intro command member
  · cases member
  all_goals
    rcases List.mem_cons.mp member with same | rest
    · exact ⟨_, same⟩
    · exact ‹∀ item ∈ _, ∃ top, item = Modules.Command.exec top› _ rest

private theorem loader_command {program : Program} {manifest : Modules.Loader.Manifest} {active : List Nat}
    {id : Nat} {state : State} {host : Modules.Catalog} {code : Modules.TopCode}
    {out : Modules.Result Unit} (native : Modules.Executes program host state (.exec code) out)
    (cache : List (Nat × Modules.Published)) :
    Modules.Loader.Runs program manifest active (.command id (.exec code)) ⟨state, cache⟩
      (Modules.Loader.liftResult id ⟨state, cache⟩ out) := by
  cases native with
  | exec ran => exact .exec ran

theorem loader_exec {program : Program} {manifest : Modules.Loader.Manifest} {active : List Nat}
    {id : Nat} {state : State} {host : Modules.Catalog} {code : List Modules.Command}
    {out : Modules.Result Unit} (native : Modules.Runs program host state code out)
    (noLoads : ∀ command ∈ code, ∃ top, command = .exec top) (cache : List (Nat × Modules.Published)) :
    Modules.Loader.Runs program manifest active (.commands id code) ⟨state, cache⟩
      (Modules.Loader.liftResult id ⟨state, cache⟩ out) := by
  induction native with
  | done => exact .done
  | @step _ _ first _ _ head _ ih =>
    obtain ⟨top, rfl⟩ := noLoads first List.mem_cons_self
    exact .step (loader_command head cache) (ih (fun cmd member => noLoads cmd (List.mem_cons_of_mem _ member)))
  | @failed _ _ first _ _ head =>
    obtain ⟨top, rfl⟩ := noLoads first List.mem_cons_self
    exact .failed (loader_command head cache)

theorem exports_declared {source : Modules.Source} {state : State} {name : String} {value : Lists.Value}
    (loaded : (Modules.publish source state).1.exports.lookup name = some value) : name ∈ source.globals := by
  obtain ⟨before, after, shape, _⟩ := List.lookup_eq_some_iff.mp loaded
  have present : (name, value) ∈ (Modules.publish source state).1.exports := by
    rw [shape]
    simp
  have global := (List.mem_filter.mp present).1
  obtain ⟨selected, member, same⟩ := List.mem_filterMap.mp global
  cases h : state.bindingValue (globalSlot selected) with
  | error => simp [h, Except.toOption] at same
  | ok => simp [h, Except.toOption] at same; exact same.1 ▸ member

theorem cached_publication {exports : Environment} {program : Program} {published : Modules.Published}
    {state next : State} (live : PublishedLive exports program published state)
    (kept : ∀ (address : Nat) cell, state.heap[address]? = some cell → next.heap[address]? = some cell) :
    PublishedLive exports program published next := by
  intro name callee tracked publicName
  obtain ⟨linked, address, defining, loaded, record, frozen⟩ := live name callee tracked publicName
  refine ⟨linked, address, defining, loaded, { record with recorded := kept _ _ record.recorded, live := ?_ }, frozen⟩
  intro capture member
  obtain ⟨value, flag, found⟩ := record.live capture member
  exact ⟨value, flag, kept _ _ found⟩

theorem producer_cold_extending {commands : List Modules.Resolve.Command} {linked final : Program}
    {code : List Modules.Command} {producer consumer : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands linked code final exports)
    (checked : resolve commands linked = .ok producer)
    {consumerCommands : List Modules.Resolve.Command} {consumerSeed : Program}
    (consumerChecked : resolve consumerCommands consumerSeed = .ok consumer)
    (extension : PreservesDeclarations producer.program consumer.program)
    (valid : Modules.validateSource consumer.program producer.source = .ok ())
    {manifest : Modules.Loader.Manifest} (bound : 0 < manifest.size) (entry : manifest[0].source = producer.source)
    (active : List Nat) (permitted : 0 ∉ active) (session : Session)
    (cold : session.cache.lookup 0 = none) :
    ∃ out, Producer commands producer.source session out ∧
      Modules.Loader.Runs consumer.program manifest active (.initialize 0) session out ∧
      (reachedSession out).runtime.slots = session.runtime.slots ∧
      KeepsContents session.runtime (reachedSession out).runtime ∧
      ∀ published next, out = .ok published next →
        next.cache = (0, published) :: session.cache ∧
        PublishedLive exports consumer.program published next.runtime ∧
        ∀ name value, published.exports.lookup name = some value → name ∈ Trace.names commands := by
  obtain ⟨out, source, native, kept, live⟩ :=
    module_runs_extending profile checked consumerChecked extension (fun _ => none) session.runtime
  have noLoads : ∀ command ∈ producer.source.commands, ∃ top, command = .exec top := by
    rw [(plan_code profile checked).1]
    exact plan_executable profile
  have ran := loader_exec (manifest := manifest) (active := 0 :: active) (id := 0)
    native noLoads session.cache
  have initialized : Modules.Loader.Runs consumer.program manifest active (.initialize 0)
      session (observed 0 producer.source session.runtime session.cache out) := by
    rw [observed_eq 0 producer.source session.runtime session]
    rw [← entry] at valid ran ⊢
    exact .initialize bound permitted cold valid ran
  refine ⟨_, .cold cold source, initialized, ?_, ?_, ?_⟩
  · cases out with
    | error => rfl
    | ok value _ => cases value; rfl
  · cases out with
    | error => exact kept
    | ok value _ => cases value; exact kept
  · intro published next success
    cases out with
    | error => cases success
    | ok value reached =>
      cases value
      cases success
      refine ⟨rfl, live _ _ rfl, fun name value loaded => ?_⟩
      exact (plan_globals profile checked) ▸ exports_declared loaded

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
