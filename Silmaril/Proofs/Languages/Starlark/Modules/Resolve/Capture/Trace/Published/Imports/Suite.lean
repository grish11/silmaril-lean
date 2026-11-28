module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Consumer
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Invariant
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Definition
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Callable
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Frame

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (fileSlot globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call (ClosureAt)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named (runs_at runs_at_reached RunsAt Spread Mapping)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Outcome)
open Silmaril.Languages.Starlark.Lists.Iteration (finishState)
open Silmaril.Languages.Starlark.Modules.Loader (Session)

local notation "Value" => Lists.Value

private theorem copy_record {aliases globals producer program} {env : Tracked} {state middle : State} {source : Lowering.Resolve.SourceExpr}
    {rhs : Lowering.Expr} {value : Value} (copy : Copy aliases source rhs)
    (evaluated : Body.Evaluates (block aliases globals) state source rhs (.ok value middle))
    (live : Live aliases producer program env state) :
    ∀ callee, copy.track env = some callee → ∃ address, value = .function address ∧
      callee.At producer program middle address := by
  intro callee tracked
  cases copy with
  | forget => cases tracked
  | name name =>
    obtain ⟨address, loaded, record⟩ := read_live live tracked
    generalize outcome : (EStateM.Result.ok value middle : Outcome Value) = result at evaluated
    cases evaluated with
    | read resolution =>
      rw [State.read, loaded] at outcome
      cases outcome
      exact ⟨address, rfl, record⟩

private theorem assigned_step {program : Program} {manifest : Modules.Loader.Manifest} {active : List Nat}
    {s : Session} {id : Nat} {name : String} {code : Lowering.Expr} {out : Outcome Value}
    (exec : ExecExpr program (List.range program.size) s.runtime code out) :
    Modules.Loader.Runs program manifest active (.command id (.exec (.assignExpr name code))) s
      (Modules.Loader.liftResult id s (afterWrite name out)) := by
  cases out <;> exact .exec (code := .assignExpr name code) (.assignExpr exec)

private theorem call_tracked {source : List Modules.Resolve.Command} {seed producer : Program} {resolved : ResolvedModule}
    (checked : resolve source seed = .ok resolved) (extension : PreservesDeclarations producer resolved.program)
    {aliases globals} (call : Invocation aliases globals) {env : Tracked}
    {callee : Callee} (tracked : env call.callee = some callee)
    {state : State} (live : Live aliases producer resolved.program env state) :
    ∃ result, RunsAt callee.layout.site callee.BodyRuns (block aliases globals) callee.layout.id call.callee
      (readSlot aliases call.callee) call.arguments call.codes call.keywords.source call.keywords.codes call.star call.mapping state result ∧
      ExecExpr resolved.program (List.range resolved.program.size) state call.code result ∧
      Body.Keeps state.heap.size state (finishState result) := by
  obtain ⟨address, loaded, record⟩ := read_live live tracked
  have read := Body.Evaluates.read (state := state) (read_resolves call.declared).1
  change Body.Evaluates _ _ _ _ (state.read (.bound (readSlot aliases call.callee))) at read
  rw [State.read, loaded] at read
  have bound := (Array.getElem?_eq_some_iff.mp (callable_found extension record)).choose
  have guard : List.Subset (List.range (callee.layout.id + 1)) (List.range resolved.program.size) := by
    intro index member
    have low := List.mem_range.mp member
    exact List.mem_range.mpr (by omega)
  exact invoke_callable checked extension callee guard (readSlot aliases call.callee) read record
    call.operands call.keywords call.star call.mapping

private theorem returned_copy {aliases globals producer program} {callee : Callee}
    {call : Invocation aliases globals} {state returned : State} {value : Value} {address : Nat}
    (live : callee.At producer program state address)
    (source : RunsAt callee.layout.site callee.BodyRuns (block aliases globals) callee.layout.id call.callee
      (readSlot aliases call.callee) call.arguments call.codes call.keywords.source call.keywords.codes call.star call.mapping
      state (.ok value returned)) :
    ∀ child, callee.returned.map Callee.regular = some child →
      ∃ address, value = .function address ∧ child.At producer program returned address := by
  intro child selected
  cases found : callee.returned with
  | none => simp [found] at selected
  | some entry =>
    have equal : Callee.regular entry = child := by simpa [found] using selected
    subst child
    obtain ⟨address, _, saved, ⟨record⟩⟩ := callable_return_record callee source found
    exact ⟨address, saved, .regular (callable_return_link live found) record⟩

theorem keeps_below {floor : Nat} {state next : State} (kept : Body.Keeps state.heap.size state next) :
    Body.Keeps floor state next :=
  ⟨kept.1, fun index cell _ found => kept.2 index cell (Array.getElem?_eq_some_iff.mp found).choose found⟩

theorem fresh_slots {floor : Nat} {state next : State} (fresh : FreshSlots floor state)
    (slots : next.slots = state.slots) : FreshSlots floor next :=
  fun binding address owned => fresh binding address (slots ▸ owned)

private theorem write_fresh {aliases : List String} {globals : List String} {floor : Nat} {state : State} {name : String}
    (frame : Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Frame aliases globals state) (fresh : FreshSlots floor state) (member : name ∈ globals)
    (value : Lists.Value) : Body.Keeps floor state (state.write (globalSlot name) value) := by
  obtain ⟨address, _, _, owned, _⟩ := frame.2 _ (List.mem_append.mpr (.inr (List.mem_map_of_mem member)))
  exact write_keeps_below owned (fresh _ _ owned) value

theorem consumer_pending {plan : Consumer} {seed : Program} {consumer : ResolvedModule}
    (checked : resolve plan.commands seed = .ok consumer) {caller reached : State}
    (slots : reached.slots = (Modules.enter consumer.source caller).slots)
    (contents : KeepsContents (Modules.enter consumer.source caller) reached) {value : Lists.Value} :
    (plan.body.map Step.destination).Nodup ∧
    Blank reached (fileSlot plan.alias) ∧
    ∀ step ∈ plan.body, Blank (reached.write (fileSlot plan.alias) value) (globalSlot step.destination) := by
  obtain ⟨_, _, globals, files⟩ := consumer_layout plan checked
  have unique := Entry.validated_module_names (checked_of_resolve checked).2.2.2
  rw [globals, ← plan.declared] at unique
  have frame := dependency_frame (plan := plan) globals files slots contents
  refine ⟨unique, entered_blank_after_dependency slots contents (by simp [files]), ?_⟩
  intro step member
  have mapped : step.destination ∈ plan.body.map Step.destination := List.mem_map_of_mem member
  have declared := plan.declared ▸ mapped
  exact other_blank frame.1 (by intro equal; cases equal)
    (entered_blank_after_dependency slots contents (by
      rw [globals]
      exact List.mem_append.mpr (.inl (List.mem_map_of_mem declared)))) value

private theorem pending_write {aliases globals} {head : Step aliases globals}
    {tail : List (Step aliases globals)} {state middle : State}
    (unique : ((head :: tail).map Step.destination).Nodup) (frame : Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Frame aliases globals middle)
    (pending : ∀ step ∈ head :: tail, Blank state (globalSlot step.destination))
    (kept : Body.Keeps state.heap.size state middle) (value : Lists.Value) :
    ∀ step ∈ tail, Blank (middle.write (globalSlot head.destination) value) (globalSlot step.destination) := by
  intro step member
  have mapped : step.destination ∈ tail.map Step.destination := List.mem_map_of_mem member
  have different : head.destination ≠ step.destination :=
    fun same => (List.nodup_cons.mp unique).1 (same.symm ▸ mapped)
  exact other_blank frame.1 (fun equal => different (congrArg Binding.name equal))
    (keeps_blank (pending step (List.mem_cons_of_mem _ member)) kept) value

theorem run_suite_preserving {source : List Modules.Resolve.Command} {seed producer : Program} {resolved : ResolvedModule}
    (checked : resolve source seed = .ok resolved)
    {manifest : Modules.Loader.Manifest} {active : List Nat} {id : Nat}
    {aliases : List String} {globals : List String} (separate : ∀ name ∈ globals, name ∉ aliases)
    (steps : List (Step aliases globals)) (prefixTable : Program)
    (producerPrefix : PreservesDeclarations producer prefixTable)
    (table : PreservesDeclarations (compileSuite prefixTable steps).2 resolved.program)
    {env : Tracked} (admitted : ReadyFor prefixTable env steps)
    (unique : (steps.map Step.destination).Nodup)
    (session : Session) (frame : Frame aliases globals session.runtime)
    (pending : ∀ step ∈ steps, Blank session.runtime (globalSlot step.destination))
    (floor : Nat) (fresh : FreshSlots floor session.runtime)
    (live : Live aliases producer resolved.program env session.runtime) :
    ∃ out, SuiteRuns prefixTable session.runtime steps out ∧
      Modules.Loader.Runs resolved.program manifest active (.commands id (compileSuite prefixTable steps).1) session
        (Modules.Loader.liftResult id session out) ∧
      Body.Keeps floor session.runtime (resultState out) ∧
      KeepsClosureCells session.runtime (resultState out) ∧
      ∀ reached, out = .ok () reached →
        Frame aliases globals reached ∧ Live aliases producer resolved.program (trackSuite prefixTable env steps) reached := by
  induction steps generalizing env session prefixTable with
  | nil => exact ⟨_, .done _ _, .done, ⟨rfl, fun _ _ _ found => found⟩,
    closure_cells_of_contents (fun _ cell found => ⟨cell.frozen, found⟩), fun _ same => by cases same; exact ⟨frame, live⟩⟩
  | cons head tail ih =>
    have tailUnique := (List.nodup_cons.mp unique).2
    have headBlank := pending head List.mem_cons_self
    cases head with
    | @assign name declared source rhs reads operand copy =>
      let stepSource : Step aliases globals := .assign name declared operand copy
      have next : ReadyFor prefixTable (track env name (copy.track env)) tail := admitted
      obtain ⟨result, ran, kept⟩ := Body.operand_total operand session.runtime
      have native : ExecExpr resolved.program (List.range resolved.program.size) session.runtime rhs result :=
        .evaluates (calls := fun _ _ _ => False) (fun _ _ _ no => no.elim)
          (Body.evaluates_with _ _ _ ran)
      have step := assigned_step (manifest := manifest) (active := active) (id := id) (name := name) native
      cases result with
      | error => exact ⟨_, .failed (.assign ran), .failed step, keeps_below kept, closure_cells_of_keeps kept, fun _ impossible => nomatch impossible⟩
      | ok value middle =>
        have arrived := keeps_frame frame kept
        have written := writes_frame arrived (globalSlot name) value
        have blank := keeps_blank headBlank kept
        have reached := writes_live blank (keeps_live live kept)
          (separate _ declared) value _ (copy_record copy ran live)
        have preserved := Body.keeps_trans (keeps_below (floor := floor) kept)
          (write_fresh arrived (fresh_slots fresh kept.1) declared value)
        obtain ⟨out, trace, nativeTail, tailKept, records, finished⟩ :=
          ih prefixTable producerPrefix table next tailUnique {session with runtime := middle.write (globalSlot name) value}
          written (pending_write (head := stepSource) unique arrived pending kept value) (fresh_slots fresh preserved.1) reached
        exact ⟨out, .next (.assign ran) trace, .step step nativeTail, Body.keeps_trans preserved tailKept,
          closure_cells_trans (closure_cells_of_keeps kept)
            (closure_cells_trans (write_blank_cells blank value) records), finished⟩
    | invoke call =>
      obtain ⟨callee, tracked, remaining⟩ := admitted
      have next : ReadyFor prefixTable (track env call.destination
          (callee.returned.map Callee.regular)) tail := by
        simpa [Step.emit, Step.advance, tracked] using remaining
      have extension : PreservesDeclarations producer resolved.program :=
        fun index declaration found => table _ _ (preserves_suite tail prefixTable _ _ (producerPrefix index declaration found))
      obtain ⟨result, ran, native, kept⟩ := call_tracked checked extension call tracked live
      have step := assigned_step (manifest := manifest) (active := active) (id := id)
        (name := call.destination) (code := call.code) native
      cases result with
      | error => exact ⟨_, .failed (.invoke callee ran), .failed step, keeps_below kept, closure_cells_of_keeps kept, fun _ impossible => nomatch impossible⟩
      | ok value returned =>
        obtain ⟨_, _, record⟩ := read_live live tracked
        have arrived := keeps_frame frame kept
        have written := writes_frame arrived (globalSlot call.destination) value
        have blank := keeps_blank headBlank kept
        have reached := writes_live blank (keeps_live live kept)
          (separate _ call.destinationGlobal) value _ (returned_copy record ran)
        have preserved := Body.keeps_trans (keeps_below (floor := floor) kept)
          (write_fresh arrived (fresh_slots fresh kept.1) call.destinationGlobal value)
        obtain ⟨out, trace, nativeTail, tailKept, records, finished⟩ :=
          ih prefixTable producerPrefix table next tailUnique {session with runtime := returned.write (globalSlot call.destination) value}
          written (pending_write (head := .invoke call) unique arrived pending kept value) (fresh_slots fresh preserved.1) reached
        refine ⟨out, .next (.invoke callee ran) trace, .step step nativeTail, Body.keeps_trans preserved tailKept,
          closure_cells_trans (closure_cells_of_keeps kept)
            (closure_cells_trans (write_blank_cells blank value) records), ?_⟩
        simpa [trackSuite, Step.emit, Step.advance, tracked] using finished
    | @define importName declaration =>
      obtain ⟨imported, seen, earlier, remaining⟩ := admitted
      let nextTable := prefixTable.push declaration.site.declaration
      have found : resolved.program[prefixTable.size]? = some declaration.site.declaration :=
        table _ _ (preserves_suite tail nextTable _ _ Array.getElem?_push_size)
      obtain ⟨aliasCell, target, flag, aliasOwned, stored, targetLive⟩ := live importName imported seen
      have owned : session.runtime.slots (fileSlot importName) = some (.owned aliasCell) := by
        simpa [readSlot, declaration.visible] using aliasOwned
      obtain ⟨defined, source, native, _, reached⟩ :=
        wrapper_defines declaration resolved.program prefixTable.size found owned stored
      cases defined with
      | error error stopped =>
        exact ⟨_, .failed (.define source), .failed (.exec (code := .define declaration.name prefixTable.size) native),
          keeps_below reached, closure_cells_of_keeps reached, fun _ impossible => nomatch impossible⟩
      | ok flow next =>
        cases flow with
        | breakLoop | continueLoop | returned => exact reached.elim
        | next =>
          obtain ⟨evaluated, _, grown, _, rfl, kept, closure, captures, _⟩ := reached
          let value := Lists.Value.function evaluated.heap.size
          let next := grown.write (globalSlot declaration.name) value
          have arrived := keeps_frame frame kept
          have blank := keeps_blank headBlank kept
          have preservedAlias := kept.2 _ _ (Array.getElem?_eq_some_iff.mp stored).choose stored
          have updated : Live aliases producer resolved.program
              (track env declaration.name (some (.wrapper declaration prefixTable.size imported))) next := by
            apply writes_live blank (keeps_live live kept)
              (separate _ declaration.target) value
            intro callee chosen
            cases chosen
            exact ⟨_, rfl, .wrapper found earlier closure captures preservedAlias
              (transport_callable targetLive (closure_cells_of_keeps kept))⟩
          have step : Modules.Loader.Runs resolved.program manifest active
              (.command id (.exec (.define declaration.name prefixTable.size))) session (.ok () {session with runtime := next}) :=
            .exec (code := .define declaration.name prefixTable.size) native
          have nextPrefix : PreservesDeclarations producer nextTable :=
            fun index entry linked => preserves_emit (.define declaration) prefixTable _ _ (producerPrefix index entry linked)
          have preserved := Body.keeps_trans (keeps_below (floor := floor) kept)
            (write_fresh arrived (fresh_slots fresh kept.1) declaration.target value)
          have nextReady : ReadyFor nextTable
              (track env declaration.name (some (.wrapper declaration prefixTable.size imported))) tail := by
            simpa [Step.emit, Step.advance, seen, nextTable] using remaining
          obtain ⟨out, trace, nativeTail, tailKept, records, finished⟩ := ih nextTable nextPrefix table nextReady
            tailUnique {session with runtime := next}
            (writes_frame arrived (globalSlot declaration.name) value)
            (pending_write (head := .define declaration) unique arrived pending kept value)
            (fresh_slots fresh preserved.1) updated
          refine ⟨out, .next (.define source) trace, .step step nativeTail, Body.keeps_trans preserved tailKept,
            closure_cells_trans (closure_cells_of_keeps kept)
              (closure_cells_trans (write_blank_cells blank value) records), ?_⟩
          simpa [trackSuite, Step.emit, Step.advance, seen, nextTable] using finished

theorem run_suite {source : List Modules.Resolve.Command} {seed producer : Program} {resolved : ResolvedModule}
    (checked : resolve source seed = .ok resolved)
    {manifest : Modules.Loader.Manifest} {active : List Nat} {id : Nat}
    {aliases : List String} {globals : List String} (separate : ∀ name ∈ globals, name ∉ aliases)
    (steps : List (Step aliases globals)) (prefixTable : Program)
    (producerPrefix : PreservesDeclarations producer prefixTable)
    (table : PreservesDeclarations (compileSuite prefixTable steps).2 resolved.program)
    {env : Tracked} (admitted : ReadyFor prefixTable env steps)
    (unique : (steps.map Step.destination).Nodup)
    (session : Session) (frame : Frame aliases globals session.runtime)
    (pending : ∀ step ∈ steps, Blank session.runtime (globalSlot step.destination))
    (live : Live aliases producer resolved.program env session.runtime) :
    ∃ out, SuiteRuns prefixTable session.runtime steps out ∧
      Modules.Loader.Runs resolved.program manifest active (.commands id (compileSuite prefixTable steps).1) session
        (Modules.Loader.liftResult id session out) ∧
      ∀ reached, out = .ok () reached →
        Frame aliases globals reached ∧ Live aliases producer resolved.program (trackSuite prefixTable env steps) reached := by
  obtain ⟨out, source, native, _, _, completed⟩ := run_suite_preserving checked separate steps prefixTable
    producerPrefix table admitted unique session frame pending 0 (fun _ _ _ => Nat.zero_le _) live
  exact ⟨out, source, native, completed⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
