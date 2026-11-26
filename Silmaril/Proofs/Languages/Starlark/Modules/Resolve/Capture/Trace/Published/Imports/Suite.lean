module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Consumer
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Invariant
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Definition
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

private theorem copy_record {importName globals producer program} {env : Tracked importName globals} {state middle : State} {source : Lowering.Resolve.SourceExpr}
    {rhs : Lowering.Expr} {value : Value} (copy : Copy importName source rhs)
    (evaluated : Body.Evaluates (block importName globals) state source rhs (.ok value middle))
    (live : Live importName producer program env state) :
    ∀ callee, copy.track env = some callee → ∃ address defining, value = .function address ∧
      callee.Linked producer program ∧ Nonempty (ClosureAt callee.layout.site callee.layout.id defining middle address) ∧
      callee.SharesImport defining.slots middle.slots := by
  intro callee tracked
  cases copy with
  | forget => cases tracked
  | name name =>
    obtain ⟨address, defining, loaded, linked, record, inherited⟩ := read_live live tracked
    generalize outcome : (EStateM.Result.ok value middle : Outcome Value) = result at evaluated
    cases evaluated with
    | read resolution =>
      rw [State.read, loaded] at outcome
      cases outcome
      exact ⟨address, defining, rfl, linked, record, inherited⟩

private theorem assigned_step {program : Program} {manifest : Modules.Loader.Manifest} {active : List Nat}
    {s : Session} {id : Nat} {name : String} {code : Lowering.Expr} {out : Outcome Value}
    (exec : ExecExpr program (List.range program.size) s.runtime code out) :
    Modules.Loader.Runs program manifest active (.command id (.exec (.assignExpr name code))) s
      (Modules.Loader.liftResult id s (afterWrite name out)) := by
  cases out <;> exact .exec (code := .assignExpr name code) (.assignExpr exec)

private theorem call_tracked {source : List Modules.Resolve.Command} {seed producer : Program} {resolved : ResolvedModule}
    (checked : resolve source seed = .ok resolved) (extension : PreservesDeclarations producer resolved.program)
    {importName globals} (call : Invocation importName globals) {env : Tracked importName globals}
    {imported : Callable} (importedLinked : imported.Linked producer) (importSeen : env importName = some (.regular imported))
    {callee : Callee importName globals} (tracked : env call.callee = some callee)
    {state : State} (live : Live importName producer resolved.program env state) :
    ∃ result, RunsAt callee.layout.site (callee.BodyRuns imported) (block importName globals) callee.layout.id call.callee
      (readSlot importName call.callee) call.arguments call.codes call.keywords.source call.keywords.codes call.star call.mapping state result ∧
      ExecExpr resolved.program (List.range resolved.program.size) state call.code result ∧
      Body.Keeps state.heap.size state (finishState result) := by
  obtain ⟨address, defining, loaded, linked, ⟨record⟩, inherited⟩ := read_live live tracked
  have read := Body.Evaluates.read (state := state) (read_resolves call.declared).1
  change Body.Evaluates _ _ _ _ (state.read (.bound (readSlot importName call.callee))) at read
  rw [State.read, loaded] at read
  cases callee with
  | regular entry =>
    have extended := linked_extends linked extension
    have permitted : entry.id ∈ List.range resolved.program.size :=
      List.mem_range.mpr (Array.getElem?_eq_some_iff.mp extended.1).choose
    obtain ⟨out, source, exec, _, kept⟩ := runs_at entry.site entry.BodyRuns checked entry.id extended.1 _ permitted
      (enter_callable checked extended) (readSlot importName call.callee) read record
      call.operands call.keywords call.star call.mapping
    exact ⟨out, source, exec, kept⟩
  | wrapper declaration id =>
    obtain ⟨aliasCell, origin, flag, originFrame, aliasSlot, stored, _, ⟨original⟩, _⟩ := live importName _ importSeen
    have owned : state.slots (fileSlot importName) = some (.owned aliasCell) := by simpa [readSlot] using aliasSlot
    have selected : Installs defining declaration.site.free [⟨fileSlot importName, aliasCell, true⟩] :=
      .cons (.enclosing (inherited.trans owned)) .nil
    have sameCaptures : record.captures = [⟨fileSlot importName, aliasCell, true⟩] :=
      Except.ok.inj ((installs_lookup _ record.installed).symm.trans (installs_lookup _ selected))
    have permitted : id ∈ List.range resolved.program.size :=
      List.mem_range.mpr (Array.getElem?_eq_some_iff.mp linked.2).choose
    obtain ⟨out, source, exec, _, kept⟩ := runs_at_reached declaration.site (declaration.Returns imported)
      checked id linked.2 _ permitted (readSlot importName call.callee) read record
      (fun packed kept assigned => by
        rw [sameCaptures]
        exact wrapper_returns declaration checked extension id linked.1 importedLinked original stored packed kept assigned)
      call.operands call.keywords call.star call.mapping
    exact ⟨out, source, exec, kept⟩

private theorem returned_copy {importName globals producer program} {callee : Callee importName globals} {imported : Callable}
    {call : Invocation importName globals} {state returned : State} {value : Value}
    (linked : callee.Linked producer program) (importLinked : imported.Linked producer)
    (source : RunsAt callee.layout.site (callee.BodyRuns imported) (block importName globals) callee.layout.id call.callee
      (readSlot importName call.callee) call.arguments call.codes call.keywords.source call.keywords.codes call.star call.mapping
      state (.ok value returned)) :
    ∀ child, callee.returned imported = some child →
      ∃ address defining, value = .function address ∧ child.Linked producer program ∧
        Nonempty (ClosureAt child.layout.site child.layout.id defining returned address) ∧
        child.SharesImport defining.slots returned.slots := by
  intro child chosen
  cases callee with
  | regular entry =>
    cases found : entry.returned with
    | none => simp [Callee.returned, found] at chosen
    | some nested =>
      have same : child = .regular (.nested nested) := by simpa [Callee.returned, found, eq_comm] using chosen
      subst child
      have selected : entry.returned.map Callable.nested = some (.nested nested) := by simp [found]
      obtain ⟨address, defining, valueAt, closure⟩ := returned_record source _ selected
      exact ⟨address, defining, valueAt, returned_linked linked _ selected, closure, trivial⟩
  | wrapper declaration index =>
    cases found : imported.returned with
    | none => simp [Callee.returned, found] at chosen
    | some nested =>
      have same : child = .regular (.nested nested) := by simpa [Callee.returned, found, eq_comm] using chosen
      subst child
      have selected : imported.returned.map Callable.nested = some (.nested nested) := by simp [found]
      generalize outcome : (EStateM.Result.ok value returned : Outcome Value) = out at source
      cases source with
      | calleeError | argumentError | bindingError => cases outcome
      | @invoked _ _ _ _ _ bodyOut _ _ _ _ _ _ _ body =>
        obtain ⟨inner, ran, rfl⟩ := body
        cases inner with
        | error => cases outcome
        | ok result reached =>
          cases outcome
          obtain ⟨address, defining, valueAt, ⟨record⟩⟩ := returned_record ran _ selected
          exact ⟨address, defining, valueAt, returned_linked importLinked _ selected,
            ⟨⟨record.captures, record.defaults, record.frozen, record.length,
              record.recorded, record.installed, record.live⟩⟩, trivial⟩

private theorem tracks_import {importName globals} {env : Tracked importName globals} {imported : Callable} {name : String}
    (member : name ∈ globals) (separate : importName ∉ globals) (seen : env importName = some (.regular imported))
    (entry : Option (Callee importName globals)) : track env name entry importName = some (.regular imported) := by
  have different : importName ≠ name := fun same => separate (same.symm ▸ member)
  simp [track, different, seen]

private theorem prefix_size {producer later : Program} (producerPrefix : PreservesDeclarations producer later) :
    producer.size ≤ later.size := by
  apply Nat.le_of_not_gt
  intro within
  have stored : producer[later.size]? = some producer[later.size] := Array.getElem?_eq_getElem within
  have impossible := (Array.getElem?_eq_some_iff.mp (producerPrefix _ _ stored)).choose
  exact (Nat.lt_irrefl _ impossible)

theorem keeps_below {floor : Nat} {state next : State} (kept : Body.Keeps state.heap.size state next) :
    Body.Keeps floor state next :=
  ⟨kept.1, fun index cell _ found => kept.2 index cell (Array.getElem?_eq_some_iff.mp found).choose found⟩

theorem fresh_slots {floor : Nat} {state next : State} (fresh : FreshSlots floor state)
    (slots : next.slots = state.slots) : FreshSlots floor next :=
  fun binding address owned => fresh binding address (slots ▸ owned)

private theorem write_fresh {aliasName : String} {globals : List String} {floor : Nat} {state : State} {name : String}
    (frame : Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Frame aliasName globals state) (fresh : FreshSlots floor state) (member : name ∈ globals)
    (value : Lists.Value) : Body.Keeps floor state (state.write (globalSlot name) value) := by
  obtain ⟨address, _, _, owned, _⟩ := frame.2 _ (List.mem_cons_of_mem _ (List.mem_map_of_mem member))
  exact write_keeps_below owned (fresh _ _ owned) value

theorem run_suite_preserving {source : List Modules.Resolve.Command} {seed producer : Program} {resolved : ResolvedModule}
    (checked : resolve source seed = .ok resolved)
    {manifest : Modules.Loader.Manifest} {active : List Nat} {id : Nat}
    {importName : String} {globals : List String} (separate : importName ∉ globals)
    (steps : List (Step importName globals)) (prefixTable : Program)
    (producerPrefix : PreservesDeclarations producer prefixTable)
    (table : PreservesDeclarations (compileSuite prefixTable steps).2 resolved.program)
    {imported : Callable} {env : Tracked importName globals} (admitted : ReadyFor imported prefixTable env steps)
    (importLinked : imported.Linked producer) (seen : env importName = some (.regular imported))
    (session : Session) (frame : Frame importName globals session.runtime)
    (floor : Nat) (fresh : FreshSlots floor session.runtime)
    (live : Live importName producer resolved.program env session.runtime) :
    ∃ out, SuiteRuns imported prefixTable session.runtime steps out ∧
      Modules.Loader.Runs resolved.program manifest active (.commands id (compileSuite prefixTable steps).1) session
        (Modules.Loader.liftResult id session out) ∧
      Body.Keeps floor session.runtime (resultState out) ∧
      KeepsClosureCells session.runtime (resultState out) ∧
      ∀ reached, out = .ok () reached →
        Frame importName globals reached ∧ Live importName producer resolved.program (trackSuite imported prefixTable env steps) reached := by
  induction steps generalizing env session prefixTable with
  | nil => exact ⟨_, .done _ _, .done, ⟨rfl, fun _ _ _ found => found⟩,
    closure_cells_of_contents (fun _ cell found => ⟨cell.frozen, found⟩), fun _ same => by cases same; exact ⟨frame, live⟩⟩
  | cons head tail ih =>
    cases head with
    | @assign name declared source rhs reads operand copy =>
      have next : ReadyFor imported prefixTable (track env name (copy.track env)) tail := admitted
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
        have reached := writes_live arrived (keeps_live live kept) declared
          (fun same => separate (same ▸ declared)) value _ (copy_record copy ran live)
        have preserved := Body.keeps_trans (keeps_below (floor := floor) kept)
          (write_fresh arrived (fresh_slots fresh kept.1) declared value)
        obtain ⟨out, trace, nativeTail, tailKept, records, finished⟩ := ih prefixTable producerPrefix table next
          (tracks_import declared separate seen _) {session with runtime := middle.write (globalSlot name) value}
          written (fresh_slots fresh preserved.1) reached
        exact ⟨out, .next (.assign ran) trace, .step step nativeTail, Body.keeps_trans preserved tailKept,
          closure_cells_trans (closure_cells_of_keeps kept)
            (closure_cells_trans (write_global_closure_cells arrived declared value) records), finished⟩
    | invoke call =>
      obtain ⟨callee, tracked, remaining⟩ := admitted
      have next : ReadyFor imported prefixTable (track env call.destination
          (callee.returned imported)) tail := by
        simpa [Step.emit, Step.advance, tracked] using remaining
      have extension : PreservesDeclarations producer resolved.program :=
        fun index declaration found => table _ _ (preserves_suite tail prefixTable _ _ (producerPrefix index declaration found))
      obtain ⟨result, ran, native, kept⟩ := call_tracked checked extension call importLinked seen tracked live
      have step := assigned_step (manifest := manifest) (active := active) (id := id)
        (name := call.destination) (code := call.code) native
      cases result with
      | error => exact ⟨_, .failed (.invoke callee ran), .failed step, keeps_below kept, closure_cells_of_keeps kept, fun _ impossible => nomatch impossible⟩
      | ok value returned =>
        obtain ⟨_, _, _, linked, _, _⟩ := read_live live tracked
        have arrived := keeps_frame frame kept
        have written := writes_frame arrived (globalSlot call.destination) value
        have reached := writes_live arrived (keeps_live live kept) call.destinationGlobal
          (fun same => separate (same ▸ call.destinationGlobal)) value _ (returned_copy linked importLinked ran)
        have preserved := Body.keeps_trans (keeps_below (floor := floor) kept)
          (write_fresh arrived (fresh_slots fresh kept.1) call.destinationGlobal value)
        obtain ⟨out, trace, nativeTail, tailKept, records, finished⟩ := ih prefixTable producerPrefix table next
          (tracks_import call.destinationGlobal separate seen _) {session with runtime := returned.write (globalSlot call.destination) value}
          written (fresh_slots fresh preserved.1) reached
        refine ⟨out, .next (.invoke callee ran) trace, .step step nativeTail, Body.keeps_trans preserved tailKept,
          closure_cells_trans (closure_cells_of_keeps kept)
            (closure_cells_trans (write_global_closure_cells arrived call.destinationGlobal value) records), ?_⟩
        simpa [trackSuite, Step.emit, Step.advance, tracked] using finished
    | define declaration =>
      let nextTable := prefixTable.push declaration.site.declaration
      have found : resolved.program[prefixTable.size]? = some declaration.site.declaration :=
        table _ _ (preserves_suite tail nextTable _ _ Array.getElem?_push_size)
      obtain ⟨_, _, _, owned, stored⟩ := frame.2 (fileSlot importName) List.mem_cons_self
      obtain ⟨grown, kept, closure, source, native⟩ :=
        wrapper_allocates declaration resolved.program prefixTable.size found owned stored
      have arrived := keeps_frame frame kept
      let value := Lists.Value.function session.runtime.heap.size
      let next := grown.write (globalSlot declaration.name) value
      have updated : Live importName producer resolved.program
          (track env declaration.name (some (.wrapper declaration prefixTable.size))) next := by
        apply writes_live arrived (keeps_live live kept) declaration.target
          (fun same => separate (same ▸ declaration.target)) value
        intro callee chosen
        cases chosen
        exact ⟨_, session.runtime, rfl, ⟨prefix_size producerPrefix, found⟩, closure, congrFun kept.1.symm _⟩
      have step : Modules.Loader.Runs resolved.program manifest active (.command id (.exec (.define declaration.name prefixTable.size)))
          session (.ok () {session with runtime := next}) :=
        .exec (code := .define declaration.name prefixTable.size) native
      have nextPrefix : PreservesDeclarations producer nextTable :=
        fun index entry linked => preserves_emit (.define declaration) prefixTable _ _ (producerPrefix index entry linked)
      have preserved := Body.keeps_trans (keeps_below (floor := floor) kept)
        (write_fresh arrived (fresh_slots fresh kept.1) declaration.target value)
      obtain ⟨out, trace, nativeTail, tailKept, records, finished⟩ := ih nextTable nextPrefix table admitted
        (tracks_import declaration.target separate seen _) {session with runtime := next}
        (writes_frame arrived (globalSlot declaration.name) value) (fresh_slots fresh preserved.1) updated
      exact ⟨out, .next (.define source) trace, .step step nativeTail, Body.keeps_trans preserved tailKept,
        closure_cells_trans (closure_cells_of_keeps kept)
          (closure_cells_trans (write_global_closure_cells arrived declaration.target value) records), finished⟩

theorem run_suite {source : List Modules.Resolve.Command} {seed producer : Program} {resolved : ResolvedModule}
    (checked : resolve source seed = .ok resolved)
    {manifest : Modules.Loader.Manifest} {active : List Nat} {id : Nat}
    {importName : String} {globals : List String} (separate : importName ∉ globals)
    (steps : List (Step importName globals)) (prefixTable : Program)
    (producerPrefix : PreservesDeclarations producer prefixTable)
    (table : PreservesDeclarations (compileSuite prefixTable steps).2 resolved.program)
    {imported : Callable} {env : Tracked importName globals} (admitted : ReadyFor imported prefixTable env steps)
    (importLinked : imported.Linked producer) (seen : env importName = some (.regular imported))
    (session : Session) (frame : Frame importName globals session.runtime)
    (live : Live importName producer resolved.program env session.runtime) :
    ∃ out, SuiteRuns imported prefixTable session.runtime steps out ∧
      Modules.Loader.Runs resolved.program manifest active (.commands id (compileSuite prefixTable steps).1) session
        (Modules.Loader.liftResult id session out) ∧
      ∀ reached, out = .ok () reached →
        Frame importName globals reached ∧ Live importName producer resolved.program (trackSuite imported prefixTable env steps) reached := by
  obtain ⟨out, source, native, _, _, completed⟩ := run_suite_preserving checked separate steps prefixTable
    producerPrefix table admitted importLinked seen session frame 0 (fun _ _ _ => Nat.zero_le _) live
  exact ⟨out, source, native, completed⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
