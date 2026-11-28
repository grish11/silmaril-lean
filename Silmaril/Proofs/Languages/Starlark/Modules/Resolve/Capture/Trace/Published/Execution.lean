module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Defs
public import Silmaril.Languages.Starlark.Modules.Operational.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Elaboration
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Frame
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.Thms
import Silmaril.Languages.Starlark.Modules.Thms
import Silmaril.Languages.Starlark.Lists.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (globalSlot Catalog enter finish Published TopCode)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive
  (lexical_defaults default_layout)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call
  (ClosureAt BodyEntry RunsActual BindingRule PackRule)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance
  (runs_activated_for links return_link invoked_value_at)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named (RunsAt runs_at)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Outcome Cell Capture)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow finishState)

local notation "Value" => Lists.Value
private abbrev Ready (globals : List String) (program : Program) (env : Environment) : Prop :=
  ∀ name callee, env name = some callee → name ∈ globals ∧ callee.Linked program

private theorem ready_update {globals : List String} {program : Program} {env : Environment}
    (ready : Ready globals program env) {name : String} (member : name ∈ globals) (entry : Option Callable)
    (new : ∀ callee, entry = some callee → callee.Linked program) :
    Ready globals program (update env name entry) := by
  intro read callee tracked
  by_cases same : read = name
  · subst read
    exact ⟨member, new callee (by simpa [update] using tracked)⟩
  · exact ready read callee (by simpa [update, same] using tracked)

private theorem known_globals {globals : List String} {program : Program} {env : Environment}
    (ready : Ready globals program env) : ∀ name callee, env name = some callee → name ∈ globals :=
  fun name callee found => (ready name callee found).1

private theorem root_found {globals : List String} {root : Root globals} {program : Program}
    (known : PreservesDeclarations root.table program) : program[root.id]? = some root.site.declaration :=
  known _ _ Array.getElem?_push_size

private theorem root_linked {globals : List String} {root : Root globals} {program : Program}
    (known : PreservesDeclarations root.table program) : root.callable.Linked program := by
  refine ⟨root_found known, root.seed, root.bodyTable, root.children, rfl, ?_, root.suite⟩
  intro id declaration found
  exact known _ _ (by simp [Root.table, Array.getElem?_push, Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp found).choose, found])

theorem enter_callable_below {callee : Callable} {prefixTable : Program}
    {commands : List Silmaril.Languages.Starlark.Modules.Resolve.Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (known : callee.Linked prefixTable)
    (extension : PreservesDeclarations prefixTable resolved.program) (available : List DeclarationId)
    (retained : List.Subset (List.range callee.id) available) :
    BodyEntry callee.site resolved.program available callee.id callee.BodyRuns := by
  obtain ⟨_, seed, bodyTable, children, size, table, suite⟩ := known
  have guarded : List.Subset (children.map Prod.fst) (withoutDeclaration available callee.id) := by
    intro index member
    obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    have stored := (links suite).2 entry present
    have earlier := (Array.getElem?_eq_some_iff.mp stored).choose
    rw [size] at earlier
    exact mem_withoutDeclaration.mpr ⟨retained (List.mem_range.mpr earlier), Nat.ne_of_lt earlier⟩
  intro caller defining captures installed live assigned
  obtain ⟨out, ran, _, kept, exec, _, resultRecord⟩ :=
    runs_activated_for callee.site suite checked (fun id declaration found => extension id declaration (table id declaration found))
      _ guarded caller defining captures installed live assigned
  exact ⟨out, ⟨ran, resultRecord⟩, exec, Body.returned_keeps caller callee.site.declaration captures assigned out kept⟩

theorem enter_callable_for {callee : Callable} {prefixTable : Program}
    {commands : List Silmaril.Languages.Starlark.Modules.Resolve.Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (known : callee.Linked prefixTable)
    (extension : PreservesDeclarations prefixTable resolved.program) (available : List DeclarationId)
    (retained : List.Subset (List.range prefixTable.size) available) :
    BodyEntry callee.site resolved.program available callee.id callee.BodyRuns :=
  enter_callable_below checked known extension available
    (fun _ member => retained (List.mem_range.mpr
      (Nat.lt_trans (List.mem_range.mp member) (Array.getElem?_eq_some_iff.mp known.1).choose)))

theorem enter_callable {callee : Callable}
    {commands : List Silmaril.Languages.Starlark.Modules.Resolve.Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (known : callee.Linked resolved.program) :
    BodyEntry callee.site resolved.program (List.range resolved.program.size) callee.id callee.BodyRuns :=
  enter_callable_for checked known (fun _ _ found => found) _ (fun _ member => member)

theorem linked_extends {callee : Callable} {earlier later : Program}
    (known : callee.Linked earlier) (extendsTable : PreservesDeclarations earlier later) :
    callee.Linked later := by
  obtain ⟨found, seed, bodyTable, children, size, table, suite⟩ := known
  exact ⟨extendsTable _ _ found, seed, bodyTable, children, size,
    fun index declaration stored => extendsTable index declaration (table index declaration stored), suite⟩

theorem returned_linked {callee : Callable} {program : Program} (known : callee.Linked program) :
    ∀ next, callee.returned.map Callable.nested = some next → next.Linked program := by
  intro next found
  cases result : callee.returned with
  | none => simp [result] at found
  | some entry =>
    have same : Callable.nested entry = next := by simpa [result] using found
    subst next
    obtain ⟨_, _, _, _, _, table, suite⟩ := known
    exact return_link suite table (fun _ _ no => nomatch no) entry result

theorem returned_record {callee : Callable} {block : LexicalBlock} {name : String} {slot : Binding}
    {Bound : Type} {actuals : State → Outcome Actual → Prop} {binds : BindingRule Bound} {packs : PackRule Bound}
    {state reached : State} {value : Value}
    (ran : RunsActual callee.site callee.BodyRuns block callee.id name slot actuals binds packs state (.ok value reached)) :
    ∀ next, callee.returned.map Callable.nested = some next → ∃ address defining, value = .function address ∧
      Nonempty (ClosureAt next.site next.id defining reached address) := by
  intro next found
  cases result : callee.returned with
  | none => simp [result] at found
  | some entry =>
    have same : Callable.nested entry = next := by simpa [result] using found
    subst next
    unfold Callable.BodyRuns at ran
    rw [result] at ran
    exact invoked_value_at ran

private theorem plan_ready {globals : List String} {env exports : Environment}
    {commands : List Silmaril.Languages.Starlark.Modules.Resolve.Command}
    {code : List Modules.Command} {seed final program : Program}
    (profile : Plan globals env commands seed code final exports)
    (table : PreservesDeclarations final program) (ready : Ready globals program env) :
    Ready globals program exports := by
  induction profile with
  | done => exact ready
  | define root suffix ih =>
    have rootTable : PreservesDeclarations root.table program :=
      fun index decl found => table index decl (preserves suffix index decl found)
    exact ih table (ready_update ready root.site.target (some root.callable)
      (fun _ same => by cases same; exact root_linked rootTable))
  | assign member _ tracks _ ih =>
    apply ih table (ready_update ready member _ ?_)
    intro callee same
    cases tracks with
    | forget => cases same
    | copy tracked => cases same; exact (ready _ _ tracked).2
  | invoke call callee tracked _ ih =>
    exact ih table (ready_update ready call.destinationGlobal (callee.returned.map Callable.nested)
      (returned_linked (ready _ _ tracked).2))

private theorem read_global {globals : List String} {name : String} {state : State} {value : Value}
    (member : name ∈ globals) (loaded : state.bindingValue (globalSlot name) = .ok value) :
    Body.Evaluates (moduleLex globals) state (.scalar (.read name)) (Leaf.readOperand (globalSlot name))
      (.ok value state) := by
  have read := Body.Evaluates.read (state := state)
    (Assignment.ReadResolves.global (block := moduleLex globals) (by simp [moduleLex]) (by simp [moduleLex]) member)
  change Body.Evaluates (moduleLex globals) state (.scalar (.read name)) (Leaf.readOperand (globalSlot name))
    (state.read (.bound (globalSlot name))) at read
  rw [State.read, loaded] at read
  exact read

private theorem native_assignment (program : Program) (host : Catalog) (state : State) (name : String)
    (code : Lowering.Expr) (out : Outcome Value)
    (ran : ExecExpr program (List.range program.size) state code out) :
    Modules.Executes program host state (.exec (.assignExpr name code)) (afterWrite name out) := by
  cases out <;> exact .exec (code := .assignExpr name code) (.assignExpr ran)

private theorem copy_record {globals : List String} {env : Environment} {state middle : State}
    {source : Lowering.Resolve.SourceExpr} {code : Lowering.Expr} {entry : Option Callable} {value : Value}
    (tracks : Tracks env source code entry)
    (evaluated : Body.Evaluates (moduleLex globals) state source code (.ok value middle))
    (live : Live env state) :
    ∀ root, entry = some root → ∃ address defining, value = .function address ∧
      Nonempty (ClosureAt root.site root.id defining middle address) := by
  intro reached selected
  cases tracks with
  | forget => cases selected
  | copy lookup =>
    cases selected
    obtain ⟨address, defining, loaded, ⟨record⟩⟩ := live _ _ lookup
    generalize outcome : (EStateM.Result.ok value middle : Outcome Value) = result at evaluated
    cases evaluated with
    | read resolution =>
      rw [State.read, loaded] at outcome
      cases outcome
      exact ⟨address, defining, rfl, ⟨record⟩⟩

private theorem grow (state : State) (cell : Cell) :
    Body.Keeps state.heap.size state {state with heap := state.heap.push cell} := by
  exact ⟨rfl, fun address _ below old => by simp [Array.getElem?_push, Nat.ne_of_lt below, old]⟩

private abbrev Fresh (floor : Nat) (state : State) : Prop :=
  ∀ binding address, state.slots binding = some (.owned address) → floor ≤ address

private theorem fresh_after {floor : Nat} {state next : State} (fresh : Fresh floor state)
    (same : next.slots = state.slots) : Fresh floor next :=
  fun binding address found => fresh binding address (same ▸ found)

private theorem kept_below {floor : Nat} {state next : State} (kept : Body.Keeps state.heap.size state next) :
    Body.Keeps floor state next :=
  ⟨kept.1, fun address cell _ found => kept.2 address cell (Array.getElem?_eq_some_iff.mp found).choose found⟩

private theorem write_keeps {globals : List String} {state : State} {name : String} {floor : Nat}
    (frame : Frame globals state) (fresh : Fresh floor state) (member : name ∈ globals) (value : Value) :
    Body.Keeps floor state (state.write (globalSlot name) value) := by
  obtain ⟨slot, _, _, owned, _⟩ := frame.2 name member
  exact write_keeps_below owned (fresh _ _ owned) value

private theorem reached_definition {globals : List String} {env : Environment} {state : State}
    {floor : Nat} (root : Root globals) (program : Program) (host : Catalog)
    (found : program[root.id]? = some root.site.declaration)
    (frame : Frame globals state) (fresh : Fresh floor state) (live : Live env state)
    (tracked : ∀ name root, env name = some root → name ∈ globals) :
    ∃ out, Executes globals state root.command out ∧
      Modules.Executes program host state (.exec (.define root.site.name root.id)) out ∧
      Body.Keeps floor state (resultState out) ∧ (∀ next, out = .ok () next → Frame globals next ∧ Live (update env root.site.name (some root.callable)) next) := by
  obtain ⟨captures, installed, cells⟩ := root_captures root frame
  have lexical := lexical_defaults root.site root.lexical
  have ⟨keys, codes⟩ := default_layout root.site root.lexical
  obtain ⟨out, source, exec, _, _⟩ := Lexical.defines_for_total program (List.range program.size)
    (globalSlot root.site.name) root.id root.site.declaration lexical found keys codes state captures installed
  refine ⟨Modules.afterCode out, .define root captures installed source, .exec exec, ?_⟩
  cases source with
  | failed defaultRan =>
    exact ⟨kept_below (Lexical.evaluates_keeps lexical defaultRan), fun _ impossible => nomatch impossible⟩
  | @installed evaluated values liveCaptures defaultRan capturesRan =>
    have kept := Lexical.evaluates_keeps lexical defaultRan
    let saved := root.site.defaultKeys.zip values
    let cell : Cell := ⟨.function ⟨root.id, liveCaptures, saved⟩, false⟩
    let grown := {evaluated with heap := evaluated.heap.push cell}
    have retained : Body.Keeps state.heap.size state grown := Body.keeps_trans kept (kept_below (grow evaluated cell))
    have grownFrame := keep_frame frame retained
    refine ⟨Body.keeps_trans (kept_below retained)
      (write_keeps grownFrame (fresh_after fresh retained.1) root.site.target _), ?_⟩
    intro next success
    cases success
    have sameCaptures : liveCaptures = captures := Except.ok.inj
      ((installs_lookup evaluated capturesRan).symm.trans
        (installs_lookup evaluated (installs_in_same_slots kept.1 installed)))
    subst liveCaptures
    have captureLive := keep_captures cells kept
    let record : ClosureAt root.site root.id evaluated grown evaluated.heap.size :=
      ⟨captures, values, false, Lexical.evaluated_length lexical defaultRan,
        Array.getElem?_push_size, capturesRan, keep_captures captureLive (grow evaluated cell)⟩
    exact ⟨write_frame (.function evaluated.heap.size) grownFrame root.site.target,
      write_live grownFrame (keep_live frame live tracked retained) tracked root.site.target _
        (some root.callable) (fun known equal => by cases equal; exact ⟨_, _, rfl, ⟨record⟩⟩)⟩

private theorem run_plan {globals : List String} {env : Environment} {commands : List Silmaril.Languages.Starlark.Modules.Resolve.Command}
    {code : List Modules.Command} {seed final linked : Program} {exports : Environment} {all : List Silmaril.Languages.Starlark.Modules.Resolve.Command}
    {resolved : ResolvedModule} (checked : resolve all linked = .ok resolved)
    (profile : Plan globals env commands seed code final exports) (table : PreservesDeclarations final resolved.program)
    (host : Catalog) (state : State) (frame : Frame globals state) (ready : Ready globals resolved.program env)
    {floor : Nat} (fresh : Fresh floor state) (live : Live env state) :
    ∃ out, ExecutesAll globals state commands out ∧ Modules.Runs resolved.program host state code out ∧
      Body.Keeps floor state (resultState out) ∧ ∀ next, out = .ok () next → Ready globals resolved.program exports ∧ Live exports next := by
  induction profile generalizing state with
  | done => exact ⟨_, .done _, .done, ⟨rfl, fun _ _ _ found => found⟩, fun _ same => by cases same; exact ⟨ready, live⟩⟩
  | define root suffix ih =>
    have known : PreservesDeclarations root.table resolved.program :=
      fun id declaration found => table id declaration (preserves suffix id declaration found)
    obtain ⟨out, ran, native, preserved, kept⟩ :=
      reached_definition root resolved.program host (root_found known) frame fresh live (known_globals ready)
    cases out with
    | error error reached => exact ⟨_, .failed ran, .failed native, preserved, fun _ no => nomatch no⟩
    | ok result reached =>
      cases result
      have ⟨nextFrame, nextLive⟩ := kept _ rfl
      have nextReady := ready_update ready root.site.target (some root.callable)
        (fun _ same => by cases same; exact root_linked known)
      obtain ⟨out, rest, nativeRest, tailKeeps, completed⟩ :=
        ih table reached nextFrame nextReady (fresh_after fresh preserved.1) nextLive
      exact ⟨out, .step ran rest, .step native nativeRest, Body.keeps_trans preserved tailKeeps, completed⟩
  | @assign _ name source rhs reads entry _ _ _ _ _ member related tracks suffix ih =>
    obtain ⟨result, ran, kept⟩ := Body.operand_total related state
    have native : ExecExpr resolved.program (List.range resolved.program.size) state rhs result :=
      .evaluates (calls := fun _ _ _ => False) (fun _ _ _ impossible => impossible.elim)
        (Body.evaluates_with _ _ _ ran)
    cases result with
    | error error reached => exact ⟨_, .failed (.assign ran), .failed (native_assignment _ _ _ _ _ _ native), kept_below kept, fun _ no => nomatch no⟩
    | ok value reached =>
      have arrived := keep_frame frame kept
      have nextLive := write_live arrived (keep_live frame live (known_globals ready) kept)
        (known_globals ready) member value entry (copy_record tracks ran live)
      have nextReady := ready_update ready member entry (fun root equal => by
        cases tracks with
        | forget => cases equal
        | copy lookup => cases equal; exact (ready _ _ lookup).2)
      have saved := Body.keeps_trans (kept_below (floor := floor) kept)
        (write_keeps arrived (fresh_after fresh kept.1) member value)
      obtain ⟨out, sourceRest, nativeRest, tailKeeps, completed⟩ :=
        ih table _ (write_frame value arrived member) nextReady (fresh_after fresh saved.1) nextLive
      exact ⟨out, .step (.assign ran) sourceRest, .step (native_assignment _ _ _ _ _ _ native) nativeRest, Body.keeps_trans saved tailKeeps, completed⟩
  | invoke call callee tracked suffix ih =>
    have known := (ready _ _ tracked).2
    have found := known.1
    have permitted : callee.id ∈ List.range resolved.program.size :=
      List.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).choose
    obtain ⟨address, defining, loaded, ⟨record⟩⟩ := live _ _ tracked
    obtain ⟨result, ran, native, _, kept⟩ :=
      runs_at callee.site callee.BodyRuns checked callee.id found _ permitted (enter_callable checked known) (globalSlot call.callee)
        (read_global call.calleeGlobal loaded) record call.operands call.keywords call.star call.mapping
    cases result with
    | error error reached =>
      exact ⟨_, .failed (.invoke call callee ran), .failed (native_assignment _ _ _ _ _ _ native), kept_below kept, fun _ no => nomatch no⟩
    | ok value reached =>
      have arrived := keep_frame frame kept
      have nextLive := write_live arrived (keep_live frame live (known_globals ready) kept)
        (known_globals ready) call.destinationGlobal value (callee.returned.map Callable.nested)
        (returned_record ran)
      have nextReady := ready_update ready call.destinationGlobal (callee.returned.map Callable.nested) (returned_linked known)
      have saved := Body.keeps_trans (kept_below (floor := floor) kept)
        (write_keeps arrived (fresh_after fresh kept.1) call.destinationGlobal value)
      obtain ⟨out, sourceRest, nativeRest, tailKeeps, completed⟩ :=
        ih table _ (write_frame value arrived call.destinationGlobal) nextReady (fresh_after fresh saved.1) nextLive
      exact ⟨out, .step (.invoke call callee ran) sourceRest, .step (native_assignment _ _ _ _ _ _ native) nativeRest, Body.keeps_trans saved tailKeeps, completed⟩

private theorem published_lookup (state : State) (name : String) (value : Value)
    (publicName : Modules.isPublic name = true) (loaded : state.bindingValue (globalSlot name) = .ok value)
    {globals : List String} (member : name ∈ globals) :
    (Modules.publish ⟨globals, [], []⟩ state).1.exports.lookup name = some value := by
  change ((globals.filterMap fun name =>
    (state.bindingValue (globalSlot name)).toOption.map (fun value => (name, value))).filter
      (fun pair => Modules.isPublic pair.1)).lookup name = some value
  induction globals with
  | nil => cases member
  | cons first rest ih =>
    by_cases same : name = first
    · subst first
      simp [loaded, Except.toOption, publicName]
    · have different : (name == first) = false := by simpa using same
      have remains : name ∈ rest := (List.mem_cons.mp member).resolve_left same
      have result := ih remains
      cases previous : state.bindingValue (globalSlot first) with
      | error => simpa [previous, Except.toOption] using result
      | ok =>
        cases visible : Modules.isPublic first <;>
          simpa [previous, Except.toOption, visible, List.lookup, different] using result

theorem published_function {source : Modules.Source} {name : String} {state : State} {address : Nat}
    (member : name ∈ source.globals) (publicName : Modules.isPublic name = true)
    (loaded : state.bindingValue (globalSlot name) = .ok (.function address)) :
    (Modules.publish source state).1.exports.lookup name = some (.function address) := by
  obtain ⟨_, _, _⟩ := source
  exact published_lookup state name _ publicName loaded member

theorem publish_record {source : Modules.Source} {callee : Callable} {name : String}
    {state defining : State} {address : Nat} (caller : State) (member : name ∈ source.globals)
    (publicName : Modules.isPublic name = true) (loaded : state.bindingValue (globalSlot name) = .ok (.function address))
    (record : ClosureAt callee.site callee.id defining state address) :
    (Modules.publish source state).1.exports.lookup name = some (.function address) ∧
      ∃ published : ClosureAt callee.site callee.id defining
        (Modules.restoreThread caller (Modules.publish source state).2) address, published.frozen = true := by
  have global : (name, Lists.Value.function address) ∈ Modules.globalValues source state :=
    List.mem_filterMap.mpr ⟨name, member, by simp [loaded, Except.toOption]⟩
  have exported := published_function member publicName loaded
  let roots := (Modules.globalValues source state).map Prod.snd
  have root : address ∈ roots.filterMap Lists.Value.address? :=
    List.mem_filterMap.mpr ⟨_, List.mem_map_of_mem global, rfl⟩
  have frozen := (Lists.freezes_iff_freeze state.heap (roots.filterMap Lists.Value.address?) _).mpr rfl
  obtain ⟨flag, stored, iff⟩ := frozen.cell address _ record.recorded
  have yes := iff.mpr (Or.inr (.root (Array.getElem?_eq_some_iff.mp record.recorded).choose root))
  subst flag
  refine ⟨exported, { record with frozen := true, recorded := stored, live := ?_ }, rfl⟩
  intro capture member
  obtain ⟨value, _, cell⟩ := record.live capture member
  obtain ⟨flag, stored, _⟩ := frozen.cell capture.address _ cell
  exact ⟨value, flag, stored⟩

private theorem live_publication {globals : List String} {program : Program} {env : Environment}
    {source : Modules.Source} (names : source.globals = globals) (caller state : State)
    (ready : Ready globals program env) (live : Live env state) :
    PublishedLive env program (Modules.publish source state).1
      (Modules.restoreThread caller (Modules.publish source state).2) := by
  intro name callee known publicName
  obtain ⟨member, linked⟩ := ready name callee known
  obtain ⟨address, defining, loaded, ⟨record⟩⟩ := live name callee known
  obtain ⟨exported, published, frozen⟩ := publish_record caller (names.symm ▸ member) publicName loaded record
  exact ⟨linked, address, defining, exported, published, frozen⟩

theorem plan_globals {commands : List Silmaril.Languages.Starlark.Modules.Resolve.Command}
    {env exports : Environment} {code : List Modules.Command} {linked final : Program} {resolved : ResolvedModule}
    (profile : Plan (Trace.names commands) env commands linked code final exports)
    (checked : resolve commands linked = .ok resolved) :
    resolved.source.globals = Trace.names commands :=
  Entry.checked_module_globals (plan_declares profile) checked

theorem plan_code {commands : List Silmaril.Languages.Starlark.Modules.Resolve.Command}
    {env exports : Environment} {code : List Modules.Command} {linked final : Program} {resolved : ResolvedModule}
    (profile : Plan (Trace.names commands) env commands linked code final exports)
    (checked : resolve commands linked = .ok resolved) :
    resolved.source.commands = code ∧ resolved.program = final := by
  have declared := plan_declares profile
  have detail := checked_of_resolve checked
  have elaborated : elaborateCommands commands linked = .ok (code, final) := by
    rw [elaborateCommands, Block.moduleBlock_eq declared]
    exact plan_compiles profile
  exact Prod.mk.inj (Except.ok.inj (detail.1.symm.trans elaborated))

theorem plan_exports_linked {commands : List Silmaril.Languages.Starlark.Modules.Resolve.Command}
    {code : List Modules.Command} {linked final : Program} {resolved : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands linked code final exports)
    (checked : resolve commands linked = .ok resolved)
    {name : String} {callee : Callable} (tracked : exports name = some callee) :
    callee.Linked resolved.program := by
  have same := (plan_code profile checked).2
  have table : PreservesDeclarations final resolved.program := same ▸ fun _ _ found => found
  exact (plan_ready profile table (fun _ _ absent => nomatch absent) name callee tracked).2

theorem module_runs_extending {commands : List Silmaril.Languages.Starlark.Modules.Resolve.Command}
    {code : List Modules.Command} {linked final : Program} {resolved : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands linked code final exports)
    (checked : resolve commands linked = .ok resolved)
    {other : List Silmaril.Languages.Starlark.Modules.Resolve.Command} {seed : Program} {whole : ResolvedModule}
    (wholeChecked : resolve other seed = .ok whole)
    (extension : PreservesDeclarations resolved.program whole.program) (host : Catalog) (caller : State) :
    ∃ reached, ExecutesAll (Trace.names commands) (enter resolved.source caller) commands reached ∧
      Modules.Runs whole.program host (enter resolved.source caller) resolved.source.commands reached ∧
      KeepsContents caller (resultState (finish resolved.source caller reached)) ∧
      ∀ published finished, finish resolved.source caller reached = .ok published finished →
        PublishedLive exports whole.program published finished := by
  have declared := plan_declares profile
  obtain ⟨sameCode, sameTable⟩ := plan_code profile checked
  have table : PreservesDeclarations final whole.program := by
    exact sameTable ▸ extension
  have entered := Entry.entered_cells resolved.source caller
  obtain ⟨reached, source, ran, preserved, completed⟩ := run_plan wholeChecked profile table host _ (entry_frame declared checked caller)
    (fun _ _ no => nomatch no) entered.1 (fun _ _ no => nomatch no)
  have native : Modules.Runs whole.program host (enter resolved.source caller) resolved.source.commands reached := by
    rw [sameCode]
    exact ran
  refine ⟨reached, source, native, ?_, ?_⟩
  · intro address cell present
    have old := preserved.2 address cell (Array.getElem?_eq_some_iff.mp present).choose (entered.2 _ _ present)
    cases reached with
    | error => exact ⟨cell.frozen, by simpa [finish, resultState, Modules.restoreThread, restoreCaller] using old⟩
    | ok result state =>
      cases result
      have frozen := (Lists.freezes_iff_freeze state.heap
        (((Modules.globalValues resolved.source state).map Prod.snd).filterMap Lists.Value.address?) _).mpr rfl
      obtain ⟨flag, stored, _⟩ := frozen.cell address cell old
      exact ⟨flag, stored⟩
  · intro published finished success
    cases reached with
    | error => cases success
    | ok result state =>
      cases result
      cases success
      obtain ⟨ready, live⟩ := completed _ rfl
      exact live_publication (Entry.checked_module_globals declared checked) caller state ready live

theorem module_agrees_preserving {commands : List Silmaril.Languages.Starlark.Modules.Resolve.Command}
    {code : List Modules.Command} {linked final : Program} {resolved : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands linked code final exports)
    (checked : resolve commands linked = .ok resolved) (host : Catalog) (caller : State) :
    ∃ reached, ExecutesAll (Trace.names commands) (enter resolved.source caller) commands reached ∧
      Modules.Runs resolved.program host (enter resolved.source caller) resolved.source.commands reached ∧
      Modules.Initializes resolved.program host resolved.source caller (finish resolved.source caller reached) ∧
      runModule commands host caller linked = .ok (finish resolved.source caller reached) ∧
      KeepsContents caller (resultState (finish resolved.source caller reached)) ∧
      ∀ published finished, finish resolved.source caller reached = .ok published finished →
        PublishedLive exports resolved.program published finished := by
  obtain ⟨reached, source, native, kept, live⟩ :=
    module_runs_extending profile checked checked (fun _ _ stored => stored) host caller
  have initialized : Modules.Initializes resolved.program host resolved.source caller (finish resolved.source caller reached) :=
    .run (checked_of_resolve checked).2.2.2 native
  exact ⟨reached, source, native, initialized,
    (initializes_iff_runModule _ _ _ _ _).mp (.run checked initialized), kept, live⟩

theorem module_agrees {commands : List Silmaril.Languages.Starlark.Modules.Resolve.Command}
    {code : List Modules.Command} {linked final : Program} {resolved : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands linked code final exports)
    (checked : resolve commands linked = .ok resolved) (host : Catalog) (caller : State) :
    ∃ reached, ExecutesAll (Trace.names commands) (enter resolved.source caller) commands reached ∧
      Modules.Runs resolved.program host (enter resolved.source caller) resolved.source.commands reached ∧
      Modules.Initializes resolved.program host resolved.source caller (finish resolved.source caller reached) ∧
      runModule commands host caller linked = .ok (finish resolved.source caller reached) ∧
      ∀ published finished, finish resolved.source caller reached = .ok published finished →
        PublishedLive exports resolved.program published finished := by
  obtain ⟨reached, source, native, initialized, exactRun, _, published⟩ :=
    module_agrees_preserving profile checked host caller
  exact ⟨reached, source, native, initialized, exactRun, published⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
