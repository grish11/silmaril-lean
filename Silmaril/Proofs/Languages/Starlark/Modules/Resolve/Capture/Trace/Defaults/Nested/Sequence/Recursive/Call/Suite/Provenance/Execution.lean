module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.Invariant
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.Elaboration
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall (DistinctOwned)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive (Site Emissions site_slots lexical_defaults default_layout)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call (BodyEntry)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite (Runs)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Outcome Capture Value)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow finishState)

private def Dispatchable {block : LexicalBlock} (program : Program) (available : List DeclarationId)
    (entry : Entry block) : Prop :=
  program[entry.id]? = some entry.site.declaration ∧ entry.id ∈ available ∧
    BodyEntry entry.site program available entry.id
      (fun state out => Runs entry.site.block state entry.site.source entry.site.body.code out)

private def Ready {block : LexicalBlock} (program : Program) (available : List DeclarationId) (locals : Locals block) : Prop :=
  ∀ name entry, locals name = some entry → Dispatchable program available entry

private theorem ready_updated {block : LexicalBlock} {program : Program} {available : List DeclarationId}
    {locals : Locals block} (ready : Ready program available locals) (name : String) (updated : Option (Entry block))
    (new : ∀ entry, updated = some entry → Dispatchable program available entry) :
    Ready program available (setLocal locals name updated) := by
  intro read entry found
  by_cases same : read = name
  · exact new entry (by simpa [setLocal, same] using found)
  · exact ready read entry (by simpa [setLocal, same] using found)

private abbrev Correspondence (program : Program) (available : List DeclarationId) : Prop :=
  ∀ {block : LexicalBlock} {locals : Locals block} {source : Statement} {seed final : Program}
    {code : ResolvedBody} {emissions : Emissions},
    Elaborates block locals source seed code final emissions → PreservesDeclarations final program →
    List.Subset (emissions.map Prod.fst) available → Ready program available locals →
    ∀ {before after : List Binding} {free : List FreeName},
    Selects block (before ++ code.reads ++ after) free →
    ∀ (state : State) {floor : Nat}, Body.Frame block free floor state → DistinctOwned state → Live locals state →
    ∃ out, Runs block state source code.code out ∧ Body.Frame block free floor (finishState out) ∧
      Body.Keeps floor state (finishState out) ∧ Exec program available state code.code out

private theorem activate_frame {parent : LexicalBlock} {formals : List PlainKeywordParameter} {varargs kwargs : Option String}
    (site : Site parent formals varargs kwargs) (caller defining : State)
    (captures : List Capture) (installed : Installs defining site.free captures)
    (live : Body.CaptureCells caller captures) (assigned : List (Binding × Value)) :
    Body.Frame site.block site.free caller.heap.size (activate caller site.declaration captures assigned) :=
  Body.selected_frame site.block site.declaration (site_slots site) site.selects caller defining captures installed live assigned

private theorem distinct_of_slots {state next : State} (same : next.slots = state.slots)
    (distinct : DistinctOwned state) : DistinctOwned next := by
  unfold DistinctOwned
  rw [same]
  exact distinct

private theorem trim_keep {floor : Nat} {state next : State} (kept : Body.Keeps state.heap.size state next) :
    Body.Keeps floor state next :=
  ⟨kept.1, fun address cell _ found => kept.2 address cell (Array.getElem?_eq_some_iff.mp found).choose found⟩

private theorem runs_guarded {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (available : List DeclarationId) :
    Correspondence resolved.program available := by
  induction available using withoutDeclaration_induction with
  | step available smaller =>
    intro block locals source seed final code emissions profile table guarded ready before after free stateSelection state floor frame distinct live
    let program := resolved.program
    induction profile generalizing before after free state with
    | plain ordinary =>
      obtain ⟨out, trace, nextFrame, kept, exec, _⟩ :=
        Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.runs
          ordinary program table available stateSelection state frame
      exact ⟨out, .plain trace, nextFrame, kept, exec⟩
    | @assign block locals name source rhs reads entry rest seed tail final emissions owned operand tracked _ ih =>
      have selection : Selects block ((before ++ reads) ++ tail.reads ++ after) free := by
        simpa only [List.append_assoc] using stateSelection
      obtain ⟨result, trace, kept⟩ := Body.operand_total operand state
      have reached : Body.Frame block free floor (finishState result) := Body.frame_preserved frame kept
      have evaluates : ExecExpr program available state rhs result :=
        .evaluates (calls := fun _ _ _ => False) (fun _ _ _ impossible => impossible.elim)
          (Body.evaluates_with _ _ _ trace)
      cases result with
      | error error stopped =>
        have sourceTrace := Runs.assignments (leading := [(name, source)]) (code := [(name, rhs)])
          (rest := rest) (tail := tail.code) (.failed trace) (out := .error error stopped) (fun _ no => nomatch no)
        exact ⟨_, sourceTrace, reached, trim_keep kept, .seqError (.assignExpr evaluates)⟩
      | ok value middle =>
        have nextLive := assigned_live tracked trace kept live distinct reached owned
        have nextReady : Ready program available (setLocal locals name entry) :=
          ready_updated ready name entry (fun known same => by
            cases tracked with
            | forget => cases same
            | copy _ seen => cases same; exact ready _ _ seen)
        have ⟨written, keptWrite⟩ := Body.written_frame owned value reached
        have retained := Body.keeps_trans (trim_keep kept) keptWrite
        have nextDistinct : DistinctOwned (middle.write (fileSlot name) value) := distinct_of_slots retained.1 distinct
        obtain ⟨out, tailTrace, finalFrame, last, tailExec⟩ :=
          ih table guarded nextReady selection _ written nextDistinct nextLive
        have sourceTrace := Runs.assignments (leading := [(name, source)]) (code := [(name, rhs)])
          (rest := rest) (tail := tail.code) (.cons trace .nil)
          (fun _ same => by cases same; exact tailTrace)
        exact ⟨out, sourceTrace, finalFrame, Body.keeps_trans retained last, .seq (.assignExpr evaluates) tailExec⟩
    | @define block locals rest seed childTable tail final descendants later formals varargs kwargs site kw child suffix _ ih =>
      have selectedDefinition : Selects block (before ++ site.reads ++ (tail.reads ++ after)) free := by
        simpa only [List.append_assoc] using stateSelection
      have selectedTail : Selects block ((before ++ site.reads) ++ tail.reads ++ after) free := by
        simpa only [List.append_assoc] using stateSelection
      have found := table _ _ ((links suffix).1 _ _ Array.getElem?_push_size)
      have permitted : childTable.size ∈ available :=
        guarded (List.mem_map.mpr ⟨_, List.mem_append_right _ List.mem_cons_self, rfl⟩)
      have childLinked : PreservesDeclarations childTable program := by
        intro id entry previous
        have below := (Array.getElem?_eq_some_iff.mp previous).choose
        exact table _ _ ((links suffix).1 _ _ (by simp [Array.getElem?_push, Nat.ne_of_lt below, previous]))
      have childGuard : List.Subset (descendants.map Prod.fst) (withoutDeclaration available childTable.size) := by
        intro id used
        obtain ⟨entry, emitted, rfl⟩ := List.mem_map.mp used
        exact mem_withoutDeclaration.mpr ⟨
          guarded (List.mem_map.mpr ⟨entry, List.mem_append_left _ emitted, rfl⟩),
          Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp ((links child).2 entry emitted)).choose⟩
      have nextReady : Ready program available (setLocal locals site.name (some ⟨childTable.size, formals, varargs, kwargs, site⟩)) := by
        apply ready_updated ready
        intro entry same
        cases same
        refine ⟨found, permitted, ?_⟩
        intro caller defining captures installed liveCells assigned
        have activeFrame := activate_frame site caller defining captures installed liveCells assigned
        have childSelection : Selects site.block ([] ++ site.body.reads ++ []) site.free := by
          simpa [Site.block] using site.selects
        obtain ⟨out, trace, _, kept, exec⟩ :=
          smaller childTable.size permitted child childLinked childGuard (fun _ _ no => nomatch no)
            childSelection _ activeFrame (RootCall.activation_distinct _ _ _ _) (empty_live _)
        exact ⟨out, trace, exec, Body.returned_keeps caller site.declaration captures assigned out kept⟩
      have tailGuard : List.Subset (later.map Prod.fst) available := by
        intro id used
        obtain ⟨entry, emitted, rfl⟩ := List.mem_map.mp used
        exact guarded (List.mem_map.mpr ⟨entry, List.mem_append_right _ (List.mem_cons_of_mem _ emitted), rfl⟩)
      obtain ⟨captures, receipts, cells⟩ :=
        Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.installs
          site selectedDefinition frame
      have lexical := lexical_defaults site kw
      have ⟨keys, codes⟩ := default_layout site kw
      obtain ⟨result, _, exec, _, step⟩ :=
        Nested.reached_site_for site.target lexical program available childTable.size site.declaration found keys codes
          frame captures receipts
      have ⟨reached, kept⟩ := Nested.site_result_frame_for site.target lexical frame step
      cases result with
      | error error stopped =>
        exact ⟨_, .define receipts step (out := .error error stopped) (fun _ no => nomatch no), reached, kept, .seqError exec⟩
      | ok flow installed =>
        have next : flow = .next := by cases step; rfl
        subst flow
        have nextDistinct : DistinctOwned installed := distinct_of_slots kept.1 distinct
        obtain ⟨out, trace, finalFrame, last, tailExec⟩ :=
          ih table tailGuard nextReady selectedTail installed reached nextDistinct
            (installed_live site kw _ receipts cells step live distinct frame)
        exact ⟨out, .define receipts step (fun _ same => by cases same; exact trace),
          finalFrame, Body.keeps_trans kept last, .seq exec tailExec⟩
    | @invoke block locals rest seed tail final emissions call entry tracked _ ih =>
      have selectedTail : Selects block ((before ++ call.reads) ++ tail.reads ++ after) free := by
        simpa only [List.append_assoc] using stateSelection
      obtain ⟨found, permitted, enter⟩ := ready call.callee entry tracked
      obtain ⟨address, defining, callee, ⟨record⟩⟩ := evaluated_local live tracked call.calleeOwned
      obtain ⟨result, ran, exec, _, kept⟩ :=
        Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.runs
          entry.site _ checked entry.id found available permitted enter callee record call.operands call.keywords call.star call.mapping
      have reached := Body.frame_preserved frame kept
      cases result with
      | error error stopped =>
        exact ⟨_, .invoke (star := call.star) (mapping := call.mapping) ran (fun _ _ child => child) (out := .error error stopped) (fun _ _ no => nomatch no),
          reached, trim_keep kept, .seqError (.assignExpr exec)⟩
      | ok value returned =>
        have nextReady := ready_updated ready call.destination none (fun _ no => nomatch no)
        have returnedDistinct : DistinctOwned returned := distinct_of_slots kept.1 distinct
        have ⟨written, keptWrite⟩ := Body.written_frame call.destinationOwned value reached
        have retained := Body.keeps_trans (trim_keep kept) keptWrite
        have nextDistinct : DistinctOwned (returned.write (fileSlot call.destination) value) :=
          distinct_of_slots retained.1 distinct
        have nextLive := write_live (name := call.destination) (entry := none) value returnedDistinct
          (keeps_live live kept) (fun _ no => nomatch no)
        obtain ⟨out, trace, finalFrame, last, tailExec⟩ :=
          ih table guarded nextReady selectedTail _ written nextDistinct nextLive
        exact ⟨out, .invoke (star := call.star) (mapping := call.mapping) ran (fun _ _ child => child) (fun _ _ same => by cases same; exact trace),
          finalFrame, Body.keeps_trans retained last, .seq (.assignExpr exec) tailExec⟩

theorem runs {block : LexicalBlock} {source : Statement} {seed final : Program}
    {code : ResolvedBody} {emissions : Emissions} (profile : Elaborates block empty source seed code final emissions)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (table : PreservesDeclarations final resolved.program)
    (available : List DeclarationId) (guarded : List.Subset (emissions.map Prod.fst) available)
    {before after : List Binding} {free : List FreeName} (selected : Selects block (before ++ code.reads ++ after) free)
    (state : State) {floor : Nat} (frame : Body.Frame block free floor state) (distinct : DistinctOwned state) :
    ∃ out, Runs block state source code.code out ∧ Body.Frame block free floor (finishState out) ∧
      Body.Keeps floor state (finishState out) ∧ Exec resolved.program available state code.code out ∧
      denoteBody resolved.program available code.code state = out := by
  obtain ⟨out, trace, lastFrame, kept, exec⟩ :=
    runs_guarded checked available profile table guarded (fun _ _ no => nomatch no) selected state frame distinct (empty_live _)
  exact ⟨out, trace, lastFrame, kept, exec, (exec_iff_denoteBody _ _ _ _ _).mp exec⟩

theorem runs_activated {parent : LexicalBlock} {formals : List PlainKeywordParameter} {varargs kwargs : Option String}
    (site : Site parent formals varargs kwargs) {seed final : Program} {emissions : Emissions}
    (profile : Elaborates site.block empty site.source seed site.body final emissions)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (table : PreservesDeclarations final resolved.program)
    (available : List DeclarationId) (guarded : List.Subset (emissions.map Prod.fst) available)
    (caller defining : State) (captures : List Capture) (installed : Installs defining site.free captures)
    (live : Body.CaptureCells caller captures) (assigned : List (Binding × Value)) :
    let active := activate caller site.declaration captures assigned
    ∃ out, Runs site.block active site.source site.body.code out ∧
      Body.Frame site.block site.free caller.heap.size (finishState out) ∧
      Body.Keeps caller.heap.size active (finishState out) ∧
      Exec resolved.program available active site.body.code out ∧
      denoteBody resolved.program available site.body.code active = out := by
  have selected : Selects site.block ([] ++ site.body.reads ++ []) site.free := by
    simpa [Site.block] using site.selects
  exact runs profile checked table available guarded selected _
    (activate_frame site caller defining captures installed live assigned) (RootCall.activation_distinct _ _ _ _)

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance
