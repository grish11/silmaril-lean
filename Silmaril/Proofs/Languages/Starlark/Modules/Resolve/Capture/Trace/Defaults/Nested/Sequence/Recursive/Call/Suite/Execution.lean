module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Elaboration
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive (Site Emissions)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Outcome Capture Value)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow finishState)

private theorem run_definition {block : LexicalBlock} (site : Site block) (program : Program)
    (available : List DeclarationId) {id : DeclarationId} (found : program[id]? = some site.declaration)
    {before after : List Binding} {free : List FreeName}
    (selected : Selects block (before ++ site.reads ++ after) free)
    {state : State} {floor : Nat} (frame : Body.Frame block free floor state)
    {rest : Statement} {tail : Body}
    (continuation : ∀ (captures : List Capture) (installed : State), Installs state site.free captures →
      Body.CaptureCells state captures →
      Nested.SiteResult block site.name site.parameters site.defaults id captures state (.ok .next installed) →
      Body.Frame block free floor installed →
      ∃ out, Runs block installed rest tail out ∧ Body.Frame block free floor (finishState out) ∧
        Body.Keeps floor installed (finishState out) ∧ Exec program available installed tail out) :
    ∃ out, Runs block state (.seq site.statement rest) (.seq (.define (fileSlot site.name) id) tail) out ∧
      Body.Frame block free floor (finishState out) ∧ Body.Keeps floor state (finishState out) ∧
      Exec program available state (.seq (.define (fileSlot site.name) id) tail) out := by
  obtain ⟨captures, receipts, live⟩ := Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.installs site selected frame
  obtain ⟨out, _, exec, _, result⟩ :=
    Nested.reached_site site.target site.lexical program available id site.declaration found rfl frame captures receipts
  have ⟨nextFrame, kept⟩ := Nested.site_result_frame site.target site.lexical frame result
  cases out with
  | error error stopped =>
    exact ⟨_, .define receipts result (out := .error error stopped) (fun _ impossible => nomatch impossible),
      nextFrame, kept, .seqError exec⟩
  | ok flow installed =>
    have next : flow = .next := by cases result; rfl
    subst flow
    obtain ⟨out, trace, lastFrame, retained, native⟩ :=
      continuation captures installed receipts live result nextFrame
    exact ⟨out, .define receipts result (fun _ same => by cases same; exact trace),
      lastFrame, Body.keeps_trans kept retained, .seq exec native⟩

private theorem run_call {block : LexicalBlock} (site : Site block) (assignment : Assignment block)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved)
    (available : List DeclarationId) {id : DeclarationId} (permitted : id ∈ available)
    (found : resolved.program[id]? = some site.declaration)
    (enter : Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.BodyEntry site resolved.program available id
      (fun state out => Runs site.block state site.source site.body.code out))
    {defining installed : State} {captures : List Capture}
    (receipts : Installs defining site.free captures) (live : Body.CaptureCells defining captures)
    (step : Nested.SiteResult block site.name site.parameters site.defaults id captures defining (.ok .next installed))
    {free : List FreeName} {floor : Nat} (frame : Body.Frame block free floor installed)
    {rest : Statement} {tail : Body}
    (continuation : ∀ state, Body.Frame block free floor state →
      ∃ out, Runs block state rest tail out ∧ Body.Frame block free floor (finishState out) ∧
        Body.Keeps floor state (finishState out) ∧ Exec resolved.program available state tail out) :
    ∃ out, Runs block installed (assignment.source site.name rest) (assignment.code site.name tail) out ∧
      Body.Frame block free floor (finishState out) ∧ Body.Keeps floor installed (finishState out) ∧
      Exec resolved.program available installed (assignment.code site.name tail) out := by
  obtain ⟨address, result, first, _, called, native, _, kept⟩ :=
    Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.runs_installed_alias_preserving_with
      site _ checked id found available permitted enter step receipts live
      assignment.copyOwned assignment.copyLegal frame assignment.operands
  let copied := installed.write (fileSlot assignment.copy) (.function address)
  have copiedStep : Exec resolved.program available installed
      (.assignExpr (fileSlot assignment.copy) (Leaf.readOperand (fileSlot site.name))) (.ok .next copied) :=
    .assignExpr (.evaluates (calls := fun _ _ _ => False) (fun _ _ _ impossible => impossible.elim)
      (Body.evaluates_with _ _ _ first))
  have ⟨copiedFrame, keptCopy⟩ := Body.written_frame assignment.copyOwned (.function address) frame
  have reached := Body.frame_preserved copiedFrame kept
  have retained : Body.Keeps floor installed (finishState result) :=
    Body.keeps_trans keptCopy ⟨kept.1, fun address cell _ found =>
      kept.2 address cell (Array.getElem?_eq_some_iff.mp found).choose found⟩
  cases result with
  | error error stopped =>
    exact ⟨_, .call first called (fun _ _ child => child) (out := .error error stopped) (fun _ _ no => nomatch no),
      reached, retained, .seq copiedStep (.seqError (.assignExpr native))⟩
  | ok value returned =>
    have ⟨written, keptWrite⟩ := Body.written_frame assignment.destinationOwned value reached
    obtain ⟨out, source, finalFrame, keptTail, tailExec⟩ := continuation _ written
    exact ⟨out, .call first called (fun _ _ child => child) (fun _ _ same => by cases same; exact source),
      finalFrame, Body.keeps_trans retained (Body.keeps_trans keptWrite keptTail),
      .seq copiedStep (.seq (.assignExpr native) tailExec)⟩

private theorem activate_frame {parent : LexicalBlock} (site : Site parent) (caller defining : State)
    (captures : List Capture) (installed : Installs defining site.free captures)
    (live : Body.CaptureCells caller captures) (assigned : List (Binding × Value)) :
    Body.Frame site.block site.free caller.heap.size (activate caller site.declaration captures assigned) := by
  have length : (site.defaults.map PlainPositionalDefault.value).length = site.parameters.optional.length := by
    simpa using congrArg List.length (Lexical.translates site.lexical).1
  exact Body.selected_frame site.block site.declaration
    (Body.signature_slots site.parameters site.locals _ length) site.selects caller defining captures installed live assigned

private abbrev Correspondence (program : Program) (available : List DeclarationId) : Prop :=
  ∀ {block : LexicalBlock} {source : Statement} {seed final : Program}
    {code : ResolvedBody} {emitted : Emissions} {calls : List DeclarationId},
    Elaborates block source seed code final emitted calls → PreservesDeclarations final program →
    List.Subset calls available →
    ∀ {before after : List Binding} {free : List FreeName},
    Selects block (before ++ code.reads ++ after) free →
    ∀ (state : State) {floor : Nat}, Body.Frame block free floor state →
    ∃ out, Runs block state source code.code out ∧ Body.Frame block free floor (finishState out) ∧
      Body.Keeps floor state (finishState out) ∧ Exec program available state code.code out ∧
      denoteBody program available code.code state = out

private theorem runs_guarded {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (available : List DeclarationId) :
    Correspondence resolved.program available := by
  induction available using withoutDeclaration_induction with
  | step available smaller =>
    intro block source seed final code emitted calls profile table guarded before after free selected state floor frame
    let program := resolved.program
    induction profile generalizing before after free state with
    | plain ordinary =>
      obtain ⟨out, trace, nextFrame, kept, exec, meaning⟩ :=
        Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.runs ordinary program table available selected state frame
      exact ⟨out, .plain trace, nextFrame, kept, exec, meaning⟩
    | @assignments block leading leadingCode leadingReads rest seed final tail emitted calls prefixProfile _ ih =>
      have selectedTail : Selects block ((before ++ leadingReads) ++ tail.reads ++ after) free := by
        simpa only [List.append_assoc] using selected
      obtain ⟨prefixOut, trace, entered, kept⟩ := Body.prefix_total prefixProfile state frame
      cases prefixOut with
      | error error stopped =>
        have ⟨exec, meaning⟩ := Body.prefix_agrees program available trace tail.code (.error error stopped)
          (fun _ no => nomatch no)
        exact ⟨_, .assignments trace (out := .error error stopped) (fun _ no => nomatch no),
          entered, kept, exec, meaning⟩
      | ok done enteredState =>
        cases done
        obtain ⟨out, tailTrace, finalFrame, retained, _, denoted⟩ := ih table guarded selectedTail enteredState entered
        have ⟨exec, meaning⟩ := Body.prefix_agrees program available trace tail.code out
          (fun _ same => by cases same; exact denoted)
        exact ⟨out, .assignments trace (fun _ same => by cases same; exact tailTrace),
          finalFrame, Body.keeps_trans kept retained, exec, meaning⟩
    | @define block rest seed childTable final tail descendants later calls childCalls site _ suffix _ ih =>
      have selectedDefinition : Selects block (before ++ site.reads ++ (tail.reads ++ after)) free := by
        simpa only [List.append_assoc] using selected
      have selectedTail : Selects block ((before ++ site.reads) ++ tail.reads ++ after) free := by
        simpa only [List.append_assoc] using selected
      have found := table _ _ ((links suffix).1 _ _ Array.getElem?_push_size)
      obtain ⟨out, trace, nextFrame, kept, exec⟩ :=
        run_definition site program available found selectedDefinition frame (fun _ installed _ _ _ reached => by
          obtain ⟨out, trace, nextFrame, kept, exec, _⟩ := ih table guarded selectedTail installed reached
          exact ⟨out, trace, nextFrame, kept, exec⟩)
      exact ⟨out, trace, nextFrame, kept, exec, (exec_iff_denoteBody _ _ _ _ _).mp exec⟩
    | @call block rest seed childTable final tail descendants later calls childCalls site _ assignment child suffix _ ih =>
      have selectedDefinition :
          Selects block (before ++ site.reads ++ (assignment.reads site.name ++ tail.reads ++ after)) free := by
        simpa only [List.append_assoc] using selected
      have selectedTail :
          Selects block ((before ++ site.reads ++ assignment.reads site.name) ++ tail.reads ++ after) free := by
        simpa only [List.append_assoc] using selected
      have found := table _ _ ((links suffix).1 _ _ Array.getElem?_push_size)
      have childLinked : PreservesDeclarations childTable program := by
        intro id entry previous
        have within := (Array.getElem?_eq_some_iff.mp previous).choose
        exact table _ _ ((links suffix).1 _ _ (by simp [Array.getElem?_push, Nat.ne_of_lt within, previous]))
      have permitted : childTable.size ∈ available := guarded List.mem_cons_self
      have nestedGuard : List.Subset childCalls (withoutDeclaration available childTable.size) :=
        child_available child (fun id used => guarded (List.mem_cons_of_mem _ (List.mem_append_left calls used)))
      have tailGuard : List.Subset calls available := fun id used =>
        guarded (List.mem_cons_of_mem _ (List.mem_append_right childCalls used))
      have enter : Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.BodyEntry site program available childTable.size
          (fun active out => Runs site.block active site.source site.body.code out) := by
        intro caller defining captures installed live assigned
        have activeFrame := activate_frame site caller defining captures installed live assigned
        have childSelection : Selects site.block ([] ++ site.body.reads ++ []) site.free := by
          simpa [Site.block] using site.selects
        obtain ⟨out, trace, _, kept, operated, _⟩ :=
          smaller childTable.size permitted child childLinked nestedGuard childSelection _ activeFrame
        exact ⟨out, trace, operated, Body.returned_keeps caller site.declaration captures assigned out kept⟩
      obtain ⟨out, trace, nextFrame, kept, exec⟩ :=
        run_definition site program available found selectedDefinition frame (fun _ _ receipts live step reached =>
          run_call site assignment checked available permitted found enter receipts live step reached (fun active activeFrame => by
            obtain ⟨out, trace, nextFrame, kept, exec, _⟩ := ih table tailGuard selectedTail active activeFrame
            exact ⟨out, trace, nextFrame, kept, exec⟩))
      exact ⟨out, trace, nextFrame, kept, exec, (exec_iff_denoteBody _ _ _ _ _).mp exec⟩

theorem runs {block : LexicalBlock} {source : Statement} {seed final : Program}
    {code : ResolvedBody} {emitted : Emissions} {calls : List DeclarationId}
    (profile : Elaborates block source seed code final emitted calls)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (table : PreservesDeclarations final resolved.program)
    (available : List DeclarationId) (guarded : List.Subset calls available)
    {before after : List Binding} {free : List FreeName} (selected : Selects block (before ++ code.reads ++ after) free)
    (state : State) {floor : Nat} (frame : Body.Frame block free floor state) :
    ∃ out, Runs block state source code.code out ∧ Body.Frame block free floor (finishState out) ∧
      Body.Keeps floor state (finishState out) ∧ Exec resolved.program available state code.code out ∧
      denoteBody resolved.program available code.code state = out :=
  runs_guarded checked available profile table guarded selected state frame

theorem runs_activated {parent : LexicalBlock} (site : Site parent) {seed final : Program}
    {emitted : Emissions} {calls : List DeclarationId}
    (profile : Elaborates site.block site.source seed site.body final emitted calls)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (table : PreservesDeclarations final resolved.program)
    (available : List DeclarationId) (guarded : List.Subset calls available)
    (caller defining : State) (captures : List Capture) (installed : Installs defining site.free captures)
    (live : Body.CaptureCells caller captures)
    (assigned : List (Binding × Silmaril.Languages.Starlark.Lists.Value)) :
    let active := activate caller site.declaration captures assigned
    ∃ out, Runs site.block active site.source site.body.code out ∧
      Body.Frame site.block site.free caller.heap.size (finishState out) ∧
      Body.Keeps caller.heap.size active (finishState out) ∧
      Exec resolved.program available active site.body.code out ∧
      denoteBody resolved.program available site.body.code active = out := by
  have frame := activate_frame site caller defining captures installed live assigned
  have selected : Selects site.block ([] ++ site.body.reads ++ []) site.free := by
    simpa [Site.block] using site.selects
  exact runs profile checked table available guarded selected _ frame

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite
