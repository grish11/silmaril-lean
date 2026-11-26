module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defaults.State

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults

open Silmaril.Languages.Starlark.Modules (globalSlot fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Block (ModuleBinders)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body (Definition Admitted)
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (Cell State)

theorem define_body {before after : List Command} {definition : Definition} {globals : List String}
    {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ definition.command :: after) globals)
    (checked : resolve (before ++ definition.command :: after) linked = .ok resolved)
    (admitted : Admitted globals definition) (suffix : RootCall.Segment globals after)
    (known : Visible globals definition.name) {state : State} (layout : ModuleSlots globals state) :
    ∃ out, Step resolved globals before.length state definition.command out ∧
      (∀ next, out = .ok () next → Bindings.Writes state definition.name next ∧
        LiveBinding globals resolved.program next definition.name (.sequenced definition)) := by
  obtain ⟨plan, codes, emitted, length, evaluates⟩ := Defaults.Body.emission admitted
  obtain ⟨id, site, found⟩ := RootCall.checked_single_emission before after _ definition.name globals linked resolved
    (plan.declaration codes) declared checked suffix emitted
  obtain ⟨out, ran, kept⟩ := evaluates state
  cases out with
  | error error final =>
    exact ⟨.error (.runtime error) final, .bodyDefinition plan site found length (.failed ran),
      fun _ impossible => nomatch impossible⟩
  | ok values final =>
    have kept := kept values final rfl
    obtain ⟨captures, installs⟩ := Defaults.Body.instantiates plan final (kept.layout layout)
    let saved := (definition.parameters.optional.map (fileSlot ∘ Prod.fst)).zip values
    let cell : Cell := ⟨.function ⟨id, captures, saved⟩, false⟩
    let grown : State := { final with heap := final.heap.push cell }
    let keep := kept.trans (Bindings.Preserves.push final cell)
    let next := grown.write (globalSlot definition.name) (.function final.heap.size)
    have live := commit_cell known.1 (keep.layout layout) final.heap.size id captures saved
      (show grown.heap[final.heap.size]? = some cell from Array.getElem?_push_size)
    have valueLength : values.length = definition.parameters.optional.length := by
      simpa only [List.length_map] using Defaults.evaluated_length ran
    have cells := Defaults.Body.root_capture_cells plan final (kept.layout layout) captures installs
    have throughPush := Defaults.Body.capture_cells_preserved (Bindings.Preserves.push final cell) cells
    have current := Defaults.Body.capture_cells_written grown (globalSlot definition.name) (.function final.heap.size) throughPush
    refine ⟨.ok () next, .bodyDefinition plan site found length (.installed ran installs), ?_⟩
    intro finish same
    cases same
    exact ⟨.commit grown _ keep, ⟨known.1, ⟨⟨id, [], plan, codes, final.heap.size, values, captures, length,
      valueLength, found, final, installs, current, live⟩⟩⟩⟩

theorem alias_body {before rest : List Command} {globals : List String} {source destination : String}
    {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ .assign destination (.scalar (.read source)) :: rest) globals)
    (checked : resolve (before ++ .assign destination (.scalar (.read source)) :: rest) linked = .ok resolved)
    (sourceKnown : Visible globals source) (destinationKnown : Visible globals destination)
    {state : State} {definition : Definition} (saved : SavedBody globals resolved.program state source definition)
    (layout : ModuleSlots globals state) :
    ∃ next, Step resolved globals before.length state (.assign destination (.scalar (.read source))) (.ok () next) ∧
      Bindings.Writes state destination next ∧ LiveBinding globals resolved.program next destination (.sequenced definition) := by
  have related := global_operand sourceKnown
  obtain ⟨reads, tracked⟩ := RootCall.resolves_operand related
  have site := RootCall.checked_assign_site before rest destination _ _ reads globals linked resolved declared checked tracked
  have evaluated : RootCall.Evaluates state (.scalar (.read source)) (.ok (.function saved.address) state) := by
    simpa [State.read, saved.live.binding] using RootCall.Evaluates.name (state := state) source
  have live := commit_cell destinationKnown.1 layout _ _ _ _ saved.live.cell
  exact ⟨_, .ordinary (.setup site (.atom related evaluated)), .commit state _ (.refl _),
    ⟨destinationKnown.1, ⟨{ saved with
      cells := Defaults.Body.capture_cells_written _ _ _ saved.cells, live }⟩⟩⟩

theorem call_body {before rest : List Command} {globals : List String} {callee destination : String}
    {arguments : List Lowering.Resolve.SourceExpr} {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ invocation callee destination arguments :: rest) globals)
    (checked : resolve (before ++ invocation callee destination arguments :: rest) linked = .ok resolved)
    (known : Visible globals callee) (allowed : ∀ operand ∈ arguments, Trace.Operand globals operand)
    {state : State} {definition : Definition} (saved : SavedBody globals resolved.program state callee definition) :
    ∃ out, Step resolved globals before.length state (invocation callee destination arguments) out ∧
      (∀ next, out = .ok () next → Bindings.Writes state destination next) := by
  obtain ⟨actuals, related⟩ := actuals_related arguments allowed
  have calleeCode := global_operand known
  have site := RootCall.checked_call_assignment_site before rest destination _ arguments _ actuals globals
    linked resolved declared checked calleeCode related
  rcases RootCall.operands_total related state with ⟨values, ran⟩ | ⟨error, failed⟩
  · obtain ⟨binding, bound⟩ := Defaults.binds_total (definition.parameters.slots saved.values) values
    cases binding with
    | error error =>
      exact ⟨.error (.runtime error) state, .bodyCall saved site calleeCode related ran (.rejected bound),
        fun _ impossible => nomatch impossible⟩
    | ok assigned =>
      let active := activate state (saved.plan.declaration saved.codes) saved.captures assigned
      have frame := Defaults.Body.captured_frame saved.plan saved.codes saved.codeLength state saved.owner saved.captures
        saved.installed saved.cells assigned
      obtain ⟨out, executed, _, keeps⟩ := Defaults.Body.runs_total saved.plan.elaborates active frame
      refine ⟨_, .bodyCall saved site calleeCode related ran (.entered bound executed), ?_⟩
      intro next success
      cases out with
      | error => cases success
      | ok flow final =>
        cases success
        have stable : Bindings.Preserves state (restoreCaller state final) := by
          refine ⟨rfl, ?_⟩
          intro index cell stored _
          have within := (Array.getElem?_eq_some_iff.mp stored).choose
          have fresh := Wrapper.activation_preserves state (saved.plan.declaration saved.codes) saved.captures assigned index within
          exact keeps.2 index cell within (fresh.trans stored)
        exact .commit _ _ stable
  · have calleeRead : RootCall.Evaluates state (.scalar (.read callee)) (.ok (.function saved.address) state) := by
      simpa [State.read, saved.live.binding] using RootCall.Evaluates.name (state := state) callee
    exact ⟨.error (.runtime error) state, .ordinary (.operandError site calleeCode related (.cons calleeRead failed)),
      fun _ impossible => nomatch impossible⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults
