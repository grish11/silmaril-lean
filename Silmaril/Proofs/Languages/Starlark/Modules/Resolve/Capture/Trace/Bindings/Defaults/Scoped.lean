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
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped (Spec Admitted)
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (Cell State)

theorem define_scoped {before after : List Command} {spec : Spec} {globals : List String}
    {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ spec.command :: after) globals)
    (checked : resolve (before ++ spec.command :: after) linked = .ok resolved)
    (admitted : Admitted globals spec) (suffix : RootCall.Segment globals after)
    (known : Visible globals spec.wrapper.name) {state : State} (layout : ModuleSlots globals state) :
    ∃ next, Step resolved globals before.length state spec.command (.ok () next) ∧
      Bindings.Writes state spec.wrapper.name next ∧
      LiveBinding globals resolved.program next spec.wrapper.name (.nestedBody spec) := by
  obtain ⟨plan⟩ := admitted.plan
  obtain ⟨childId, site, childCode, parentCode⟩ := Defaults.Escape.Scoped.checked_site
    admitted.names plan declared checked suffix
  obtain ⟨captures, installed⟩ := Defaults.Body.instantiate_selected plan.leadingSelects state layout
  have cells := Defaults.Body.selected_cells plan.leadingSelects state layout captures installed
  let cell : Cell := ⟨.function ⟨childId + 1, captures, []⟩, false⟩
  let grown : State := { state with heap := state.heap.push cell }
  let keep := Bindings.Preserves.push state cell
  have live := commit_cell known.1 (keep.layout layout) state.heap.size (childId + 1) captures []
    (show grown.heap[state.heap.size]? = some cell from Array.getElem?_push_size)
  obtain ⟨retained, liveCells⟩ := commit_captures keep spec.wrapper.name (.function state.heap.size) installed cells
  exact ⟨_, .ordinary (.define site parentCode installed), .commit grown _ keep,
    ⟨known.1, ⟨⟨childId, state.heap.size, admitted.names, plan, childCode, parentCode, captures, retained, liveCells, live⟩⟩⟩⟩

theorem alias_scoped {before rest : List Command} {globals : List String} {source destination : String}
    {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ .assign destination (.scalar (.read source)) :: rest) globals)
    (checked : resolve (before ++ .assign destination (.scalar (.read source)) :: rest) linked = .ok resolved)
    (sourceKnown : Visible globals source) (destinationKnown : Visible globals destination)
    {state : State} {spec : Spec} (root : ScopedRoot globals resolved.program state source spec)
    (layout : ModuleSlots globals state) :
    ∃ next, Step resolved globals before.length state (.assign destination (.scalar (.read source))) (.ok () next) ∧
      Bindings.Writes state destination next ∧ LiveBinding globals resolved.program next destination (.nestedBody spec) := by
  have related := global_operand sourceKnown
  obtain ⟨reads, tracked⟩ := RootCall.resolves_operand related
  have site := RootCall.checked_assign_site before rest destination _ _ reads globals linked resolved declared checked tracked
  have evaluated : RootCall.Evaluates state (.scalar (.read source)) (.ok (.function root.address) state) := by
    simpa [State.read, root.live.binding] using RootCall.Evaluates.name (state := state) source
  have live := commit_cell destinationKnown.1 layout _ _ _ _ root.live.cell
  obtain ⟨installed, cells⟩ := commit_captures (Bindings.Preserves.refl state) destination
    (.function root.address) root.installed root.cells
  exact ⟨_, .ordinary (.setup site (.atom related evaluated)), .commit state _ (.refl _),
    ⟨destinationKnown.1, ⟨{ root with installed, cells, live }⟩⟩⟩

theorem call_scoped {before rest : List Command} {globals : List String} {callee destination : String}
    {arguments : List Lowering.Resolve.SourceExpr} {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ invocation callee destination arguments :: rest) globals)
    (checked : resolve (before ++ invocation callee destination arguments :: rest) linked = .ok resolved)
    (known : Visible globals callee) (target : Visible globals destination)
    (allowed : ∀ operand ∈ arguments, Trace.Operand globals operand)
    {state : State} {spec : Spec} (root : ScopedRoot globals resolved.program state callee spec)
    (layout : ModuleSlots globals state) :
    ∃ out, Step resolved globals before.length state (invocation callee destination arguments) out ∧
      (∀ next, out = .ok () next → Bindings.Writes state destination next ∧
        LiveBinding globals resolved.program next destination (.sequenced spec.child)) := by
  obtain ⟨actuals, related⟩ := actuals_related arguments allowed
  have calleeCode := global_operand known
  have site := RootCall.checked_call_assignment_site before rest destination _ arguments _ actuals globals
    linked resolved declared checked calleeCode related
  rcases RootCall.operands_total related state with ⟨values, ran⟩ | ⟨error, failed⟩
  · obtain ⟨binding, bound⟩ := Entry.binds_total spec.parameters values
    cases binding with
    | error error =>
      exact ⟨.error (.runtime error) state, .scopedCall root site calleeCode related ran (.rejected bound),
        fun _ impossible => nomatch impossible⟩
    | ok assigned =>
      let codes := spec.wrapper.codes
      obtain ⟨out, _, returned, _, _, progress⟩ := Defaults.Escape.Scoped.returns_total root.names root.plan
        resolved.program (withoutDeclaration (List.range resolved.program.size) (root.childId + 1))
        root.childId root.childCode state root.captures root.installed root.cells assigned
      refine ⟨_, .scopedCall root site calleeCode related ran (.entered bound returned), ?_⟩
      intro next success
      cases out with
      | error => cases success
      | ok value middle =>
        cases success
        obtain ⟨address, values, reached, captures, rfl, length, _, _, installed, cell, kept, retained, _⟩ :=
          progress value middle rfl
        have stored := Defaults.Body.capture_cells_written middle (globalSlot destination) (.function address) retained
        have live := commit_cell target.1 (kept.layout layout) address root.childId captures _ cell
        exact ⟨.commit middle _ kept, ⟨target.1, ⟨⟨root.childId, spec.enclosing, root.plan.body, codes,
          address, values, captures, Defaults.Escape.code_length spec.wrapper, length, root.childCode,
          reached, installed, stored, live⟩⟩⟩⟩
  · have calleeRead : RootCall.Evaluates state (.scalar (.read callee)) (.ok (.function root.address) state) := by
      simpa [State.read, root.live.binding] using RootCall.Evaluates.name (state := state) callee
    exact ⟨.error (.runtime error) state, .ordinary (.operandError site calleeCode related (.cons calleeRead failed)),
      fun _ impossible => nomatch impossible⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults
