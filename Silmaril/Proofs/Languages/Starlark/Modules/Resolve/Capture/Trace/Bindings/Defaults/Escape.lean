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
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape (Spec Admitted)
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (Cell State)

theorem define_wrapper {before after : List Command} {wrapper : Spec} {globals : List String}
    {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ wrapper.command :: after) globals)
    (checked : resolve (before ++ wrapper.command :: after) linked = .ok resolved)
    (admitted : Admitted wrapper) (suffix : RootCall.Segment globals after)
    (known : Visible globals wrapper.name) {state : State} (layout : ModuleSlots globals state) :
    ∃ next, Step resolved globals before.length state wrapper.command (.ok () next) ∧
      Bindings.Writes state wrapper.name next ∧
      LiveBinding globals resolved.program next wrapper.name (.escaping wrapper) := by
  obtain ⟨childId, site, childCode, parentCode⟩ := Defaults.Escape.checked_site admitted declared checked suffix
  let cell : Cell := ⟨.function ⟨childId + 1, [], []⟩, false⟩
  let grown : State := { state with heap := state.heap.push cell }
  let keep := Bindings.Preserves.push state cell
  have live := commit_cell known.1 (keep.layout layout) state.heap.size (childId + 1) [] []
    (show grown.heap[state.heap.size]? = some cell from Array.getElem?_push_size)
  exact ⟨_, .ordinary (.define site parentCode .nil), .commit grown _ keep,
    ⟨known.1, ⟨⟨childId, state.heap.size, admitted, childCode, parentCode, live⟩⟩⟩⟩

theorem alias_wrapper {before rest : List Command} {globals : List String} {source destination : String}
    {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ .assign destination (.scalar (.read source)) :: rest) globals)
    (checked : resolve (before ++ .assign destination (.scalar (.read source)) :: rest) linked = .ok resolved)
    (sourceKnown : Visible globals source) (destinationKnown : Visible globals destination)
    {state : State} {wrapper : Spec} (root : Escaping resolved.program state source wrapper)
    (layout : ModuleSlots globals state) :
    ∃ next, Step resolved globals before.length state (.assign destination (.scalar (.read source))) (.ok () next) ∧
      Bindings.Writes state destination next ∧ LiveBinding globals resolved.program next destination (.escaping wrapper) := by
  have related := global_operand sourceKnown
  obtain ⟨reads, tracked⟩ := RootCall.resolves_operand related
  have site := RootCall.checked_assign_site before rest destination _ _ reads globals linked resolved declared checked tracked
  have evaluated : RootCall.Evaluates state (.scalar (.read source)) (.ok (.function root.address) state) := by
    simpa [State.read, root.live.binding] using RootCall.Evaluates.name (state := state) source
  have live := commit_cell destinationKnown.1 layout _ _ _ _ root.live.cell
  exact ⟨_, .ordinary (.setup site (.atom related evaluated)), .commit state _ (Bindings.Preserves.refl _),
    ⟨destinationKnown.1, ⟨{ root with live }⟩⟩⟩

theorem call_wrapper {before rest : List Command} {globals : List String} {callee destination : String}
    {arguments : List Lowering.Resolve.SourceExpr} {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ invocation callee destination arguments :: rest) globals)
    (checked : resolve (before ++ invocation callee destination arguments :: rest) linked = .ok resolved)
    (known : Visible globals callee) (target : Visible globals destination)
    (allowed : ∀ operand ∈ arguments, Trace.Operand globals operand)
    {state : State} {wrapper : Spec} (root : Escaping resolved.program state callee wrapper)
    (layout : ModuleSlots globals state) :
    ∃ out, Step resolved globals before.length state (invocation callee destination arguments) out ∧
      (∀ next, out = .ok () next → Bindings.Writes state destination next ∧
        LiveBinding globals resolved.program next destination (.defaulted wrapper.child)) := by
  obtain ⟨actuals, related⟩ := actuals_related arguments allowed
  have calleeCode := global_operand known
  have site := RootCall.checked_call_assignment_site before rest destination _ arguments _ actuals globals
    linked resolved declared checked calleeCode related
  rcases RootCall.operands_total related state with ⟨values, ran⟩ | ⟨error, failed⟩
  · obtain ⟨binding, bound⟩ := Entry.binds_total [wrapper.parameter] values
    cases binding with
    | error error =>
      exact ⟨.error (.runtime error) state, .wrapper root site calleeCode related ran (.rejected bound),
        fun _ impossible => nomatch impossible⟩
    | ok assigned =>
      cases bound with
      | success fill =>
        cases fill with
        | @cons _ _ argument _ _ tail =>
          cases tail
          obtain ⟨out, _, returned, _, _, progress⟩ := Defaults.Escape.returns_total resolved.program
            (withoutDeclaration (List.range resolved.program.size) (root.childId + 1)) wrapper root.admitted
            root.childId root.childCode state argument
          refine ⟨_, .wrapper root site calleeCode related ran (.entered returned), ?_⟩
          intro next success
          cases out with
          | error => cases success
          | ok value middle =>
            cases success
            obtain ⟨address, values, rfl, length, cell, _, kept⟩ := progress value middle rfl
            exact ⟨.commit middle _ kept, retarget target.1 (kept.layout layout) root.childId wrapper.codes address values
              (Defaults.Escape.code_length wrapper) length root.childCode cell⟩
  · have calleeRead : RootCall.Evaluates state (.scalar (.read callee)) (.ok (.function root.address) state) := by
      simpa [State.read, root.live.binding] using RootCall.Evaluates.name (state := state) callee
    exact ⟨.error (.runtime error) state, .ordinary (.operandError site calleeCode related (.cons calleeRead failed)),
      fun _ impossible => nomatch impossible⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults
