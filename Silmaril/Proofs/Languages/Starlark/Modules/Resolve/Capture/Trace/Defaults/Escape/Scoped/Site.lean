module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.Defs
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Site
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Site

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped

open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Block (ModuleBinders)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve (resolveTracked)

theorem emission (spec : Spec) (globals : List String) (names : Names spec)
    (plan : Plan globals spec) (program : Program) :
    elaborateCommand ⟨⟨[], globals⟩, .global⟩ spec.command program =
      .ok (.exec (.define spec.wrapper.name (program.size + 1)),
        (program.push (plan.childDeclaration)).push (plan.frame program.size).declaration) := by
  have translated : ∀ item ∈ plan.defaultItems,
      resolveTracked ⟨spec.enclosing, globals⟩ item.source = .ok (item.value, item.reads) := by
    intro item present
    simpa only [Spec.block, Assignment.LexicalBlock.context, List.append_nil] using
      Defaults.Lexical.translated plan.defaults item present
  have reads (binding : Silmaril.Languages.Starlark.Binding)
      (member : binding ∈ plan.body.free.map FreeName.source) :
      ∃ name ∈ spec.enclosing, binding = fileSlot name := by
    obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    obtain ⟨name, eligible, _, rfl⟩ := plan.captured entry present
    exact ⟨name, eligible, rfl⟩
  apply Defaults.Escape.wrap_emission spec.wrapper names.wrapper globals spec.additional names.childFresh spec.updates
    (fun name member => (names.localUpdates name member).1) spec.leading plan.leadingCode plan.leadingReads
    spec.child.body.source _ _ _ plan.leading plan.moduleFree (Capture.captureNames_eq plan.selects) reads
  intro seed
  exact Defaults.Body.compile_nested plan.body plan.defaultItems (Defaults.Lexical.sources_eq plan.defaults) translated seed

theorem checked_site {before after : List Command} {globals : List String} {spec : Spec}
    {linked : Program} {resolved : ResolvedModule} (names : Names spec)
    (plan : Plan globals spec) (declared : ModuleBinders (before ++ spec.command :: after) globals)
    (checked : resolve (before ++ spec.command :: after) linked = .ok resolved)
    (suffix : RootCall.Segment globals after) :
    ∃ id, resolved.source.commands[before.length]? = some (.exec (.define spec.wrapper.name (id + 1))) ∧
      resolved.program[id]? = some (plan.childDeclaration) ∧
      resolved.program[id + 1]? = some (plan.frame id).declaration :=
  RootCall.checked_pair_emission before after spec.command spec.wrapper.name globals linked resolved
    (plan.childDeclaration) (fun id => (plan.frame id).declaration)
    declared checked suffix (emission spec globals names plan)

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped
