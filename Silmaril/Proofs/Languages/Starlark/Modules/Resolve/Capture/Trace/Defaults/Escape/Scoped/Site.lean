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

theorem emission (spec : Spec) (globals : List String) (names : Defaults.Escape.WrapperNames spec.wrapper)
    (plan : Plan globals spec) (program : Program) :
    elaborateCommand ⟨⟨[], globals⟩, .global⟩ spec.command program =
      .ok (.exec (.define spec.wrapper.name (program.size + 1)),
        (program.push (plan.body.declaration spec.wrapper.codes)).push (spec.wrapper.frame program.size).declaration) := by
  let wrapper := spec.wrapper
  let defaults := Defaults.Escape.planned wrapper
  have paired : defaults.map (fun item => (item.name, item.source)) = spec.child.parameters.optional := by
    simp [defaults, wrapper, Defaults.Escape.planned, Spec.child, Defaults.Escape.Spec.child, List.map_map, Function.comp_def]
  have translated : ∀ item ∈ defaults,
      resolveTracked ⟨spec.enclosing, globals⟩ item.source = .ok (item.value, item.reads) := by
    intro item member
    obtain ⟨⟨name, operand⟩, _, rfl⟩ := List.mem_map.mp member
    exact Defaults.Escape.default_read _ wrapper.parameter (by simp [Spec.enclosing, wrapper]) names.parameterLegal operand
  have codes : defaults.map PlainPositionalDefault.value = wrapper.codes := by
    simp [defaults, Defaults.Escape.planned, Defaults.Escape.Spec.codes, List.map_map, Function.comp_def]
  have reads (binding : Silmaril.Languages.Starlark.Binding)
      (member : binding ∈ defaults.flatMap PlainPositionalDefault.reads ++ plan.body.free.map FreeName.source) :
      binding = fileSlot wrapper.parameter := by
    rcases List.mem_append.mp member with fromDefault | fromBody
    · exact Defaults.Escape.only_parameter wrapper fromDefault
    · simpa [plan.captured, wrapper] using fromBody
  apply Defaults.Escape.wrap_emission wrapper names globals spec.child.body.source _ _ reads
  intro seed
  have step := Defaults.Body.compile_nested plan.body defaults paired translated seed
  rw [codes] at step
  exact step

theorem checked_site {before after : List Command} {globals : List String} {spec : Spec}
    {linked : Program} {resolved : ResolvedModule} (names : Defaults.Escape.WrapperNames spec.wrapper)
    (plan : Plan globals spec) (declared : ModuleBinders (before ++ spec.command :: after) globals)
    (checked : resolve (before ++ spec.command :: after) linked = .ok resolved)
    (suffix : RootCall.Segment globals after) :
    ∃ id, resolved.source.commands[before.length]? = some (.exec (.define spec.wrapper.name (id + 1))) ∧
      resolved.program[id]? = some (plan.body.declaration spec.wrapper.codes) ∧
      resolved.program[id + 1]? = some (spec.wrapper.frame id).declaration :=
  RootCall.checked_pair_emission before after spec.command spec.wrapper.name globals linked resolved
    (plan.body.declaration spec.wrapper.codes) (fun id => (spec.wrapper.frame id).declaration)
    declared checked suffix (emission spec globals names plan)

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped
