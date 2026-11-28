module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Definition
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (fileSlot globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive (Site compile_site)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named (resolves_at)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Functions (Program withoutDeclaration mem_withoutDeclaration)

theorem layout (wrapper : Wrapper) {producer : Program} {consumer : ResolvedModule}
    (checked : resolve wrapper.commands producer = .ok consumer) :
    consumer.program = producer.push wrapper.site.declaration ∧
    consumer.source.commands = wrapper.moduleCode producer ∧
    consumer.source.globals = [wrapper.name, wrapper.destination] ∧
    consumer.source.fileNames = [wrapper.alias] := by
  have detail := checked_of_resolve checked
  have distinct := wrapper.separate
  have compiledDef : elaborateCommand ⟨wrapper.parent.context, .global⟩
      (.define wrapper.name wrapper.site.sourceSignature wrapper.site.source) producer =
        .ok (.exec (.define wrapper.name producer.size), producer.push wrapper.site.declaration) :=
    wrapper_compiles wrapper.declaration producer
  have caller : Body.Operand wrapper.parent (.scalar (.read wrapper.name))
      (Leaf.readOperand (globalSlot wrapper.name)) [globalSlot wrapper.name] :=
    .read wrapper.legalName (.global (by simpa [Wrapper.parent, block] using distinct) (by simp [Wrapper.parent, block])
      (by simp [Wrapper.parent, block])) (.module (by simpa [Wrapper.parent, block] using distinct)
        (by simp [Wrapper.parent, block]) (by simp [Wrapper.parent, block]))
  have compiledCall := elaborateCommand_assign ⟨wrapper.parent.context, .global⟩ wrapper.destination wrapper.invoke
    (producer.push wrapper.site.declaration)
  rw [show Functions.Lowering.Resolve.resolveTracked wrapper.parent.context wrapper.invoke =
    .ok (wrapper.invokeCode, [globalSlot wrapper.name]) from resolves_at _ caller .nil .empty none none] at compiledCall
  have compiled : elaborateCommands wrapper.commands producer = .ok (wrapper.moduleCode producer,
      producer.push wrapper.site.declaration) := by
    rw [elaborateCommands, show moduleBlock wrapper.commands = ⟨wrapper.parent.context, .global⟩ by rfl]
    simp [Wrapper.commands, Wrapper.moduleCode, List.mapM_cons, bind, StateT.bind, Except.bind, pure,
      StateT.pure, Except.pure, elaborateCommand_load, compiledDef, compiledCall, Except.map, Except.mapError]
  obtain ⟨code, table⟩ := Prod.mk.inj (Except.ok.inj (detail.1.symm.trans compiled))
  exact ⟨table, code, detail.2.1, by rw [Modules.Source.fileNames, detail.2.2.1, code]; rfl⟩

theorem linked (wrapper : Wrapper) {producer : Program} {consumer : ResolvedModule}
    (checked : resolve wrapper.commands producer = .ok consumer) :
    PreservesDeclarations producer consumer.program ∧
    consumer.program[producer.size]? = some wrapper.site.declaration ∧
    List.Subset (List.range producer.size)
      (withoutDeclaration (List.range consumer.program.size) producer.size) := by
  rw [(layout wrapper checked).1]
  refine ⟨?_, Array.getElem?_push_size, ?_⟩
  · intro id decl found
    simp [Array.getElem?_push, Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp found).choose, found]
  · intro id member
    have below := List.mem_range.mp member
    exact mem_withoutDeclaration.mpr ⟨List.mem_range.mpr (by simp; omega), Nat.ne_of_lt below⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper
