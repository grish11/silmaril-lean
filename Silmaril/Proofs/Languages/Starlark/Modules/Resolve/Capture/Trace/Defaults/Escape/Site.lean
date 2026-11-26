module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Defs
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Site
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.Site

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape

open Silmaril.Languages.Starlark (Binding resolveName)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Block (ModuleBinders)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve

private theorem local_read_at (context : Context) (name : String) (owned : name ∈ context.locals)
    (legal : name.toList.head? ≠ some '$') (initial : List Binding) :
    resolveExpr context (.scalar (.read name)) initial = .ok (Leaf.readOperand (fileSlot name), fileSlot name :: initial) := by
  rw [resolveExpr.eq_def]
  simp [resolveScalar, resolveRead, resolveReadValue, resolveName, owned, legal, Except.map, Leaf.readOperand, fileSlot]

private theorem int_at (context : Context) (value : Int) (initial : List Binding) :
    resolveExpr context (.scalar (.int value)) initial = .ok (.atom (.scalar (.int value)), initial) := by
  rw [resolveExpr.eq_def]
  rfl

private theorem local_read (context : Context) (name : String) (owned : name ∈ context.locals)
    (legal : name.toList.head? ≠ some '$') :
    resolveTracked context (.scalar (.read name)) = .ok (Leaf.readOperand (fileSlot name), [fileSlot name]) := by
  simp [resolveTracked, local_read_at context name owned legal, Except.map]

theorem default_read (context : Context) (parameter : String) (owned : parameter ∈ context.locals)
    (legal : parameter.toList.head? ≠ some '$') (operand : Operand) :
    resolveTracked context (operand.source parameter) = .ok (operand.code parameter, operand.reads parameter) := by
  cases operand with
  | parameter => exact local_read context parameter owned legal
  | index offset =>
    change resolveTracked context (.index (.scalar (.read parameter)) (.scalar (.int offset))) = _
    rw [resolveTracked, resolveExpr.eq_def]
    simp [local_read_at context parameter owned legal, int_at, Operand.code, Operand.reads,
      bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, Except.map]
  | integer value => simp [Operand.source, Operand.code, Operand.reads, resolveTracked, int_at, Except.map]
  | list value =>
    change resolveTracked context (.list [.scalar (.int value)]) = _
    rw [resolveTracked, resolveExpr.eq_def]
    simp [int_at, Operand.code, Operand.reads, bind, StateT.bind, Except.bind, pure, StateT.pure,
      Except.pure, Except.map]
@[expose] def planned (wrapper : Spec) : List PlainPositionalDefault :=
  wrapper.defaults.map fun (name, operand) =>
    ⟨name, operand.source wrapper.parameter, operand.code wrapper.parameter, operand.reads wrapper.parameter⟩

theorem only_parameter (wrapper : Spec) {binding : Binding}
    (present : binding ∈ (planned wrapper).flatMap PlainPositionalDefault.reads) :
    binding = fileSlot wrapper.parameter := by
  simp only [planned, List.flatMap_map, List.mem_flatMap] at present
  obtain ⟨⟨name, operand⟩, _, same⟩ := present
  cases operand <;> simp [Operand.reads] at same <;> exact same

theorem code_length (wrapper : Spec) : wrapper.codes.length = wrapper.child.parameters.optional.length := by
  simp [Spec.codes, Spec.child]

/-- Compile the existing wrapper around any child declaration whose
definition-time reads belong to the wrapper parameter. -/
theorem wrap_emission (wrapper : Spec) (admitted : WrapperNames wrapper) (globals : List String)
    (childBody : Statement) (child : Declaration) (reads : List Binding)
    (owned : ∀ binding ∈ reads, binding = fileSlot wrapper.parameter)
    (childStep : ∀ program, compileBody ⟨⟨[wrapper.parameter, wrapper.childName], globals⟩, .local⟩
        (.define wrapper.childName wrapper.child.parameters.source childBody) program =
      .ok (⟨.define (fileSlot wrapper.childName) program.size, reads⟩, program.push child))
    (program : Program) :
    elaborateCommand ⟨⟨[], globals⟩, .global⟩ (wrapper.commandWith childBody) program =
      .ok (.exec (.define wrapper.name (program.size + 1)),
        (program.push child).push (wrapper.frame program.size).declaration) := by
  let outer : BlockContext := ⟨⟨[], globals⟩, .global⟩
  let context : BlockContext := ⟨⟨[wrapper.parameter, wrapper.childName], globals⟩, .local⟩
  let parentLayout : FunctionLayout := ⟨[wrapper.childName], context⟩
  have parentCollected : collectFunctionLayout outer.reads (.required [wrapper.parameter]) (wrapper.bodyWith childBody) =
      .ok parentLayout := by
    simp [collectFunctionLayout, Statement.localNames, Spec.bodyWith, functionLayout,
      SourceSignature.required, SourceSignature.parameterNames, parentLayout, outer, context,
      List.eraseDups_cons, Ne.symm admitted.distinct, Except.map, bind, Except.bind, pure, Except.pure]
  let grown := program.push child
  have rebound := compileBody_plainAssign context wrapper.parameter (.scalar (.int wrapper.rebound)) _ _ grown
    (default_read context.reads wrapper.parameter (by simp [context]) admitted.parameterLegal (.integer wrapper.rebound))
  have tail := compileBody_seqReturn context (.assign wrapper.parameter (.scalar (.int wrapper.rebound)))
    (.scalar (.read wrapper.childName)) grown grown _ _ _ rebound
    (local_read context.reads wrapper.childName (by simp [context]) admitted.childLegal)
  have body := compileBody_plainSeq context _ _ program grown grown _ _ (childStep program) tail
  have captures : captureNames [wrapper.parameter, wrapper.childName]
      (reads ++ [fileSlot wrapper.childName]) = [] := by
    unfold captureNames
    suffices removed : ((reads ++ [fileSlot wrapper.childName]).eraseDups.filter
        fun binding => binding.scope == .global || ![wrapper.parameter, wrapper.childName].contains binding.name) = [] by
      rw [removed]
      rfl
    apply List.filter_eq_nil_iff.mpr
    intro binding mem
    have present := List.mem_eraseDups.mp mem
    rcases List.mem_append.mp present with earlier | returned
    · rw [owned binding earlier]
      simp [fileSlot]
    · have same : binding = fileSlot wrapper.childName := by simpa using returned
      simp [same, fileSlot]
  have compiled := compileBody_requiredDefinition outer wrapper.name [wrapper.parameter] (wrapper.bodyWith childBody) program grown
      parentLayout _ parentCollected body
  have root := elaborateCommand_requiredDefinition outer .global wrapper.name [wrapper.parameter] (wrapper.bodyWith childBody) program _ _ _ compiled
  simpa [Spec.commandWith, Spec.frame, Forwarding.Frame.declaration, outer, parentLayout, grown,
    Operand.code, Operand.reads, List.nil_append, captures] using root


theorem emission (wrapper : Spec) (admitted : Admitted wrapper) (globals : List String) (program : Program) :
    elaborateCommand ⟨⟨[], globals⟩, .global⟩ wrapper.command program =
      .ok (.exec (.define wrapper.name (program.size + 1)),
        (program.push (wrapper.child.emitted wrapper.codes)).push (wrapper.frame program.size).declaration) := by
  let context : BlockContext := ⟨⟨[wrapper.parameter, wrapper.childName], globals⟩, .local⟩
  let inner : BlockContext := ⟨⟨wrapper.child.parameters.names ++ context.reads.locals, globals⟩, .local⟩
  let childLayout : FunctionLayout := ⟨[], inner⟩
  let defaults := planned wrapper
  have signature : wrapper.child.parameters.source = {
      positional := wrapper.required.map (fun name => ⟨name, none⟩) ++ defaults.map PlainPositionalDefault.parameter } := by
    simp [Spec.child, Defaults.Parameters.source, defaults, planned, List.map_map,
      Function.comp_def, PlainPositionalDefault.parameter]
  have paramNames : wrapper.child.parameters.source.parameterNames = wrapper.child.parameters.names := by
    simp [Defaults.Parameters.source, Defaults.Parameters.names, SourceSignature.parameterNames,
      List.map_append, List.map_map, Function.comp_def]
  have childCollected : collectFunctionLayout context.reads wrapper.child.parameters.source wrapper.childBody =
      .ok childLayout := by
    simp [collectFunctionLayout, Statement.localNames, functionLayout, Spec.childBody, paramNames,
      context, inner, childLayout, Except.map, pure, Except.pure]
  have childRead := local_read inner.reads wrapper.returned
    (by simp [inner, admitted.returned.1]) admitted.returned.2
  have defaultsRead : ∀ item ∈ defaults, resolveTracked context.reads item.source = .ok (item.value, item.reads) := by
    intro item member
    obtain ⟨⟨name, operand⟩, _, rfl⟩ := List.mem_map.mp member
    exact default_read context.reads wrapper.parameter (by simp [context]) admitted.parameterLegal operand
  have childCaptures : captureNames wrapper.child.parameters.names [fileSlot wrapper.returned] = [] := by
    simp [captureNames, fileSlot, admitted.returned.1]
  rw [signature] at childCollected paramNames
  have optionalCodes : defaults.map PlainPositionalDefault.resolved =
      ((wrapper.child.parameters.optional.map (fileSlot ∘ Prod.fst)).zip wrapper.codes).map
        (fun (slot, code) => (⟨slot, some code⟩ : Parameter)) := by
    simp [defaults, planned, Spec.child, Spec.codes, List.map_map, Function.comp_def,
      List.zip_map', PlainPositionalDefault.resolved]
  let child := wrapper.child.emitted wrapper.codes
  exact wrap_emission wrapper admitted.wrapperNames globals wrapper.childBody child
    (defaults.flatMap PlainPositionalDefault.reads) (fun _ member => only_parameter wrapper member) (fun seed => by
      have compiled := compileBody_plainReturn inner (.scalar (.read wrapper.returned)) _ _ seed childRead
      have definition := compileBody_plainPositionalDefinition context wrapper.childName wrapper.required defaults
        wrapper.childBody seed seed childLayout _ defaultsRead childCollected compiled
      rw [signature, definition, optionalCodes]
      simp only [childLayout, List.map_nil, List.append_nil, paramNames, childCaptures]
      rfl) program

theorem checked_site {before after : List Command} {globals : List String} {wrapper : Spec}
    {linked : Program} {resolved : ResolvedModule} (admitted : Admitted wrapper)
    (declared : ModuleBinders (before ++ wrapper.command :: after) globals)
    (checked : resolve (before ++ wrapper.command :: after) linked = .ok resolved)
    (suffix : RootCall.Segment globals after) :
    ∃ childId, resolved.source.commands[before.length]? = some (.exec (.define wrapper.name (childId + 1))) ∧
      resolved.program[childId]? = some (wrapper.child.emitted wrapper.codes) ∧
      resolved.program[childId + 1]? = some (wrapper.frame childId).declaration :=
  RootCall.checked_pair_emission before after wrapper.command wrapper.name globals linked resolved
    (wrapper.child.emitted wrapper.codes) (fun id => (wrapper.frame id).declaration) declared checked suffix
    (emission wrapper admitted globals)

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape
