module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Defs
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Site
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.Site
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Site

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
    (legal : parameter.toList.head? ≠ some '$') (operand : Operand)
    (named : ∀ name, operand = .read name → name ∈ context.locals ∧ name.toList.head? ≠ some '$') :
    resolveTracked context (operand.source parameter) = .ok (operand.code parameter, operand.reads parameter) := by
  cases operand with
  | parameter => exact local_read context parameter owned legal
  | read name =>
    obtain ⟨member, allowed⟩ := named name rfl
    exact local_read context name member allowed
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

theorem default_bindings (wrapper : Spec) (owned : List String) (parameter : wrapper.parameter ∈ owned)
    (allowed : wrapper.DefaultReads owned) {binding : Binding}
    (present : binding ∈ (planned wrapper).flatMap PlainPositionalDefault.reads) :
    ∃ name ∈ owned, binding = fileSlot name := by
  simp only [planned, List.flatMap_map, List.mem_flatMap] at present
  obtain ⟨⟨target, operand⟩, member, same⟩ := present
  cases operand with
  | parameter | index => exact ⟨_, parameter, by simpa [Operand.reads] using same⟩
  | read name => exact ⟨name, (allowed name ⟨target, member⟩).1, by simpa [Operand.reads] using same⟩
  | integer | list => simp [Operand.reads] at same

private theorem update_binders (wrapper : Spec) (updates : List (String × Int)) :
    (wrapper.updateSuite updates).binders = updates.map Prod.fst := by
  induction updates with
  | nil => rfl
  | cons item rest ih =>
    change item.1 :: (wrapper.updateSuite rest).binders = item.1 :: rest.map Prod.fst
    rw [ih]

theorem updates_elaborate (wrapper : Spec) (updates : List (String × Int)) (block : Assignment.LexicalBlock)
    (owned : ∀ name ∈ updates.map Prod.fst, name ∈ block.owned)
    (child : wrapper.childName ∈ block.owned) (legal : wrapper.childName.toList.head? ≠ some '$') :
    Defaults.Body.Elaborates block (wrapper.updateSuite updates) (wrapper.updateCode updates) [fileSlot wrapper.childName] := by
  induction updates with
  | nil => exact .ret (.read legal (.owned child) (.owned child))
  | cons update rest ih =>
    exact .assign (owned update.1 List.mem_cons_self) (.int update.2)
      (ih (fun name member => owned name (List.mem_cons_of_mem _ member)))

theorem code_length (wrapper : Spec) : wrapper.codes.length = wrapper.child.parameters.optional.length := by
  simp [Spec.codes, Spec.child]

private theorem captureNames_append_owned (owned : List String) (earlier later : List Binding)
    (localReads : ∀ binding ∈ later, ∃ name ∈ owned, binding = fileSlot name) :
    captureNames owned (earlier ++ later) = captureNames owned earlier := by
  let exported := fun (binding : Binding) => binding.scope == .global || !owned.contains binding.name
  have noNew : ((later.filter fun binding => !earlier.contains binding).eraseDups.filter exported) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro binding present
    obtain ⟨name, member, rfl⟩ := localReads binding (List.mem_filter.mp (List.mem_eraseDups.mp present)).1
    change ¬(false || !owned.contains name) = true
    rw [List.contains_iff_mem.mpr member]
    decide
  unfold captureNames
  rw [List.eraseDups_append, List.filter_append]
  change ((earlier.eraseDups.filter exported) ++
    (later.filter fun binding => !earlier.contains binding).eraseDups.filter exported).map _ = _
  rw [noNew, List.append_nil]

/-- Collect the whole wrapper before resolving either side of the
definition, then compile the assignments around the same child declaration. -/
theorem wrap_emission (wrapper : Spec) (admitted : WrapperNames wrapper) (globals additional : List String)
    (childFresh : wrapper.childName ∉ additional) (updates : List (String × Int))
    (fresh : ∀ name ∈ updates.map Prod.fst, name ∉ wrapper.parameter :: additional)
    (leading : List (String × SourceExpr)) (leadingCode : List (String × Lowering.Expr)) (leadingReads : List Binding)
    (childBody : Statement) (child : Declaration) (reads : List Binding)
    (leadingRelated : Defaults.Body.ElaboratesPrefix
      ⟨(wrapper.parameter :: additional) ++ wrapper.locals updates additional (leading.map Prod.fst), [], globals⟩
      leading leadingCode leadingReads)
    (leadingFree : List FreeName)
    (selected : Selects
      ⟨(wrapper.parameter :: additional) ++ wrapper.locals updates additional (leading.map Prod.fst), [], globals⟩
      leadingReads leadingFree)
    (owned : ∀ binding ∈ reads,
      ∃ name ∈ (wrapper.parameter :: additional) ++ wrapper.locals updates additional (leading.map Prod.fst),
        binding = fileSlot name)
    (childStep : ∀ program, compileBody
        ⟨⟨(wrapper.parameter :: additional) ++ wrapper.locals updates additional (leading.map Prod.fst), globals⟩, .local⟩
        (.define wrapper.childName wrapper.child.parameters.source childBody) program =
      .ok (⟨.define (fileSlot wrapper.childName) program.size, reads⟩, program.push child))
    (program : Program) :
    let frame := wrapper.frame program.size additional updates (leading.map Prod.fst)
    elaborateCommand ⟨⟨[], globals⟩, .global⟩ (wrapper.commandWith childBody additional updates leading) program =
      .ok (.exec (.define wrapper.name (program.size + 1)),
        (program.push child).push ({ frame with free := leadingFree, code := Defaults.Body.prependCode leadingCode frame.code } :
          Forwarding.Frame).declaration) := by
  let parameters := wrapper.parameter :: additional
  let locals := wrapper.locals updates additional (leading.map Prod.fst)
  let outer : BlockContext := ⟨⟨[], globals⟩, .global⟩
  let context : BlockContext := ⟨⟨parameters ++ locals, globals⟩, .local⟩
  let parentLayout : FunctionLayout := ⟨locals, context⟩
  let source := Defaults.Body.prependSource leading (wrapper.bodyWith childBody updates)
  have parameterNames : (SourceSignature.required parameters).parameterNames = parameters := by
    simp [SourceSignature.required, SourceSignature.parameterNames, List.map_map, Function.comp_def]
  have tailBinders : Block.BodyBinders (wrapper.bodyWith childBody updates)
      (wrapper.childName :: wrapper.parameter :: updates.map Prod.fst) := by
    rw [← update_binders wrapper updates]
    exact .seq (.define _ _ _) (.seq (.assign _ _) (Defaults.Body.collects (wrapper.updateSuite updates)))
  have occurrences : source.localNames = .ok (wrapper.occurrences updates (leading.map Prod.fst)) :=
    Block.localNames_eq (Defaults.Body.collects_prefix leading tailBinders)
  have parentCollected : collectFunctionLayout outer.reads (.required parameters) source = .ok parentLayout := by
    simp only [collectFunctionLayout, occurrences, Except.map]
    unfold functionLayout
    rw [parameterNames]
    simp [locals, Spec.locals, parameters, outer, parentLayout, context]
  have childLocal : wrapper.childName ∈ locals :=
    wrapper.local_member updates additional _ _ (by simp [Spec.occurrences]) (by
      simp [Ne.symm admitted.distinct, childFresh])
  let grown := program.push child
  have rebound := compileBody_plainAssign context wrapper.parameter (.scalar (.int wrapper.rebound)) _ _ grown
    (default_read context.reads wrapper.parameter (by simp [context, parameters]) admitted.parameterLegal
      (.integer wrapper.rebound) (by intro _ impossible; cases impossible))
  let block : Assignment.LexicalBlock := ⟨parameters ++ locals, [], globals⟩
  have tail : compileBody context (wrapper.updateSuite updates).source grown =
      .ok (⟨wrapper.updateCode updates, [fileSlot wrapper.childName]⟩, grown) := by
    simpa only [block, context, Assignment.LexicalBlock.context, List.append_nil] using
      Defaults.Body.compile_suite (updates_elaborate wrapper updates block
        (fun name member => List.mem_append_right _ (wrapper.local_member updates additional _ name
          (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))) (fresh name member)))
        (List.mem_append_right _ childLocal) admitted.childLegal) grown
  have tailCode := compileBody_plainSeq context _ _ grown grown grown _ _ rebound tail
  have body := compileBody_plainSeq context _ _ program grown grown _ _ (childStep program) tailCode
  have related : Defaults.Body.ElaboratesPrefix block leading leadingCode leadingReads := leadingRelated
  have bodyInContext := body
  have ctx : (⟨block.context, .local⟩ : BlockContext) = context := by
    simp [block, Assignment.LexicalBlock.context, context]
  rw [← ctx] at bodyInContext
  have prefixed := Defaults.Body.compile_prefix related bodyInContext
  rw [ctx] at prefixed
  have captures : captureNames (wrapper.parameter :: (additional ++ locals))
      (leadingReads ++ (reads ++ [fileSlot wrapper.childName])) = leadingFree := by
    change captureNames (parameters ++ locals) _ = _
    rw [captureNames_append_owned]
    · exact Capture.captureNames_eq selected
    · intro binding member
      rcases List.mem_append.mp member with earlier | returned
      · exact owned binding earlier
      · exact ⟨wrapper.childName, List.mem_append_right _ childLocal, by simpa using returned⟩
  have compiled := compileBody_requiredDefinition outer wrapper.name parameters source program grown
      parentLayout _ parentCollected prefixed
  have root := elaborateCommand_requiredDefinition outer .global wrapper.name parameters source program _ _ _ compiled
  simpa [Spec.commandWith, Spec.frame, Forwarding.Frame.declaration, outer, parentLayout, grown, parameters,
    Operand.code, Operand.reads, captures, source] using root

theorem emission (wrapper : Spec) (admitted : Admitted wrapper) (globals : List String) (program : Program) :
    elaborateCommand ⟨⟨[], globals⟩, .global⟩ wrapper.command program =
      .ok (.exec (.define wrapper.name (program.size + 1)),
        (program.push (wrapper.child.emitted wrapper.codes)).push (wrapper.frame program.size).declaration) := by
  let context : BlockContext := ⟨⟨[wrapper.parameter] ++ wrapper.locals [], globals⟩, .local⟩
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
    obtain ⟨⟨target, operand⟩, sourceMem, rfl⟩ := List.mem_map.mp member
    apply default_read context.reads wrapper.parameter (by simp [context]) admitted.parameterLegal operand
    intro name same
    subst operand
    obtain ⟨member, legal⟩ := admitted.defaultReads name ⟨target, sourceMem⟩
    exact ⟨List.mem_append_left _ member, legal⟩
  have childCaptures : captureNames wrapper.child.parameters.names [fileSlot wrapper.returned] = [] := by
    simp [captureNames, fileSlot, admitted.returned.1]
  rw [signature] at childCollected paramNames
  have optionalCodes : defaults.map PlainPositionalDefault.resolved =
      ((wrapper.child.parameters.optional.map (fileSlot ∘ Prod.fst)).zip wrapper.codes).map
        (fun (slot, code) => (⟨slot, some code⟩ : Parameter)) := by
    simp [defaults, planned, Spec.child, Spec.codes, List.map_map, Function.comp_def,
      List.zip_map', PlainPositionalDefault.resolved]
  let child := wrapper.child.emitted wrapper.codes
  exact wrap_emission wrapper admitted.wrapperNames globals [] (by simp) [] (by simp) [] [] [] wrapper.childBody child
    (defaults.flatMap PlainPositionalDefault.reads) .nil [] .nil (fun _ member => by
      obtain ⟨name, owned, same⟩ := default_bindings wrapper [wrapper.parameter] (by simp) admitted.defaultReads member
      exact ⟨name, List.mem_append_left _ owned, same⟩) (fun seed => by
      have compiled := compileBody_plainReturn inner (.scalar (.read wrapper.returned)) _ _ seed childRead
      have definition := compileBody_plainPositionalDefinition context wrapper.childName wrapper.required defaults
        wrapper.childBody seed seed childLayout _ defaultsRead childCollected compiled
      change compileBody context (.define wrapper.childName wrapper.child.parameters.source wrapper.childBody) seed = _
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
