module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Eval

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults

open Silmaril.Languages.Starlark (Binding resolveName)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Block (ModuleBinders)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve

theorem signature_defaults (parameters : Parameters) (codes : List Lowering.Expr) :
    (parameters.signature codes).defaulted = (parameters.optional.map (fileSlot ∘ Prod.fst)).zip codes := by
  simp [Parameters.signature, requiredSignature, Signature.defaulted, Signature.named,
    List.filterMap_append, List.filterMap_map, Function.comp_def]

theorem default_slots (definition : Definition) (codes : List Lowering.Expr) :
    (definition.emitted codes).signature.defaulted =
      (definition.parameters.optional.map (fileSlot ∘ Prod.fst)).zip codes :=
  signature_defaults definition.parameters codes

private theorem parameter_names (parameters : Parameters) :
    parameters.source.parameterNames = parameters.names := by
  simp [Parameters.source, Parameters.names, SourceSignature.parameterNames, List.map_append,
    List.map_map, Function.comp_def]

private theorem signature_source (definition : Definition) (defaults : List PlainPositionalDefault)
    (names : defaults.map (fun item => (item.name, item.source)) = definition.parameters.optional) :
    definition.parameters.source =
      { positional := definition.parameters.required.map (fun name => ⟨name, none⟩) ++
          defaults.map PlainPositionalDefault.parameter } := by
  simp [Parameters.source, ← names, List.map_map, PlainPositionalDefault.parameter, Function.comp_def]

private theorem defaults_resolved (definition : Definition) (defaults : List PlainPositionalDefault)
    (names : defaults.map (fun item => (item.name, item.source)) = definition.parameters.optional) :
    defaults.map PlainPositionalDefault.resolved =
      ((definition.parameters.optional.map (fileSlot ∘ Prod.fst)).zip
        (defaults.map PlainPositionalDefault.value)).map (fun (slot, code) => (⟨slot, some code⟩ : Parameter)) := by
  simp [← names, List.map_map, List.zip_map', PlainPositionalDefault.resolved, Function.comp_def]

private theorem elaborates {globals : List String} {definition : Definition}
    (admitted : Admitted globals definition)
    (defaults : List PlainPositionalDefault)
    (identified : defaults.map (fun item => (item.name, item.source)) = definition.parameters.optional)
    (translated : ∀ item ∈ defaults, resolveTracked ⟨[], globals⟩ item.source = .ok (item.value, item.reads))
    (program : Program) :
    elaborateCommand ⟨⟨[], globals⟩, .global⟩ definition.command program =
      .ok (.exec (.define definition.name program.size),
        program.push (definition.emitted (defaults.map PlainPositionalDefault.value))) := by
  let source : SourceExpr := .scalar (.read definition.returned)
  let body : Statement := .ret (some source)
  let parent : BlockContext := ⟨⟨[], globals⟩, .global⟩
  let layout : FunctionLayout := ⟨[], ⟨⟨definition.parameters.names, globals⟩, .local⟩⟩
  have collected : collectFunctionLayout parent.reads definition.parameters.source body = .ok layout := by
    simp [collectFunctionLayout, Statement.localNames, functionLayout, parameter_names, parent, body, layout,
      Except.map, pure, Except.pure]
  have operand : resolveTracked layout.block.reads source =
      .ok (Leaf.readOperand (fileSlot definition.returned), [fileSlot definition.returned]) := by
    have owned := admitted.returned.1
    have legal := admitted.returned.2
    unfold source
    rw [resolveTracked, resolveExpr.eq_def]
    simp [layout, resolveScalar, resolveRead, resolveReadValue, resolveName, owned, legal, Except.map,
      Leaf.readOperand, fileSlot]
  have closed := compileBody_plainReturn layout.block source _ _ program operand
  have sourceSignature := signature_source definition defaults identified
  rw [sourceSignature] at collected
  have actual := elaborateCommand_plainPositionalDefinition parent definition.name definition.parameters.required
    defaults body program program layout _ translated collected closed
  have free : captureNames definition.parameters.names [fileSlot definition.returned] = [] := by
    simp [captureNames, fileSlot, admitted.returned.1]
  change elaborateCommand parent (.define definition.name definition.parameters.source body) program = _
  rw [sourceSignature, actual]
  rw [defaults_resolved definition defaults identified]
  have params := parameter_names definition.parameters
  rw [sourceSignature] at params
  simp [Definition.emitted, Parameters.signature, layout, params, free]

theorem definition_emission {globals : List String} {definition : Definition}
    (admitted : Admitted globals definition) :
    ∃ codes, (∀ program,
      elaborateCommand ⟨⟨[], globals⟩, .global⟩ definition.command program =
        .ok (.exec (.define definition.name program.size), program.push (definition.emitted codes))) ∧
      codes.length = definition.parameters.optional.length ∧
      ∀ state, ∃ out, Evaluates globals state (definition.parameters.optional.map Prod.snd) codes out ∧
        (∀ values next, out = .ok values next → Bindings.Preserves state next) := by
  obtain ⟨defaults, identified, translated, eval⟩ := evaluates_from_source admitted.defaults
  refine ⟨defaults.map PlainPositionalDefault.value, elaborates admitted defaults identified translated, ?_, eval⟩
  rw [← identified]
  simp

theorem checked_definition_site {before after : List Command} {definition : Definition} {globals : List String}
    {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ definition.command :: after) globals)
    (checked : resolve (before ++ definition.command :: after) linked = .ok resolved)
    (admitted : Admitted globals definition) (segment : RootCall.Segment globals after) :
    ∃ id codes, resolved.source.commands[before.length]? = some (.exec (.define definition.name id)) ∧
      resolved.program[id]? = some (definition.emitted codes) ∧ codes.length = definition.parameters.optional.length ∧
      ∀ state, ∃ out, Evaluates globals state (definition.parameters.optional.map Prod.snd) codes out := by
  obtain ⟨codes, emits, length, evaluates⟩ := definition_emission admitted
  obtain ⟨id, site, found⟩ :=
    RootCall.checked_single_emission before after definition.command definition.name globals linked resolved
      (definition.emitted codes) declared checked segment emits
  refine ⟨id, codes, site, found, length, fun state => ?_⟩
  obtain ⟨out, ran, _⟩ := evaluates state
  exact ⟨out, ran⟩

private theorem exact_saved (parameters : Parameters) (values : List Silmaril.Languages.Starlark.Lists.Value) :
    savedValues (parameters.slots values) = (parameters.optional.map (fileSlot ∘ Prod.fst)).zip values := by
  unfold Parameters.slots savedValues
  rw [List.filterMap_append, List.zip_map_right]
  simp [List.filterMap_map, Function.comp_def, Prod.map]

private theorem same_slots (parameters : Parameters) (codes : List Lowering.Expr)
    (values : List Silmaril.Languages.Starlark.Lists.Value)
    (codeLength : codes.length = parameters.optional.length)
    (valueLength : values.length = parameters.optional.length) :
    (parameters.signature codes).positional.map Parameter.slot =
      (parameters.slots values).map Prod.fst := by
  have codeSlots := List.map_fst_zip (l₁ := parameters.optional.map (fileSlot ∘ Prod.fst))
    (l₂ := codes) (by simp [codeLength])
  have valueSlots := List.map_fst_zip (l₁ := parameters.optional.map (fileSlot ∘ Prod.fst))
    (l₂ := values.map some) (by simp [valueLength])
  simp [Parameters.signature, Parameters.slots, requiredSignature, List.map_map, Function.comp_def]
  exact codeSlots.trans valueSlots.symm

private theorem checked_slots {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (id : Nat) (declaration : Declaration)
    (found : resolved.program[id]? = some declaration) (keywordOnly : declaration.signature.keywordOnly = [])
    (varargs : declaration.signature.varargs = none) (kwargs : declaration.signature.kwargs = none) :
    (declaration.signature.positional.map Parameter.slot).Nodup := by
  have validated := Entry.checked_signature checked _ _ found
  let keys := declaration.signature.positional.map Parameter.slot
  have slots : declaration.signature.slots = keys := by
    simp [keys, Signature.slots, Signature.named, keywordOnly, varargs, kwargs]
  have firstNone : ∀ names : List String, firstDuplicate names = none ↔ names.Nodup := by
    intro names
    induction names with
    | nil => simp [firstDuplicate]
    | cons name rest ih =>
      by_cases member : name ∈ rest <;> simp [firstDuplicate, member, ih]
  have unique : (keys.map Binding.name).Nodup := by
    apply (firstNone _).mp
    unfold Signature.validate at validated
    rw [slots] at validated
    cases h : firstDuplicate (keys.map Binding.name) with
    | none => rfl
    | some duplicate => simp [h] at validated; contradiction
  exact List.Pairwise.of_map (f := Binding.name) (fun _ _ different same => different (congrArg Binding.name same)) unique

theorem checked_prepare_positional {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (id : Nat) (available : List DeclarationId)
    (permitted : id ∈ available) (parameters : Parameters)
    (declaration : Declaration) (codes : List Lowering.Expr)
    (found : resolved.program[id]? = some declaration)
    (signature : declaration.signature = parameters.signature codes)
    (codeLength : codes.length = parameters.optional.length)
    (state : Silmaril.Languages.Starlark.Lists.State) (address : Nat) (frozen : Bool)
    (captures : List Silmaril.Languages.Starlark.Lists.Capture)
    (defaults actuals : List Silmaril.Languages.Starlark.Lists.Value)
    (valueLength : defaults.length = parameters.optional.length)
    (cell : state.heap[address]? = some ⟨.function ⟨id, captures,
      (parameters.optional.map (fileSlot ∘ Prod.fst)).zip defaults⟩, frozen⟩)
    {result : Except Silmaril.Languages.Starlark.Lists.Error (List (Binding × Silmaril.Languages.Starlark.Lists.Value))}
    (binding : Binds (parameters.slots defaults) actuals result) :
    prepareExpanded resolved.program available ⟨actuals, []⟩ (.function address) state =
      match result with
      | .error error => .error error state
      | .ok assigned => .ok (.closure ⟨id, permitted, declaration.body⟩)
        (activate state declaration captures assigned) := by
  have slots := same_slots parameters codes defaults codeLength valueLength
  rw [← signature] at slots
  have keywords : declaration.signature.keywordOnly = [] := by rw [signature]; rfl
  have varargs : declaration.signature.varargs = none := by rw [signature]; rfl
  have kwargs : declaration.signature.kwargs = none := by rw [signature]; rfl
  have unique := checked_slots checked id declaration found keywords varargs kwargs
  rw [slots] at unique
  have ready := prepare_saved resolved.program available _ id permitted state address captures frozen _ actuals
    (by rw [exact_saved]; exact cell) found slots unique keywords varargs kwargs binding
  cases result <;> exact ready

theorem checked_prepare_signature {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (id : Nat) (parameters : Parameters)
    (declaration : Declaration) (codes : List Lowering.Expr)
    (found : resolved.program[id]? = some declaration)
    (signature : declaration.signature = parameters.signature codes)
    (codeLength : codes.length = parameters.optional.length)
    (state : Silmaril.Languages.Starlark.Lists.State) (address : Nat) (frozen : Bool)
    (captures : List Silmaril.Languages.Starlark.Lists.Capture)
    (defaults actuals : List Silmaril.Languages.Starlark.Lists.Value)
    (valueLength : defaults.length = parameters.optional.length)
    (cell : state.heap[address]? = some ⟨.function ⟨id, captures,
      (parameters.optional.map (fileSlot ∘ Prod.fst)).zip defaults⟩, frozen⟩)
    {result : Except Silmaril.Languages.Starlark.Lists.Error (List (Binding × Silmaril.Languages.Starlark.Lists.Value))}
    (binding : Binds (parameters.slots defaults) actuals result) :
    let available := List.range resolved.program.size
    ∃ permitted : id ∈ available,
      prepareExpanded resolved.program available ⟨actuals, []⟩ (.function address) state =
        match result with
        | .error error => .error error state
        | .ok assigned => .ok (.closure ⟨id, permitted, declaration.body⟩)
          (activate state declaration captures assigned) := by
  have permitted : id ∈ List.range resolved.program.size :=
    List.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).choose
  have prepared := checked_prepare_positional checked id _ permitted parameters declaration codes
    found signature codeLength state address frozen captures defaults actuals valueLength cell binding
  exact ⟨permitted, by cases result <;> exact prepared⟩

/-- At a later call, the current heap supplies the closure and the values
saved when it was defined. Preparing an omitted argument reads that value. -/
theorem checked_prepare_saved {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (id : Nat) (definition : Definition)
    (codes : List Lowering.Expr) (found : resolved.program[id]? = some (definition.emitted codes))
    (codeLength : codes.length = definition.parameters.optional.length)
    (state : Silmaril.Languages.Starlark.Lists.State) (address : Nat) (frozen : Bool)
    (defaults actuals : List Silmaril.Languages.Starlark.Lists.Value)
    (valueLength : defaults.length = definition.parameters.optional.length)
    (cell : state.heap[address]? = some ⟨.function ⟨id, [],
      (definition.parameters.optional.map (fileSlot ∘ Prod.fst)).zip defaults⟩, frozen⟩)
    {result : Except Silmaril.Languages.Starlark.Lists.Error (List (Binding × Silmaril.Languages.Starlark.Lists.Value))}
    (binding : Binds (definition.parameters.slots defaults) actuals result) :
    let available := List.range resolved.program.size
    ∃ permitted : id ∈ available,
      prepareExpanded resolved.program available ⟨actuals, []⟩ (.function address) state =
        match result with
        | .error error => .error error state
        | .ok assigned => .ok (.closure ⟨id, permitted, (definition.emitted codes).body⟩)
          (activate state (definition.emitted codes) [] assigned) := by
  have prepared := checked_prepare_signature checked id definition.parameters (definition.emitted codes)
    codes found rfl codeLength state address frozen [] defaults actuals valueLength cell binding
  cases result <;> exact prepared

/-- Successful evaluation determines the new closure cell and every later
positional binding that uses that cell at the same address. -/
theorem checked_installed_defaults {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) (id : Nat) (definition : Definition)
    (codes : List Lowering.Expr) (found : resolved.program[id]? = some (definition.emitted codes))
    (codeLength : codes.length = definition.parameters.optional.length)
    {globals : List String} {state residual : Silmaril.Languages.Starlark.Lists.State}
    {defaults : List Silmaril.Languages.Starlark.Lists.Value}
    (evaluated : Evaluates globals state (definition.parameters.optional.map Prod.snd) codes (.ok defaults residual)) :
    let saved := (definition.parameters.optional.map (fileSlot ∘ Prod.fst)).zip defaults
    let closure : Silmaril.Languages.Starlark.Lists.Closure := ⟨id, [], saved⟩
    let address := residual.heap.size
    let installed := install (Silmaril.Languages.Starlark.Modules.globalSlot definition.name) id [] saved residual
    let available := List.range resolved.program.size
    installed.heap[address]? = some ⟨.function closure, false⟩ ∧
      ∀ (later : Silmaril.Languages.Starlark.Lists.State) (frozen : Bool)
        (actuals : List Silmaril.Languages.Starlark.Lists.Value),
        later.heap[address]? = some ⟨.function closure, frozen⟩ →
        ∃ result, Binds (definition.parameters.slots defaults) actuals result ∧
          ∃ permitted : id ∈ available,
            prepareExpanded resolved.program available ⟨actuals, []⟩ (.function address) later =
              match result with
              | .error error => .error error later
              | .ok assigned => .ok (.closure ⟨id, permitted, (definition.emitted codes).body⟩)
                (activate later (definition.emitted codes) [] assigned) := by
  dsimp only
  refine ⟨write_keeps_function _ _ _ _ _ _ Array.getElem?_push_size, ?_⟩
  intro later frozen actuals cell
  obtain ⟨result, bound⟩ := binds_total (definition.parameters.slots defaults) actuals
  have length : defaults.length = definition.parameters.optional.length := by
    simpa only [List.length_map] using evaluated_length evaluated
  refine ⟨result, bound, ?_⟩
  have prepared := checked_prepare_saved checked id definition codes found codeLength
    later residual.heap.size frozen defaults actuals length cell bound
  cases result <;> exact prepared

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
