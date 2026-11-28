module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Run
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Site
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Block

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body

open Silmaril.Languages.Starlark (Binding resolveName)
open Silmaril.Languages.Starlark.Modules (fileSlot globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Block (BodyBinders LocalBinders ModuleBinders)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve

theorem resolves_at {block : LexicalBlock} {source : SourceExpr} {code : Lowering.Expr}
    {reads : List Binding} (operand : Operand block source code reads) (initial : List Binding) :
    resolveExpr block.context source initial = .ok (code, reads.reverse ++ initial) := by
  induction operand generalizing initial with
  | @read name binding origin legal lexical _ =>
    rw [resolveExpr.eq_def]
    cases lexical with
    | owned member =>
      simp [LexicalBlock.context, resolveScalar, resolveRead, resolveReadValue, resolveName, legal, member, Except.map,
        Leaf.readOperand]
    | enclosing hidden member =>
      simp [LexicalBlock.context, resolveScalar, resolveRead, resolveReadValue, resolveName, legal, member, Except.map,
        Leaf.readOperand]
    | global hidden outer member =>
      simp [LexicalBlock.context, resolveScalar, resolveRead, resolveReadValue, resolveName, legal, hidden, outer, member,
        Except.map, Leaf.readOperand]
  | int =>
    rw [resolveExpr.eq_def]
    rfl
  | index left right first second =>
    rw [resolveExpr.eq_def]
    simp [first, second, List.reverse_append, List.append_assoc, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure]
  | list _ ih =>
    rw [resolveExpr.eq_def]
    simp [ih, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure]

theorem resolves {block : LexicalBlock} {source : SourceExpr} {code : Lowering.Expr}
    {reads : List Binding} (operand : Operand block source code reads) :
    resolveTracked block.context source = .ok (code, reads) := by
  simp [resolveTracked, resolves_at operand, Except.map]

theorem compile_suite {block : LexicalBlock} {source : Suite}
    {code : Silmaril.Languages.Starlark.Functions.Body} {reads : List Binding}
    (related : Elaborates block source code reads) (program : Program) :
    compileBody ⟨block.context, .local⟩ source.source program = .ok (⟨code, reads⟩, program) := by
  induction related with
  | ret operand => exact compileBody_plainReturn _ _ _ _ program (resolves operand)
  | assign _ operand _ ih =>
    exact compileBody_plainSeq _ _ _ program program program _ _
      (compileBody_plainAssign _ _ _ _ _ program (resolves operand)) ih

theorem compile_prefix {block : LexicalBlock} {source : List (String × SourceExpr)}
    {code : List (String × Lowering.Expr)} {reads : List Binding}
    (related : ElaboratesPrefix block source code reads)
    {tail : Statement} {tailCode : ResolvedBody} {program final : Program}
    (compiled : compileBody ⟨block.context, .local⟩ tail program = .ok (tailCode, final)) :
    compileBody ⟨block.context, .local⟩ (prependSource source tail) program =
      .ok (⟨prependCode code tailCode.code, reads ++ tailCode.reads⟩, final) := by
  induction related with
  | nil => exact compiled
  | cons _ operand _ ih =>
    simpa only [prependSource, prependCode, List.foldr_cons, List.append_assoc] using
      compileBody_plainSeq ⟨block.context, .local⟩ _ _ program program final _ _
        (compileBody_plainAssign _ _ _ _ _ program (resolves operand)) ih

theorem collects_prefix (source : List (String × SourceExpr)) {tail : Statement} {binders : List String}
    (collected : BodyBinders tail binders) : BodyBinders (prependSource source tail) (source.map Prod.fst ++ binders) := by
  induction source with
  | nil => exact collected
  | cons item rest ih =>
    change BodyBinders (Statement.seq (.assign item.1 item.2) (prependSource rest tail))
      ([item.1] ++ (rest.map Prod.fst ++ binders))
    exact .seq (.assign item.1 item.2) ih

theorem collects (body : Suite) : BodyBinders body.source body.binders := by
  induction body with
  | ret => exact .ret _
  | assign name rhs _ ih => exact .seq (.assign name rhs) ih

private theorem names_eq (parameters : Defaults.Parameters) :
    parameters.source.parameterNames = parameters.names := by
  simp [Defaults.Parameters.source, Defaults.Parameters.names, SourceSignature.parameterNames,
    List.map_append, List.map_map, Function.comp_def]

private theorem emits {globals : List String} {definition : Definition} (plan : Plan globals definition)
    (defaults : List PlainPositionalDefault)
    (same : defaults.map (fun item => (item.name, item.source)) = definition.parameters.optional)
    (tracked : ∀ item ∈ defaults, resolveTracked ⟨[], globals⟩ item.source = .ok (item.value, item.reads))
    (program : Program) :
    elaborateCommand ⟨⟨[], globals⟩, .global⟩ definition.command program =
      .ok (.exec (.define definition.name program.size),
        program.push (plan.declaration (defaults.map PlainPositionalDefault.value))) := by
  let parent : BlockContext := ⟨⟨[], globals⟩, .global⟩
  let layout : FunctionLayout := ⟨plan.locals, ⟨plan.block.context, .local⟩⟩
  have signature : definition.parameters.source =
      { positional := definition.parameters.required.map (fun name => ⟨name, none⟩) ++
          defaults.map PlainPositionalDefault.parameter } := by
    simp [Defaults.Parameters.source, ← same, List.map_map, PlainPositionalDefault.parameter, Function.comp_def]
  have localNames := Block.localNames_eq (collects definition.body)
  have localOrder := Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Block.local_names plan.binders
  have layoutBuilt : collectFunctionLayout parent.reads definition.parameters.source definition.body.source = .ok layout := by
    simp [collectFunctionLayout, localNames, functionLayout, names_eq, layout, parent, Plan.block,
      LexicalBlock.context, Except.map]
    simpa using localOrder
  rw [signature] at layoutBuilt
  have compiled := compile_suite plan.elaborates program
  have emitted := elaborateCommand_plainPositionalDefinition parent definition.name definition.parameters.required
    defaults definition.body.source program program layout _ tracked layoutBuilt compiled
  have readNames := names_eq definition.parameters
  rw [signature] at readNames
  have capture : captureNames (definition.parameters.names ++ plan.locals) plan.reads = plan.free :=
    Capture.captureNames_eq plan.selects
  have optional : defaults.map PlainPositionalDefault.resolved =
      ((definition.parameters.optional.map (fileSlot ∘ Prod.fst)).zip (defaults.map PlainPositionalDefault.value)).map
        (fun (slot, code) => (⟨slot, some code⟩ : Parameter)) := by
    simp [← same, List.map_map, List.zip_map', PlainPositionalDefault.resolved, Function.comp_def]
  change elaborateCommand parent (.define definition.name definition.parameters.source definition.body.source) program = _
  rw [signature, emitted, optional]
  simp [Plan.declaration, Defaults.Parameters.signature, layout, readNames, capture]

theorem compile_nested_body {globals enclosing : List String} (name : String) (parameters : Defaults.Parameters)
    {source : Statement} {occurrences locals : List String} (collected : BodyBinders source occurrences)
    (binders : LocalBinders parameters.names occurrences locals)
    (body : ResolvedBody) {free : List FreeName}
    (selected : Selects ⟨parameters.names ++ locals, enclosing, globals⟩ body.reads free)
    (defaults : List PlainPositionalDefault)
    (same : defaults.map (fun item => (item.name, item.source)) = parameters.optional)
    (tracked : ∀ item ∈ defaults, resolveTracked ⟨enclosing, globals⟩ item.source = .ok (item.value, item.reads))
    (seed middle : Program)
    (compiled : compileBody ⟨(LexicalBlock.mk (parameters.names ++ locals) enclosing globals).context, .local⟩
      source seed = .ok (body, middle)) :
    compileBody ⟨⟨enclosing, globals⟩, .local⟩ (.define name parameters.source source) seed =
      .ok (⟨.define (fileSlot name) middle.size,
          defaults.flatMap PlainPositionalDefault.reads ++ free.map FreeName.source⟩,
        middle.push ⟨parameters.signature (defaults.map PlainPositionalDefault.value), locals.map fileSlot, free, body.code⟩) := by
  let parent : BlockContext := ⟨⟨enclosing, globals⟩, .local⟩
  let layout : FunctionLayout := ⟨locals, ⟨(LexicalBlock.mk (parameters.names ++ locals) enclosing globals).context, .local⟩⟩
  have signature : parameters.source =
      { positional := parameters.required.map (fun name => ⟨name, none⟩) ++
          defaults.map PlainPositionalDefault.parameter } := by
    simp [Defaults.Parameters.source, ← same, List.map_map, PlainPositionalDefault.parameter, Function.comp_def]
  have localNames := Block.localNames_eq (collected)
  have localOrder := Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Block.local_names binders
  have layoutBuilt : collectFunctionLayout parent.reads parameters.source source = .ok layout := by
    simp [collectFunctionLayout, localNames, functionLayout, names_eq, layout, parent, LexicalBlock.context, Except.map]
    simpa using localOrder
  rw [signature] at layoutBuilt
  have emitted := compileBody_plainPositionalDefinition parent name parameters.required
    defaults source seed middle layout _ tracked layoutBuilt compiled
  have readNames := names_eq parameters
  rw [signature] at readNames
  have capture : captureNames (parameters.names ++ locals) body.reads = free :=
    Capture.captureNames_eq selected
  have optional : defaults.map PlainPositionalDefault.resolved =
      ((parameters.optional.map (fileSlot ∘ Prod.fst)).zip (defaults.map PlainPositionalDefault.value)).map
        (fun (slot, code) => (⟨slot, some code⟩ : Parameter)) := by
    simp [← same, List.map_map, List.zip_map', PlainPositionalDefault.resolved, Function.comp_def]
  change compileBody parent (.define name parameters.source source) seed = _
  rw [signature, emitted, optional]
  simp [Defaults.Parameters.signature, layout, readNames, capture]

theorem compile_nested {globals enclosing : List String} {definition : Definition}
    (plan : Plan globals definition enclosing)
    (defaults : List PlainPositionalDefault)
    (same : defaults.map (fun item => (item.name, item.source)) = definition.parameters.optional)
    (tracked : ∀ item ∈ defaults, resolveTracked ⟨enclosing, globals⟩ item.source = .ok (item.value, item.reads))
    (program : Program) :
    compileBody ⟨⟨enclosing, globals⟩, .local⟩
        (.define definition.name definition.parameters.source definition.body.source) program =
      .ok (⟨.define (fileSlot definition.name) program.size,
          defaults.flatMap PlainPositionalDefault.reads ++ plan.free.map FreeName.source⟩,
        program.push (plan.declaration (defaults.map PlainPositionalDefault.value))) :=
  compile_nested_body definition.name definition.parameters (collects definition.body) plan.binders
    ⟨plan.code, plan.reads⟩ plan.selects defaults same tracked program program (compile_suite plan.elaborates program)

theorem operand_origins {block : LexicalBlock} {source : SourceExpr} {code : Lowering.Expr}
    {reads : List Binding} (related : Operand block source code reads) :
    ∀ binding ∈ reads, ∃ origin, ReadOrigin block binding origin := by
  induction related with
  | read _ _ resolved =>
    intro binding member
    cases List.mem_singleton.mp member
    exact ⟨_, resolved⟩
  | int => simp
  | index _ _ first tail =>
    intro binding member
    exact (List.mem_append.mp member).elim (first binding) (tail binding)
  | list _ ih => exact ih

theorem prefix_read_origins {block : LexicalBlock}
    {source : List (String × SourceExpr)} {code : List (String × Lowering.Expr)}
    {reads : List Binding} (related : ElaboratesPrefix block source code reads) :
    ∀ binding ∈ reads, ∃ origin, ReadOrigin block binding origin := by
  induction related with
  | nil => simp
  | cons _ operand _ tail =>
    intro binding member
    exact (List.mem_append.mp member).elim (operand_origins operand binding) (tail binding)

theorem body_origins {block : LexicalBlock} {source : Suite}
    {code : Silmaril.Languages.Starlark.Functions.Body} {reads : List Binding}
    (related : Elaborates block source code reads) :
    ∀ binding ∈ reads, ∃ origin, ReadOrigin block binding origin := by
  induction related with
  | ret operand => exact operand_origins operand
  | assign _ operand _ ih =>
    intro binding member
    exact (List.mem_append.mp member).elim (operand_origins operand binding) (ih binding)

theorem plan_of_suite (globals : List String) (definition : Definition) (locals : List String)
    (enclosing : List String := [])
    {code : Silmaril.Languages.Starlark.Functions.Body} {reads : List Binding}
    (binders : LocalBinders definition.parameters.names definition.body.binders locals)
    (related : Elaborates ⟨definition.parameters.names ++ locals, enclosing, globals⟩ definition.body code reads) :
    Nonempty (Plan globals definition enclosing) := by
  obtain ⟨free, selected⟩ := Capture.selects_of_origins _ (body_origins related)
  exact ⟨⟨locals, code, reads, free, binders, related, selected⟩⟩

theorem emission {globals : List String} {definition : Definition} (admitted : Admitted globals definition) :
    ∃ (plan : Plan globals definition) (codes : List Lowering.Expr),
      (∀ program, elaborateCommand ⟨⟨[], globals⟩, .global⟩ definition.command program =
        .ok (.exec (.define definition.name program.size), program.push (plan.declaration codes))) ∧
      codes.length = definition.parameters.optional.length ∧
      ∀ state, ∃ out, Defaults.Evaluates globals state (definition.parameters.optional.map Prod.snd) codes out ∧
        (∀ values next, out = .ok values next → Bindings.Preserves state next) := by
  obtain ⟨plan⟩ := admitted.body
  obtain ⟨defaults, identified, tracked, eval⟩ := Defaults.evaluates_from_source admitted.defaults
  refine ⟨plan, _, emits plan defaults identified tracked, ?_, eval⟩
  rw [← identified]
  simp

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body
