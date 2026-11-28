module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.Operands

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Block (ModuleBinders moduleBlock_eq)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall
open Silmaril.Languages.Starlark.Functions (Program)

local notation "SourceCommand" => Resolve.Command

private abbrev compileSegment (block : BlockContext) (commands : List SourceCommand) (program : Program) :=
  (commands.mapM (elaborateCommand block)) program

private theorem append_result (block : BlockContext) (before suffix : List SourceCommand)
    (program : Program) :
    compileSegment block (before ++ suffix) program = (do
      let (first, middle) ← compileSegment block before program
      let (last, final) ← compileSegment block suffix middle
      pure (first ++ last, final)) := by
  simp [compileSegment, List.mapM_append, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure]

private theorem cons_result (block : BlockContext) (first : SourceCommand) (rest : List SourceCommand)
    (program : Program) :
    compileSegment block (first :: rest) program = (do
      let (head, middle) ← elaborateCommand block first program
      let (tail, final) ← compileSegment block rest middle
      pure (head :: tail, final)) := by
  simp [compileSegment, List.mapM_cons, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure]

private theorem checked_segment {commands : List SourceCommand} {globals : List String}
    {linked : Program} {resolved : ResolvedModule}
    (binders : ModuleBinders commands globals) (checked : resolve commands linked = .ok resolved) :
    compileSegment ⟨(parentContext globals []).reads, .global⟩ commands linked =
      .ok (resolved.source.commands, resolved.program) := by
  have source : moduleBlock commands = ⟨(parentContext globals []).reads, .global⟩ :=
    moduleBlock_eq binders
  simpa only [elaborateCommands, source] using (checked_of_resolve checked).1

private theorem append_frame (program : Program) (frames : List Capture.Forwarding.Frame) {index : Nat} {declaration : Functions.Declaration}
    (found : program[index]? = some declaration) :
    (EmittedProgram program frames)[index]? = some declaration := by
  induction frames with
  | nil => exact found
  | cons frame rest ih =>
    have within := (Array.getElem?_eq_some_iff.mp ih).choose
    simp [EmittedProgram, Array.getElem?_push, Nat.ne_of_lt within, ih]

private theorem chain_step (globals : List String) (program : Program) (chain : Chain)
    (accepted : Accepted globals program [] chain) :
    ∃ head rest, Emits globals [] chain (head :: rest) ∧ Links program chain (head :: rest) ∧
      ScopedLeaves globals [] chain (head :: rest) ∧
      elaborateCommand ⟨(parentContext globals []).reads, .global⟩
        (.define chain.name (.required chain.parameters) chain.body) program =
        .ok (.exec (.define chain.name (EmittedProgram program rest).size), EmittedProgram program (head :: rest)) := by
  obtain ⟨head, rest, emits, linked, scopes, compiled⟩ := compile_chain_scoped accepted
  exact ⟨head, rest, emits, linked, scopes,
    elaborateCommand_requiredDefinition (parentContext globals []) .global _ _ _ _ _ _ _ compiled⟩

private theorem simple_step (globals : List String) (program : Program) (command : SourceCommand)
    (simple : (∃ name operand, command = .assign name operand) ∨ (∃ operand, command = .eval operand))
    {code : Modules.Command} {next : Program}
    (compiled : elaborateCommand ⟨(parentContext globals []).reads, .global⟩ command program = .ok (code, next)) :
    next = program := by
  rcases simple with ⟨name, operand, rfl⟩ | ⟨operand, rfl⟩
  · rw [elaborateCommand_assign] at compiled
    cases resolved : Functions.Lowering.Resolve.resolveTracked (parentContext globals []).reads operand <;>
      simp_all [Except.mapError, Except.map]
  · rw [elaborateCommand_eval] at compiled
    cases resolved : Functions.Lowering.Resolve.resolveTracked (parentContext globals []).reads operand <;>
      simp_all [Except.mapError, Except.map]

private theorem step_preserves {globals : List String} {head : SourceCommand} {rest : List SourceCommand}
    (profile : Segment globals (head :: rest)) (program next : Program) (code : Modules.Command)
    (compiled : elaborateCommand ⟨(parentContext globals []).reads, .global⟩ head program = .ok (code, next))
    {index : Nat} {declaration : Functions.Declaration} (found : program[index]? = some declaration) :
    next[index]? = some declaration := by
  cases profile with
  | assign => simpa [simple_step globals program _ (.inl ⟨_, _, rfl⟩) compiled] using found
  | eval => simpa [simple_step globals program _ (.inr ⟨_, rfl⟩) compiled] using found
  | define chain accepted _ =>
    obtain ⟨frame, frames, _, _, _, step⟩ := chain_step globals program chain (accepted program)
    rw [step] at compiled
    cases compiled
    exact append_frame program (frame :: frames) found
  | @emit name signature body rest emitted _ =>
    obtain ⟨declaration, step⟩ := emitted
    change elaborateCommand ⟨⟨[], globals⟩, .global⟩ (.define name signature body) program = _ at compiled
    rw [step program] at compiled
    cases compiled
    have within := (Array.getElem?_eq_some_iff.mp found).choose
    simp [Array.getElem?_push, Nat.ne_of_lt within, found]

  | @emitPair name signature body rest emitted _ =>
    obtain ⟨child, parent, step⟩ := emitted
    change elaborateCommand ⟨⟨[], globals⟩, .global⟩ (.define name signature body) program = _ at compiled
    rw [step program] at compiled
    cases compiled
    have within := (Array.getElem?_eq_some_iff.mp found).choose
    simp [Array.getElem?_push, Nat.ne_of_lt within, Nat.ne_of_lt (Nat.lt_succ_of_lt within), found]

private theorem segment_preserves {globals : List String} {commands : List SourceCommand}
    (profile : Segment globals commands) (program next : Program) (code : List Modules.Command)
    (compiled : compileSegment ⟨(parentContext globals []).reads, .global⟩ commands program = .ok (code, next))
    {index : Nat} {declaration : Functions.Declaration} (found : program[index]? = some declaration) :
    next[index]? = some declaration := by
  induction commands generalizing program next code with
  | nil =>
    change Except.ok ([], program) = .ok (code, next) at compiled
    cases compiled
    exact found
  | cons head rest ih =>
    rw [cons_result] at compiled
    cases first : elaborateCommand ⟨(parentContext globals []).reads, .global⟩ head program with
    | error error => simp [first, bind, Except.bind] at compiled
    | ok result =>
      rcases result with ⟨command, middle⟩
      cases tail : compileSegment ⟨(parentContext globals []).reads, .global⟩ rest middle with
      | error error => simp [first, tail, bind, Except.bind] at compiled
      | ok result =>
        rcases result with ⟨tailCode, final⟩
        simp [first, tail, bind, Except.bind] at compiled
        rcases compiled with ⟨rfl, rfl⟩
        have tailProfile : Segment globals rest := by cases profile <;> assumption
        exact ih tailProfile middle _ _ tail (step_preserves profile program middle command first found)

private theorem segment_length (block : BlockContext) (source : List SourceCommand)
    (program next : Program) (code : List Modules.Command)
    (compiled : compileSegment block source program = .ok (code, next)) :
    code.length = source.length := by
  induction source generalizing program next code with
  | nil =>
    change Except.ok ([], program) = .ok (code, next) at compiled
    cases compiled
    rfl
  | cons first rest ih =>
    rw [cons_result] at compiled
    cases selected : elaborateCommand block first program with
    | error error => simp [selected, bind, Except.bind] at compiled
    | ok selection =>
      rcases selection with ⟨command, middle⟩
      cases tail : compileSegment block rest middle with
      | error error => simp [selected, tail, bind, Except.bind] at compiled
      | ok result =>
        rcases result with ⟨tailCode, final⟩
        simp [selected, tail, bind, Except.bind] at compiled
        rcases compiled with ⟨rfl, rfl⟩
        simp [ih middle _ _ tail]

theorem checked_command_count {commands : List SourceCommand} {linked : Program} {resolved : ResolvedModule}
    (checked : resolve commands linked = .ok resolved) :
    resolved.source.commands.length = commands.length :=
  segment_length (moduleBlock commands) commands linked resolved.program resolved.source.commands
    (checked_of_resolve checked).1

private theorem split_site (block : BlockContext) (before after : List SourceCommand)
    (atSite : SourceCommand) (linked final : Program) (code : List Modules.Command)
    (compiled : compileSegment block (before ++ atSite :: after) linked = .ok (code, final)) :
    ∃ earlier later middle next command,
      compileSegment block before linked = .ok (earlier, middle) ∧
      elaborateCommand block atSite middle = .ok (command, next) ∧
      compileSegment block after next = .ok (later, final) ∧
      code = earlier ++ command :: later ∧ earlier.length = before.length := by
  rw [append_result] at compiled
  cases front : compileSegment block before linked with
  | error error => simp [front, bind, Except.bind] at compiled
  | ok result =>
    rcases result with ⟨earlier, middle⟩
    simp only [front, bind, Except.bind] at compiled
    rw [cons_result] at compiled
    cases step : elaborateCommand block atSite middle with
    | error error => simp [step, bind, Except.bind] at compiled
    | ok result =>
      rcases result with ⟨command, next⟩
      cases tail : compileSegment block after next with
      | error error => simp [step, tail, bind, Except.bind] at compiled
      | ok result =>
        rcases result with ⟨later, last⟩
        simp [step, tail, bind, Except.bind] at compiled
        rcases compiled with ⟨rfl, rfl⟩
        exact ⟨_, _, _, _, _, rfl, step, tail, rfl, segment_length block before linked _ _ front⟩

theorem checked_chain_scoped_site (before after : List SourceCommand) (chain : Chain) (globals : List String)
    (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (before ++ .define chain.name (.required chain.parameters) chain.body :: after) globals)
    (checked : resolve (before ++ .define chain.name (.required chain.parameters) chain.body :: after) linked =
      .ok resolved)
    (accepted : ∀ program, Accepted globals program [] chain) (suffixProfile : Segment globals after) :
    ∃ seed head frames, Emits globals [] chain (head :: frames) ∧ Links seed chain (head :: frames) ∧
      ScopedLeaves globals [] chain (head :: frames) ∧
      resolved.source.commands[before.length]? = some (.exec (.define chain.name (EmittedProgram seed frames).size)) ∧
      (∀ (index : Nat) (declaration : Functions.Declaration), (EmittedProgram seed (head :: frames))[index]? = some declaration →
        resolved.program[index]? = some declaration) := by
  obtain ⟨earlier, later, middle, next, code, _, step, tail, commands, length⟩ :=
    split_site _ before after _ linked _ _ (checked_segment binders checked)
  obtain ⟨head, frames, emits, links, scopes, actual⟩ := chain_step globals middle chain (accepted middle)
  rw [actual] at step
  cases step
  exact ⟨middle, head, frames, emits, links, scopes, by simp [commands, ← length],
    fun _ _ found => segment_preserves suffixProfile _ _ later tail found⟩

theorem checked_chain_site (before after : List SourceCommand) (chain : Chain) (globals : List String)
    (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (before ++ .define chain.name (.required chain.parameters) chain.body :: after) globals)
    (checked : resolve (before ++ .define chain.name (.required chain.parameters) chain.body :: after) linked =
      .ok resolved)
    (accepted : ∀ program, Accepted globals program [] chain) (suffixProfile : Segment globals after) :
    ∃ seed head frames, Emits globals [] chain (head :: frames) ∧ Links seed chain (head :: frames) ∧
      resolved.source.commands[before.length]? = some (.exec (.define chain.name (EmittedProgram seed frames).size)) ∧
      (∀ (index : Nat) (declaration : Functions.Declaration), (EmittedProgram seed (head :: frames))[index]? = some declaration →
        resolved.program[index]? = some declaration) := by
  obtain ⟨seed, head, rest, emits, links, _, site, keeps⟩ :=
    checked_chain_scoped_site before after chain globals linked resolved binders checked accepted suffixProfile
  exact ⟨seed, head, rest, emits, links, site, keeps⟩

theorem checked_root_site (before after : List SourceCommand) (chain : Chain) (globals : List String)
    (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (before ++ .define chain.name (.required chain.parameters) chain.body :: after) globals)
    (checked : resolve (before ++ .define chain.name (.required chain.parameters) chain.body :: after) linked =
      .ok resolved)
    (accepted : ∀ program, Accepted globals program [] chain) (suffixProfile : Segment globals after) :
    ∃ head frames id, Emits globals [] chain (head :: frames) ∧
      resolved.source.commands[before.length]? = some (.exec (.define chain.name id)) ∧
      resolved.program[id]? = some head.declaration := by
  obtain ⟨seed, head, frames, emits, _, command, keeps⟩ :=
    checked_chain_site before after chain globals linked resolved binders checked accepted suffixProfile
  exact ⟨head, frames, _, emits, command, keeps _ _ (by simp [EmittedProgram])⟩

theorem checked_single_emission (before after : List SourceCommand) (command : SourceCommand) (name : String)
    (globals : List String) (linked : Program) (resolved : ResolvedModule) (declaration : Functions.Declaration)
    (binders : ModuleBinders (before ++ command :: after) globals)
    (checked : resolve (before ++ command :: after) linked = .ok resolved)
    (suffix : Segment globals after)
    (emits : ∀ program, elaborateCommand ⟨(parentContext globals []).reads, .global⟩ command program =
      .ok (.exec (.define name program.size), program.push declaration)) :
    ∃ id, resolved.source.commands[before.length]? = some (.exec (.define name id)) ∧
      resolved.program[id]? = some declaration := by
  obtain ⟨earlier, later, middle, next, code, _, step, tail, commands, length⟩ :=
    split_site _ before after command linked _ _ (checked_segment binders checked)
  rw [emits middle] at step
  cases step
  exact ⟨middle.size, by simp [commands, ← length],
    segment_preserves suffix _ _ later tail (by simp)⟩

theorem checked_pair_emission (before after : List SourceCommand) (command : SourceCommand) (name : String)
    (globals : List String) (linked : Program) (resolved : ResolvedModule) (child : Functions.Declaration)
    (parent : Nat → Functions.Declaration)
    (binders : ModuleBinders (before ++ command :: after) globals)
    (checked : resolve (before ++ command :: after) linked = .ok resolved) (suffix : Segment globals after)
    (emits : ∀ program, elaborateCommand ⟨⟨[], globals⟩, .global⟩ command program =
      .ok (.exec (.define name (program.size + 1)), (program.push child).push (parent program.size))) :
    ∃ id, resolved.source.commands[before.length]? = some (.exec (.define name (id + 1))) ∧
      resolved.program[id]? = some child ∧ resolved.program[id + 1]? = some (parent id) := by
  obtain ⟨earlier, later, middle, next, code, _, step, tail, commands, length⟩ :=
    split_site _ before after command linked _ _ (checked_segment binders checked)
  have compiled := emits middle
  change elaborateCommand ⟨⟨[], globals⟩, .global⟩ command middle = _ at step
  rw [compiled] at step
  cases step
  refine ⟨middle.size, by simp [commands, ← length], ?_, ?_⟩
  · exact segment_preserves suffix _ _ later tail (by simp [Array.getElem?_push])
  · apply segment_preserves suffix _ _ later tail
    exact (by
      rw [← Array.size_push (xs := middle) (v := child)]
      exact Array.getElem?_push_size)

theorem checked_eval_site (before after : List SourceCommand)
    (source : Functions.Lowering.Resolve.SourceExpr) (code : Functions.Lowering.Expr) (reads : List Binding)
    (globals : List String) (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (before ++ .eval source :: after) globals)
    (checked : resolve (before ++ .eval source :: after) linked = .ok resolved)
    (operand : Functions.Lowering.Resolve.resolveTracked ⟨[], globals⟩ source = .ok (code, reads)) :
    resolved.source.commands[before.length]? = some (.exec (.evalExpr code)) := by
  obtain ⟨earlier, later, middle, next, command, _, step, _, commands, length⟩ :=
    split_site _ before after (.eval source) linked _ _ (checked_segment binders checked)
  have resolvedOperand : Functions.Lowering.Resolve.resolveTracked (parentContext globals []).reads source =
      .ok (code, reads) := operand
  rw [elaborateCommand_eval, resolvedOperand] at step
  cases step
  simp [commands, ← length]

theorem checked_assign_site (before after : List SourceCommand) (destination : String)
    (source : Functions.Lowering.Resolve.SourceExpr) (code : Functions.Lowering.Expr) (reads : List Binding)
    (globals : List String) (linked : Program) (resolved : ResolvedModule)
    (binders : ModuleBinders (before ++ .assign destination source :: after) globals)
    (checked : resolve (before ++ .assign destination source :: after) linked = .ok resolved)
    (operand : Functions.Lowering.Resolve.resolveTracked ⟨[], globals⟩ source = .ok (code, reads)) :
    resolved.source.commands[before.length]? = some (.exec (.assignExpr destination code)) := by
  obtain ⟨earlier, later, middle, next, command, _, step, _, commands, length⟩ :=
    split_site _ before after (.assign destination source) linked _ _ (checked_segment binders checked)
  have resolvedOperand : Functions.Lowering.Resolve.resolveTracked (parentContext globals []).reads source =
      .ok (code, reads) := operand
  rw [elaborateCommand_assign, resolvedOperand] at step
  cases step
  simp [commands, ← length]

private theorem writes_compile {globals : List String} {name : String} {state final : Lists.State}
    {source : List SourceCommand} {code : List Modules.Command}
    (writes : Writes globals name state source code final) (program : Program) :
    compileSegment ⟨(parentContext globals []).reads, .global⟩ source program = .ok (code, program) := by
  induction writes with
  | nil => rfl
  | @cons state final destination rhs compiled value rest commands unrelated related evaluated writes ih =>
    obtain ⟨reads, operand⟩ := resolves_operand related
    have resolvedOperand : Functions.Lowering.Resolve.resolveTracked (parentContext globals []).reads rhs =
        .ok (compiled, reads) := operand
    simp [cons_result, elaborateCommand_assign, resolvedOperand, Except.mapError, Except.map, ih,
      bind, Except.bind, pure, Except.pure]

theorem checked_writes_site (before after : List SourceCommand) {source : List SourceCommand}
    {code : List Modules.Command} {globals : List String} {name : String}
    {state final : Lists.State} (writes : Writes globals name state source code final)
    {linked : Program} {resolved : ResolvedModule} (binders : ModuleBinders (before ++ source ++ after) globals)
    (checked : resolve (before ++ source ++ after) linked = .ok resolved) :
    ∃ earlier later, earlier.length = before.length ∧ resolved.source.commands = earlier ++ code ++ later := by
  let block : BlockContext := ⟨(parentContext globals []).reads, .global⟩
  have compiled : compileSegment block (before ++ source ++ after) linked =
      .ok (resolved.source.commands, resolved.program) := checked_segment binders checked
  rw [List.append_assoc, append_result] at compiled
  cases front : compileSegment block before linked with
  | error error => simp [front, bind, Except.bind] at compiled
  | ok result =>
    rcases result with ⟨earlier, middle⟩
    simp only [front, bind, Except.bind] at compiled
    rw [append_result, writes_compile writes middle] at compiled
    cases tail : compileSegment block after middle with
    | error error => simp [tail, bind, Except.bind] at compiled
    | ok result =>
      rcases result with ⟨later, last⟩
      simp [tail, bind, Except.bind, pure, Except.pure] at compiled
      exact ⟨earlier, later, segment_length _ _ _ _ _ front, by rw [← compiled.1, List.append_assoc]⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall
