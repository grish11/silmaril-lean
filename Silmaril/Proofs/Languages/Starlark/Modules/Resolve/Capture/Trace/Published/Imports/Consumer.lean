module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Definition

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (fileSlot globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named (resolves_at)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Functions (Program)
local notation "CodeExpr" => Silmaril.Languages.Starlark.Functions.Lowering.Expr
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve (resolveExpr resolveTracked)
open Silmaril.Languages.Starlark.Lists (State)

local notation "SourceCommand" => Modules.Resolve.Command

theorem read_resolves {aliases : List String} {name : String} {globals : List String}
    (declared : name ∈ aliases ∨ name ∈ globals) :
    Assignment.ReadResolves (block aliases globals) name (Leaf.readOperand (readSlot aliases name)) [readSlot aliases name] ∧
    ∃ origin, ReadOrigin (block aliases globals) (readSlot aliases name) origin := by
  by_cases localName : name ∈ aliases
  · simp only [readSlot, ite_eq_left localName]
    exact ⟨.owned localName, ⟨_, .owned localName⟩⟩
  · have global := declared.resolve_left localName
    simpa [readSlot, localName, Leaf.readOperand, globalSlot] using And.intro
      (Assignment.ReadResolves.global (block := block aliases globals) localName (by simp [block]) global)
      (show ∃ origin, ReadOrigin (block aliases globals) (globalSlot name) origin from
        ⟨_, .module localName (by simp [block]) global⟩)

private theorem plain_assignment {context : BlockContext} {source : Silmaril.Languages.Starlark.Functions.Lowering.Resolve.SourceExpr}
    {name : String} {rhs : CodeExpr} {reads : List Binding} {program : Program}
    (resolved : resolveTracked context.reads source = .ok (rhs, reads)) :
    elaborateCommand context (.assign name source) program = .ok (.exec (.assignExpr name rhs), program) := by
  rw [elaborateCommand_assign, resolved]
  rfl

private theorem compiles_step {aliases globals} (step : Step aliases globals) (program : Program) :
    elaborateCommand ⟨(block aliases globals).context, .global⟩ step.source program = .ok (step.code program, step.emit program) := by
  cases step with
  | @assign name declared source rhs reads operand _ =>
    have resolved : resolveExpr (block aliases globals).context source [] = .ok (rhs, reads.reverse) := by
      simpa using Body.resolves_at operand []
    apply plain_assignment (reads := reads)
    change resolveTracked (block aliases globals).context source = .ok (rhs, reads)
    simp [resolveTracked, resolved, Except.map]
  | invoke call =>
    obtain ⟨resolved, origin, selected⟩ := read_resolves call.declared
    exact plain_assignment (resolves_at (readSlot aliases call.callee) (.read call.legal resolved selected)
      call.operands call.keywords call.star call.mapping)

  | define declaration => exact wrapper_compiles declaration program

theorem compiles_suite {aliases globals} (body : List (Step aliases globals)) (program : Program) :
    ((body.map Step.source).mapM (elaborateCommand ⟨(block aliases globals).context, .global⟩)) program =
      .ok (compileSuite program body) := by
  induction body generalizing program with
  | nil => rfl
  | cons first rest ih =>
    cases tail : compileSuite (first.emit program) rest with
    | mk code final =>
      simp [List.mapM_cons, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
        compiles_step, ih, compileSuite, tail]

theorem suite_names {aliases globals} (body : List (Step aliases globals)) :
    globalNames (body.map Step.source) = body.map Step.destination ∧ fileNames (body.map Step.source) = [] := by
  induction body with
  | nil => exact ⟨rfl, rfl⟩
  | cons head tail ih =>
    cases head <;> simp [globalNames, fileNames, Step.source, Step.destination, globalNames] at *
    all_goals exact ⟨ih.1, ih.2⟩

private theorem compiled_suite_files {aliases globals} (body : List (Step aliases globals)) (program : Program) :
    (compileSuite program body).1.flatMap (fun command => match command with
      | .load _ imports => imports.map Modules.Import.localName
      | _ => []) = [] := by
  induction body generalizing program with
  | nil => rfl
  | cons head tail ih => cases head <;> simpa [compileSuite, Step.code] using ih _

theorem ordered_layout (plan : OrderedConsumer) {program : Program} {consumer : ResolvedModule}
    (checked : resolve plan.commands program = .ok consumer) :
    consumer.program = (compileSuite program plan.body).2 ∧ consumer.source.commands = plan.code program ∧
    consumer.source.globals = plan.globals ∧ consumer.source.fileNames = plan.aliases := by
  let body := plan.body.map Step.source
  have suffixNames := suite_names plan.body
  have names (loads : List ImportSite) : globalNames (loads.map ImportSite.source ++ body) = plan.globals := by
    induction loads with
    | nil => exact suffixNames.1.trans plan.declared
    | cons head tail ih => exact ih
  have itemNames (site : ImportSite) : (site.bindings.map ImportBinding.item).map Modules.Import.localName =
      site.aliases := by
    simp [ImportSite.aliases, ImportBinding.item, List.map_map, Function.comp_def]
  have files (loads : List ImportSite) :
      fileNames (loads.map ImportSite.source ++ body) = loads.flatMap ImportSite.aliases := by
    induction loads with
    | nil => exact suffixNames.2
    | cons head tail ih =>
      change (head.bindings.map ImportBinding.item).map Modules.Import.localName ++
        fileNames (tail.map ImportSite.source ++ body) = head.aliases ++ tail.flatMap ImportSite.aliases
      rw [itemNames, ih]
  let context : BlockContext := ⟨(block (plan.aliases) plan.globals).context, .global⟩
  have sameContext : moduleBlock plan.commands = context := by
    change moduleBlock (plan.imports.map ImportSite.source ++ body) = context
    simp [moduleBlock, names, files, context, block, Assignment.LexicalBlock.context, OrderedConsumer.aliases]
  have compiledLoads (loads : List ImportSite) :
      (((loads.map ImportSite.source ++ body).mapM (elaborateCommand context))) program =
        .ok (loads.map ImportSite.code ++ (compileSuite program plan.body).1, (compileSuite program plan.body).2) := by
    induction loads with
    | nil => simpa [body, context, OrderedConsumer.aliases] using compiles_suite plan.body program
    | cons head tail ih =>
      have headCode : elaborateCommand context head.source program = .ok (head.code, program) := by
        cases items : head.bindings with
        | nil => exact (head.nonempty items).elim
        | cons item rest =>
          simpa [ImportSite.source, ImportSite.code, items] using
            elaborateCommand_load context head.label item.item (rest.map ImportBinding.item) program
      simp only [List.map_cons, List.cons_append, List.mapM_cons, bind, StateT.bind, Except.bind,
        pure, StateT.pure, Except.pure, headCode, ih]
  have detail := checked_of_resolve checked
  rw [elaborateCommands, sameContext] at detail
  obtain ⟨sameCode, sameTable⟩ := Prod.mk.inj (Except.ok.inj (detail.1.symm.trans (compiledLoads plan.imports)))
  refine ⟨sameTable, sameCode, detail.2.1.trans (names plan.imports), ?_⟩
  rw [Modules.Source.fileNames, detail.2.2.1, sameCode, List.nil_append, List.flatMap_append]
  let collect : Modules.Command → List String := fun
    | .load _ imports => imports.map Modules.Import.localName
    | _ => []
  change (plan.imports.map ImportSite.code).flatMap collect ++
    (compileSuite program plan.body).1.flatMap collect = plan.imports.flatMap ImportSite.aliases
  have empty : (compileSuite program plan.body).1.flatMap collect = [] := compiled_suite_files plan.body program
  rw [empty, List.append_nil]
  suffices ∀ loads : List ImportSite, (loads.map ImportSite.code).flatMap collect = loads.flatMap ImportSite.aliases from this _
  intro loads
  induction loads with
  | nil => rfl
  | cons head tail ih =>
    change (head.bindings.map ImportBinding.item).map Modules.Import.localName ++
      (tail.map ImportSite.code).flatMap collect = head.aliases ++ tail.flatMap ImportSite.aliases
    rw [itemNames, ih]

theorem consumer_layout (plan : Consumer) {program : Program} {consumer : ResolvedModule}
    (checked : resolve plan.commands program = .ok consumer) :
    consumer.program = (compileSuite program plan.body).2 ∧ consumer.source.commands = plan.code program ∧
    consumer.source.globals = plan.globals ∧ consumer.source.fileNames = [plan.alias] := by
  have names : globalNames plan.commands = plan.globals := by
    change globalNames (plan.body.map Step.source) = plan.globals
    exact (suite_names plan.body).1.trans plan.declared
  have files : fileNames plan.commands = [plan.alias] := by
    change plan.alias :: fileNames (plan.body.map Step.source) = [plan.alias]
    rw [(suite_names plan.body).2]
  have context : moduleBlock plan.commands = ⟨(block [plan.alias] plan.globals).context, .global⟩ := by
    simp [moduleBlock, names, files, block, Assignment.LexicalBlock.context]
  have compiled : elaborateCommands plan.commands program =
      .ok (plan.code program, (compileSuite program plan.body).2) := by
    rw [elaborateCommands, context]
    cases suite : compileSuite program plan.body
    simp [Consumer.commands, Consumer.code, List.mapM_cons, bind, StateT.bind, Except.bind, pure,
      StateT.pure, Except.pure, elaborateCommand_load, compiles_suite, suite]
  have detail := checked_of_resolve checked
  obtain ⟨sameCode, sameTable⟩ := Prod.mk.inj (Except.ok.inj (detail.1.symm.trans compiled))
  refine ⟨sameTable, sameCode, detail.2.1.trans names, ?_⟩
  rw [Modules.Source.fileNames, detail.2.2.1, sameCode, Consumer.code]
  exact congrArg (List.cons plan.alias) (compiled_suite_files plan.body program)

theorem preserves_emit {aliases globals} (step : Step aliases globals) (program : Program) :
    PreservesDeclarations program (step.emit program) := by
  intro id declaration found
  cases step with
  | assign | invoke => exact found
  | define relay =>
    simp [Step.emit, Array.getElem?_push, Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp found).choose, found]

theorem preserves_suite {aliases globals} (body : List (Step aliases globals)) (program : Program) :
    PreservesDeclarations program (compileSuite program body).2 := by
  induction body generalizing program with
  | nil => exact fun _ _ found => found
  | cons step rest ih =>
    intro id declaration found
    exact ih (step.emit program) id declaration (preserves_emit step program id declaration found)

theorem consumer_preserves (plan : Consumer) {program : Program} {consumer : ResolvedModule}
    (checked : resolve plan.commands program = .ok consumer) :
    PreservesDeclarations program consumer.program :=
  (consumer_layout plan checked).1.symm ▸ preserves_suite plan.body program

theorem import_agrees {plan : Consumer} {published : Modules.Published} {s : State} {out : Modules.Result Unit}
    (source : BindsAlias plan published s out) :
    Modules.bindImports (Modules.importsOf published plan.label [plan.item]) s = out := by
  cases source with
  | missing absent =>
    simp [Modules.importsOf, Modules.bindImports, Consumer.item, plan.publicName, absent, List.mapM_cons,
      bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure]
  | found loaded =>
    simp [Modules.importsOf, Modules.bindImports, Consumer.item, plan.publicName, loaded, List.mapM_cons,
      bind, Except.bind, pure, Except.pure]

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
