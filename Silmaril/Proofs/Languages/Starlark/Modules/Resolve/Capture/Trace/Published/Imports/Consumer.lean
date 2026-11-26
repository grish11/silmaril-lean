module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (fileSlot globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named (resolves_at)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Functions (Program)
local notation "CodeExpr" => Silmaril.Languages.Starlark.Functions.Lowering.Expr
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve (resolveExpr resolveTracked)
open Silmaril.Languages.Starlark.Lists (State)

local notation "SourceCommand" => Modules.Resolve.Command

theorem read_resolves {importName name : String} {globals : List String} (declared : name = importName ∨ name ∈ globals) :
    Assignment.ReadResolves (block importName globals) name (Leaf.readOperand (readSlot importName name)) [readSlot importName name] ∧
    ∃ origin, ReadOrigin (block importName globals) (readSlot importName name) origin := by
  by_cases same : name = importName
  · subst name
    simpa [readSlot, Leaf.readOperand, fileSlot] using And.intro
      (Assignment.ReadResolves.owned (block := block importName globals) (name := importName) (by simp [block]))
      (show ∃ origin, ReadOrigin (block importName globals) (fileSlot importName) origin from ⟨_, .owned (by simp [block])⟩)
  · have global := declared.resolve_left same
    have outside : name ∉ (block importName globals).owned := by simpa [block] using same
    simpa [readSlot, same, Leaf.readOperand, globalSlot] using And.intro
      (Assignment.ReadResolves.global (block := block importName globals) outside (by simp [block]) global)
      (show ∃ origin, ReadOrigin (block importName globals) (globalSlot name) origin from
        ⟨_, .module outside (by simp [block]) global⟩)

private theorem plain_assignment {context : BlockContext} {source : Silmaril.Languages.Starlark.Functions.Lowering.Resolve.SourceExpr}
    {name : String} {rhs : CodeExpr} {reads : List Binding} {program : Program}
    (resolved : resolveTracked context.reads source = .ok (rhs, reads)) :
    elaborateCommand context (.assign name source) program = .ok (.exec (.assignExpr name rhs), program) := by
  rw [elaborateCommand_assign, resolved]
  rfl

private theorem compiles_step {importName globals} (step : Step importName globals) (program : Program) :
    elaborateCommand ⟨(block importName globals).context, .global⟩ step.source program = .ok (step.code, program) := by
  cases step with
  | @assign name declared source rhs reads operand _ =>
    have resolved : resolveExpr (block importName globals).context source [] = .ok (rhs, reads.reverse) := by
      simpa using Body.resolves_at operand []
    apply plain_assignment (reads := reads)
    change resolveTracked (block importName globals).context source = .ok (rhs, reads)
    simp [resolveTracked, resolved, Except.map]
  | invoke call =>
    obtain ⟨resolved, origin, selected⟩ := read_resolves call.declared
    exact plain_assignment (resolves_at (readSlot importName call.callee) (.read call.legal resolved selected)
      call.operands call.keywords call.star call.mapping)

private theorem compiles_suite {importName globals} (body : List (Step importName globals)) (program : Program) :
    ((body.map Step.source).mapM (elaborateCommand ⟨(block importName globals).context, .global⟩)) program =
      .ok (body.map Step.code, program) := by
  induction body with
  | nil => rfl
  | cons first rest ih =>
    simp [List.mapM_cons, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, compiles_step, ih]

private theorem suite_names {importName globals} (body : List (Step importName globals)) :
    globalNames (body.map Step.source) = body.map Step.destination ∧ fileNames (body.map Step.source) = [] := by
  induction body with
  | nil => exact ⟨rfl, rfl⟩
  | cons head tail ih =>
    cases head <;> simp [globalNames, fileNames, Step.source, Step.destination, globalNames] at *
    all_goals exact ⟨ih.1, ih.2⟩

theorem consumer_layout (plan : Consumer) {program : Program} {consumer : ResolvedModule}
    (checked : resolve plan.commands program = .ok consumer) :
    consumer.program = program ∧ consumer.source.commands = plan.code ∧
    consumer.source.globals = plan.globals ∧ consumer.source.fileNames = [plan.alias] := by
  have names : globalNames plan.commands = plan.globals := by
    change globalNames (plan.body.map Step.source) = plan.globals
    exact (suite_names plan.body).1.trans plan.declared
  have files : fileNames plan.commands = [plan.alias] := by
    change plan.alias :: fileNames (plan.body.map Step.source) = [plan.alias]
    rw [(suite_names plan.body).2]
  have context : moduleBlock plan.commands = ⟨(block plan.alias plan.globals).context, .global⟩ := by
    simp [moduleBlock, names, files, block, Assignment.LexicalBlock.context]
  have compiled : elaborateCommands plan.commands program = .ok (plan.code, program) := by
    rw [elaborateCommands, context]
    simp [Consumer.commands, Consumer.code, List.mapM_cons, bind, StateT.bind, Except.bind, pure,
      StateT.pure, Except.pure, elaborateCommand_load, compiles_suite]
  have detail := checked_of_resolve checked
  obtain ⟨sameCode, sameTable⟩ := Prod.mk.inj (Except.ok.inj (detail.1.symm.trans compiled))
  refine ⟨sameTable, sameCode, detail.2.1.trans names, ?_⟩
  have noLoads : (plan.body.map Step.code).flatMap
      (fun command => match command with
        | .load _ imports => imports.map Modules.Import.localName
        | _ => []) = [] := by
    induction plan.body with
    | nil => rfl
    | cons head tail ih => cases head <;> simpa [Step.code] using ih
  rw [Modules.Source.fileNames, detail.2.2.1, sameCode, Consumer.code]
  change plan.alias :: _ = [plan.alias]
  exact congrArg (List.cons plan.alias) noLoads

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
