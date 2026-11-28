module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Defaults.Defs
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Module
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Run
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Escape.Scoped.Frame
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.Dispatch
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Heap
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Heap
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Leaf.Module

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults

open Silmaril.Languages.Starlark.Modules (globalSlot fileSlot Catalog Executes)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Block (ModuleBinders)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Outcome)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow)

local notation "Value" => Silmaril.Languages.Starlark.Lists.Value
local notation "Result" => Silmaril.Languages.Starlark.Modules.Result
local notation "ModuleCode" => Silmaril.Languages.Starlark.Modules.Command

private theorem return_sound (program : Program) (available : List DeclarationId) (caller : State)
    (definition : Trace.Defaults.Definition) (codes : List Lowering.Expr)
    (assigned : List (Silmaril.Languages.Starlark.Binding × Value)) {out : Outcome Value}
    (returned : ReturnsParameter caller definition codes assigned out) :
    ∃ bodyOut, Exec program available (activate caller (definition.emitted codes) [] assigned)
      (definition.emitted codes).body bodyOut ∧ Leaf.returnTo caller bodyOut = out := by
  let active := activate caller (definition.emitted codes) [] assigned
  let slot := fileSlot definition.returned
  have evaluated : ExecExpr program available active (Leaf.readOperand slot) (active.read (.bound slot)) :=
    .evaluates (calls := fun _ _ _ => False) (fun _ _ _ impossible => impossible.elim)
      (.atom trivial .read)
  cases returned with
  | read read =>
    exact ⟨_, .returnExpr evaluated, by
      simp [active, slot, State.read, read, Leaf.returnTo, Outcome.resume, pure, EStateM.pure, Lowering.callValue]⟩
  | error read =>
    exact ⟨_, .returnExpr evaluated, by
      simp [active, slot, State.read, read, Leaf.returnTo, Outcome.resume]⟩

private theorem return_keeps (caller : State) (definition : Trace.Defaults.Definition)
    (codes : List Lowering.Expr) (assigned : List (Silmaril.Languages.Starlark.Binding × Value))
    {value : Value} {next : State}
    (returned : ReturnsParameter caller definition codes assigned (.ok value next)) :
    Bindings.Preserves caller next := by
  cases returned
  exact Bindings.Preserves.of_old_cells rfl (fun index low => Wrapper.activation_preserves _ _ _ _ index low)

theorem call_step {before rest : List Command} {globals : List String} {callee destination : String}
    {arguments : List Lowering.Resolve.SourceExpr} {linked : Program} {resolved : ResolvedModule}
    (declared : ModuleBinders (before ++ invocation callee destination arguments :: rest) globals)
    (checked : resolve (before ++ invocation callee destination arguments :: rest) linked = .ok resolved)
    (known : Visible globals callee) (allowed : ∀ argument ∈ arguments, Trace.Operand globals argument)
    {state : State} {definition : Trace.Defaults.Definition}
    (saved : Saved resolved.program state callee definition) :
    ∃ out, Step resolved globals before.length state (invocation callee destination arguments) out ∧
      (∀ next, out = .ok () next → Bindings.Writes state destination next) := by
  obtain ⟨actuals, related⟩ := actuals_related arguments allowed
  have calleeCode := global_operand known
  have site := RootCall.checked_call_assignment_site before rest destination _ arguments _ actuals globals
    linked resolved declared checked calleeCode related
  rcases RootCall.operands_total related state with ⟨values, ran⟩ | ⟨error, failed⟩
  · obtain ⟨bound, binds⟩ := Defaults.binds_total (definition.parameters.slots saved.values) values
    cases bound with
    | error error =>
      exact ⟨.error (.runtime error) state, .call saved site calleeCode related (.rejected ran binds),
        fun _ impossible => nomatch impossible⟩
    | ok assigned =>
      let active := activate state (definition.emitted saved.codes) [] assigned
      cases read : active.bindingValue (fileSlot definition.returned) with
      | error error =>
        exact ⟨_, .call saved site calleeCode related (.returned ran binds (.error read)),
          fun _ impossible => nomatch impossible⟩
      | ok value =>
        have body : ReturnsParameter state definition saved.codes assigned (.ok value (restoreCaller state active)) :=
          .read read
        refine ⟨_, .call saved site calleeCode related (.returned ran binds body), ?_⟩
        intro next success
        cases success
        exact .commit _ value (return_keeps _ _ _ _ body)
  · have calleeRead : RootCall.Evaluates state (.scalar (.read callee)) (.ok (.function saved.address) state) := by
      simpa [State.read, saved.live.binding] using RootCall.Evaluates.name (state := state) callee
    exact ⟨.error (.runtime error) state,
      .ordinary (.operandError site calleeCode related (.cons calleeRead failed)), fun _ impossible => nomatch impossible⟩

theorem step_sound {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    {globals : List String} (checked : resolve commands linked = .ok resolved) (host : Catalog)
    {index : Nat} {state : State} {command : Command} {out : Result Unit}
    (stepped : Step resolved globals index state command out) :
    ∃ code, resolved.source.commands[index]? = some code ∧ Executes resolved.program host state code out := by
  let available := List.range resolved.program.size
  cases stepped with
  | ordinary step => exact Leaf.step_sound checked host step
  | definition step => exact Defaults.step_sound step host
  | @call _ callee destination definition arguments actuals out saved site related operands calls =>
    obtain ⟨id, codes, address, values, codeLength, valueLength, found, live⟩ := saved
    cases calls with
    | @rejected actualValues error evaluated bound =>
      obtain ⟨permitted, prepared⟩ := Defaults.checked_prepare_saved checked id definition codes found codeLength
        state address false values _ valueLength live.cell bound
      have evaluatedCall := RootCall.prepared_invocation_expr resolved.program available
        (declaration := definition.emitted codes) (captures := []) (result := .error error) permitted related operands
        live.binding evaluated prepared (.error error state) (by intro assigned impossible; cases impossible)
      exact ⟨_, site, .exec (code := .assignExpr _ _) (.assignExpr evaluatedCall)⟩
    | @returned actualValues assigned out evaluated bound returned =>
      obtain ⟨permitted, prepared⟩ := Defaults.checked_prepare_saved checked id definition codes found codeLength
        state address false values _ valueLength live.cell bound
      obtain ⟨bodyOut, ran, same⟩ := return_sound resolved.program (withoutDeclaration available id) _ _ _ _ returned
      have evaluatedCall := RootCall.prepared_invocation_expr resolved.program available
        (declaration := definition.emitted codes) (captures := []) (result := .ok assigned) permitted related operands
        live.binding evaluated prepared bodyOut (by intro assigned h; cases h; exact ran)
      subst out
      cases bodyOut <;> exact ⟨_, site, .exec (code := .assignExpr _ _) (.assignExpr evaluatedCall)⟩

  | @wrapper _ callee destination body arguments actuals values out root site related operands evaluated calls =>
    cases calls with
    | @rejected _ error bound =>
      have expression := RootCall.checked_invocation_expr checked related operands root.live.binding root.live.cell
        root.parentCode evaluated bound (.error error state) (by intro assigned impossible; cases impossible)
      exact ⟨_, site, .exec (code := .assignExpr _ _) (.assignExpr expression)⟩
    | @entered argument out returned =>
      have bound : Entry.Binds [body.parameter] [argument] (.ok [(fileSlot body.parameter, argument)]) :=
        .success (.cons .nil)
      obtain ⟨bodyOut, ran, same⟩ := Defaults.Escape.returns_sound resolved.program
        (withoutDeclaration available (root.childId + 1)) body root.admitted root.childId root.childCode state argument returned
      have expression := RootCall.checked_invocation_expr checked related operands root.live.binding root.live.cell
        root.parentCode evaluated bound bodyOut (by intro assigned equal; cases equal; exact ran)
      subst out
      cases bodyOut <;> exact ⟨_, site, .exec (code := .assignExpr _ _) (.assignExpr expression)⟩
  | bodyDefinition plan site found length executed =>
    have agreed := Defaults.definition_sound resolved.program available _ _ _ _ _ found
      (Defaults.signature_defaults _ _) length executed
    exact ⟨_, site, .exec (code := .define _ _) agreed.1⟩
  | @bodyCall _ callee destination definition arguments actuals values out saved site related operands evaluated calls =>
    have prepares {result : Except Silmaril.Languages.Starlark.Lists.Error
        (List (Silmaril.Languages.Starlark.Binding × Value))}
        (bound : Defaults.Binds (definition.parameters.slots saved.values) values result) :=
      Defaults.checked_prepare_signature checked saved.id definition.parameters (saved.plan.declaration saved.codes)
        saved.codes saved.found rfl saved.codeLength state saved.address false saved.captures saved.values values
        saved.valueLength saved.live.cell bound
    cases calls with
    | @rejected error bound =>
      obtain ⟨permitted, prepared⟩ := prepares bound
      have expression := RootCall.prepared_invocation_expr resolved.program available
        (declaration := saved.plan.declaration saved.codes) (captures := saved.captures) (result := .error error)
        permitted related operands saved.live.binding evaluated prepared (.error error state)
        (by intro assigned impossible; cases impossible)
      exact ⟨_, site, .exec (code := .assignExpr _ _) (.assignExpr expression)⟩
    | @entered assigned bodyOut bound executed =>
      obtain ⟨permitted, prepared⟩ := prepares bound
      have ran := Defaults.Body.runs_sound resolved.program (withoutDeclaration available saved.id) executed
      have expression := RootCall.prepared_invocation_expr resolved.program available
        (declaration := saved.plan.declaration saved.codes) (captures := saved.captures) (result := .ok assigned)
        permitted related operands saved.live.binding evaluated prepared bodyOut (by intro locals equal; cases equal; exact ran)
      cases bodyOut <;> exact ⟨_, site, .exec (code := .assignExpr _ _) (.assignExpr expression)⟩
  | @scopedCall _ callee destination spec arguments actuals values out root site related operands evaluated calls =>
    cases calls with
    | @rejected error bound =>
      have expression := RootCall.checked_invocation_expr checked related operands root.live.binding root.live.cell
        root.parentCode evaluated bound (.error error state) (by intro assigned impossible; cases impossible)
      exact ⟨_, site, .exec (code := .assignExpr _ _) (.assignExpr expression)⟩
    | @entered assigned out bound returned =>
      obtain ⟨bodyOut, ran, same⟩ := Defaults.Escape.Scoped.returns_sound root.names root.plan resolved.program
        (withoutDeclaration available (root.childId + 1)) root.childId root.childCode state root.captures root.installed root.cells assigned returned
      have expression := RootCall.checked_invocation_expr checked related operands root.live.binding root.live.cell
        root.parentCode evaluated bound bodyOut (by intro assigned equal; cases equal; exact ran)
      subst out
      cases bodyOut <;> exact ⟨_, site, .exec (code := .assignExpr _ _) (.assignExpr expression)⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.WithDefaults
