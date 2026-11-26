module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Operands
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Spread
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Binder
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named

open Silmaril.Languages.Starlark (Binding Scope)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive (Site)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call (BodyEntry ClosureAt)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named hiding Arguments
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Outcome Value)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow finishState)

theorem runs_at_reached {parent block : LexicalBlock} {formals : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent formals varargs kwargs scope)
    (bodyRuns : State → Outcome Flow → Prop)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (_checked : resolve commands linked = .ok resolved) (id : DeclarationId)
    (found : resolved.program[id]? = some site.declaration)
    (available : List DeclarationId) (permitted : id ∈ available)
    {name : String} (slot : Binding) {state defining : State} {address : Nat}
    (callee : Body.Evaluates block state (.scalar (.read name)) (Leaf.readOperand slot)
      (.ok (.function address) state))
    (record : ClosureAt site id defining state address)
    (enterReached : ∀ packed, Body.Keeps state.heap.size state packed →
      ∀ assigned : List (Binding × Value),
      let active := activate packed site.declaration record.captures assigned
      ∃ out, bodyRuns active out ∧ Exec resolved.program (withoutDeclaration available id) active site.body.code out ∧
        Body.Keeps packed.heap.size packed (finishState (Leaf.returnTo packed out)))
    {arguments : List Lowering.Resolve.SourceExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Arguments
      block arguments codes reads) (keywords : Operands block) (star : Option (Spread block) := none) (mapping : Option (Mapping block) := none) :
    ∃ out, RunsAt site bodyRuns block id name slot arguments codes keywords.source keywords.codes star mapping state out ∧
      ExecExpr resolved.program available state (expressionAt slot codes keywords.codes (star.map Spread.code) (mapping.map Mapping.code)) out ∧
      Lowering.denoteExpr resolved.program available (expressionAt slot codes keywords.codes (star.map Spread.code) (mapping.map Mapping.code)) state = out ∧
      Body.Keeps state.heap.size state (finishState out) :=
  Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.runs_actual_reached
    site bodyRuns resolved.program id available permitted slot callee record enterReached codes keywords.codes
    (star.map Spread.code) (mapping.map Mapping.code) _
    (actuals_total resolved.program available related keywords star mapping)
    (SiteBinding site) (Packs site.declaration.signature.varargs site.declaration.signature.kwargs)
    (fun _ _ => binds_total _ _ _ _ _ _) (by
      intro reached closure actual result _ binding
      cases result <;> exact prepare_exact site resolved.program available id permitted found closure actual binding)

theorem runs_at {parent block : LexicalBlock} {formals : List PlainKeywordParameter} {varargs kwargs : Option String} {scope : Scope}
    (site : Site parent formals varargs kwargs scope)
    (bodyRuns : State → Outcome Flow → Prop)
    {commands : List Command} {linked : Program} {resolved : ResolvedModule}
    (_checked : resolve commands linked = .ok resolved) (id : DeclarationId)
    (found : resolved.program[id]? = some site.declaration)
    (available : List DeclarationId) (permitted : id ∈ available)
    (enterBody : BodyEntry site resolved.program available id bodyRuns)
    {name : String} (slot : Binding) {state defining : State} {address : Nat}
    (callee : Body.Evaluates block state (.scalar (.read name)) (Leaf.readOperand slot)
      (.ok (.function address) state))
    (record : ClosureAt site id defining state address)
    {arguments : List Lowering.Resolve.SourceExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (related : Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Arguments
      block arguments codes reads) (keywords : Operands block) (star : Option (Spread block) := none) (mapping : Option (Mapping block) := none) :
    ∃ out, RunsAt site bodyRuns block id name slot arguments codes keywords.source keywords.codes star mapping state out ∧
      ExecExpr resolved.program available state (expressionAt slot codes keywords.codes (star.map Spread.code) (mapping.map Mapping.code)) out ∧
      Lowering.denoteExpr resolved.program available (expressionAt slot codes keywords.codes (star.map Spread.code) (mapping.map Mapping.code)) state = out ∧
      Body.Keeps state.heap.size state (finishState out) :=
  runs_at_reached site bodyRuns _checked id found available permitted slot callee record
    (fun packed preserved assigned =>
      enterBody packed defining record.captures record.installed
        (fun capture member => by
          obtain ⟨value, frozen, found⟩ := record.live capture member
          exact ⟨value, frozen, preserved.2 _ _ (Array.getElem?_eq_some_iff.mp found).choose found⟩) assigned) related keywords star mapping

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
