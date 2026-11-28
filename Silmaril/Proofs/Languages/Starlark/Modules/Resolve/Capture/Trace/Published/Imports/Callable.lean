module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Invariant
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Definition

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call (Arguments RunsActual BindingRule PackRule ClosureAt)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
  (RunsAt Operands Spread Mapping expressionAt runs_at runs_at_reached)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Outcome Capture Slot Cell)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow finishState)

theorem callable_found {origin program : Program} {state : State} {callee : Callee} {address : Nat}
    (extension : PreservesDeclarations origin program) (live : callee.At origin program state address) :
    program[callee.layout.id]? = some callee.layout.site.declaration := by
  cases live with
  | regular linked _ => exact extension _ _ linked.1
  | wrapper found _ _ _ _ _ => exact found

/-- Removing a wrapper still leaves every declaration up to its imported
callee, so all recursive calls have the required strictly smaller guard. -/
theorem invoke_callable {origin seed : Program} {source : List Modules.Resolve.Command} {resolved : ResolvedModule}
    (checked : resolve source seed = .ok resolved) (extension : PreservesDeclarations origin resolved.program)
    (callee : Callee) {available : List Nat}
    (guarded : List.Subset (List.range (callee.layout.id + 1)) available)
    {lexical : LexicalBlock} {name : String} (slot : Binding) {state : State} {address : Nat}
    (read : Body.Evaluates lexical state (.scalar (.read name)) (Leaf.readOperand slot) (.ok (.function address) state))
    (live : callee.At origin resolved.program state address)
    {arguments : List Lowering.Resolve.SourceExpr} {codes : List Lowering.Expr} {reads : List Binding}
    (operands : Arguments lexical arguments codes reads) (keywords : Operands lexical)
    (star : Option (Spread lexical)) (mapping : Option (Mapping lexical)) :
    ∃ out, RunsAt callee.layout.site callee.BodyRuns lexical callee.layout.id name slot arguments codes
      keywords.source keywords.codes star mapping state out ∧
      ExecExpr resolved.program available state (expressionAt slot codes keywords.codes (star.map Spread.code) (mapping.map Mapping.code)) out ∧
      Body.Keeps state.heap.size state (finishState out) := by
  induction callee generalizing available lexical name slot state address arguments codes reads with
  | regular entry =>
    cases live with
    | regular linked record =>
      have allowed : entry.id ∈ available := guarded (List.mem_range.mpr (Nat.lt_succ_self _))
      have body := enter_callable_below checked linked extension available
        (fun _ chosen => guarded (List.mem_range.mpr (Nat.lt_succ_of_lt (List.mem_range.mp chosen))))
      obtain ⟨out, source, native, _, kept⟩ := runs_at entry.site entry.BodyRuns checked entry.id
        (extension _ _ linked.1) available allowed body slot read record operands keywords star mapping
      exact ⟨out, source, native, kept⟩
  | @wrapper importName aliases globals declaration id imported ih =>
    cases live with
    | @wrapper _ _ _ _ _ _ defining _ cell target flag found earlier record captureEq stored original =>
      change List.Subset (List.range (id + 1)) available at guarded
      have allowed : id ∈ available := guarded (List.mem_range.mpr (Nat.lt_succ_self _))
      have bodyGuard : List.Subset (List.range (imported.layout.id + 1)) (withoutDeclaration available id) := by
        intro index member
        have lower := List.mem_range.mp member
        have below := Nat.lt_of_le_of_lt (Nat.lt_succ_iff.mp lower) earlier
        exact mem_withoutDeclaration.mpr ⟨guarded (List.mem_range.mpr (Nat.lt_succ_of_lt below)), Nat.ne_of_lt below⟩
      have body (packed : State) (kept : Body.Keeps state.heap.size state packed)
          (assigned : List (Binding × Lists.Value)) :
          let active := activate packed declaration.site.declaration record.captures assigned
          ∃ out, (Callee.wrapper declaration id imported).BodyRuns active out ∧
            Exec resolved.program (withoutDeclaration available id) active declaration.site.body.code out ∧
            Body.Keeps packed.heap.size packed (finishState (Leaf.returnTo packed out)) := by
        let capture : Capture := ⟨fileSlot importName, cell, true⟩
        let active := activate packed declaration.site.declaration [capture] assigned
        rw [captureEq]
        change ∃ out, (Callee.wrapper declaration id imported).BodyRuns active out ∧
          Exec resolved.program (withoutDeclaration available id) active declaration.site.body.code out ∧
          Body.Keeps packed.heap.size packed (finishState (Leaf.returnTo packed out))
        have slotFound : active.slots (fileSlot importName) = some (.captured cell true) :=
          wrapper_import_slot declaration packed cell assigned
        have previous : KeepsContents packed active := by
          intro address old present
          exact ⟨old.frozen, (Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper.activation_preserves packed
            declaration.site.declaration [capture] assigned address (Array.getElem?_eq_some_iff.mp present).choose).trans present⟩
        have transported := closure_cells_trans (closure_cells_of_keeps kept) (closure_cells_of_contents previous)
        obtain ⟨nextFlag, aliasStored⟩ := keeps_initialized transported stored
        have fromAlias : active.bindingValue (fileSlot importName) = .ok (.function target) := by
          simp [State.bindingValue, slotFound, Slot.address, aliasStored]
        obtain ⟨notOwned, enclosing⟩ := wrapper_import_origin declaration
        have calleeRead := Body.Evaluates.read (state := active)
          (Assignment.ReadResolves.enclosing (block := declaration.site.block) (name := importName)
            notOwned enclosing)
        change Body.Evaluates _ _ _ _ (active.read (.bound (fileSlot importName))) at calleeRead
        rw [State.read, fromAlias] at calleeRead
        obtain ⟨result, ran, interpreted, saved⟩ := ih bodyGuard (fileSlot importName) calleeRead
          (transport_callable original transported) declaration.operands declaration.keywords declaration.star declaration.mapping
        have finish : finishState (result.resume (fun value => pure (Flow.returned value))) = finishState result := by
          cases result <;> rfl
        refine ⟨_, ⟨result, ran, rfl⟩, .returnExpr interpreted,
          Body.returned_keeps packed declaration.site.declaration [capture] assigned _ ?_⟩
        rw [finish]
        exact ⟨saved.1, fun index old _ present => saved.2 index old
          (Array.getElem?_eq_some_iff.mp present).choose present⟩
      obtain ⟨out, source, native, _, kept⟩ := runs_at_reached declaration.site
        (Callee.BodyRuns (.wrapper declaration id imported)) checked id found available allowed slot read record body
        operands keywords star mapping
      exact ⟨out, source, native, kept⟩

theorem callable_return_link {origin program : Program} {state : State} {callee : Callee} {address : Nat}
    (live : callee.At origin program state address) {child : Callable} (returned : callee.returned = some child) :
    child.Linked origin := by
  induction live with
  | regular linked _ => exact returned_linked linked child returned
  | wrapper _ _ _ _ _ _ ih => exact ih returned

theorem callable_return_record (callee : Callee) {block : LexicalBlock} {name : String} {slot : Binding}
    {Bound : Type} {actuals : State → Outcome Actual → Prop} {binds : BindingRule Bound} {packs : PackRule Bound}
    {state reached : State} {value : Lists.Value}
    (ran : RunsActual callee.layout.site callee.BodyRuns block callee.layout.id name slot actuals binds packs state (.ok value reached))
    {child : Callable} (returned : callee.returned = some child) :
    ∃ address defining, value = .function address ∧ Nonempty (ClosureAt child.site child.id defining reached address) := by
  induction callee generalizing block name slot Bound actuals binds packs state reached value with
  | regular entry => exact returned_record ran child returned
  | wrapper declaration id imported ih =>
    generalize outcome : (EStateM.Result.ok value reached : Outcome Lists.Value) = out at ran
    cases ran with
    | calleeError | argumentError | bindingError => cases outcome
    | @invoked _ _ _ _ _ bodyOut _ _ _ _ _ _ _ body =>
      obtain ⟨inner, source, rfl⟩ := body
      cases inner with
      | error => cases outcome
      | ok result ready =>
        cases outcome
        obtain ⟨address, defining, valueAt, ⟨record⟩⟩ := ih source returned
        exact ⟨address, defining, valueAt, ⟨⟨record.captures, record.defaults, record.frozen, record.length,
          record.recorded, record.installed, record.live⟩⟩⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
