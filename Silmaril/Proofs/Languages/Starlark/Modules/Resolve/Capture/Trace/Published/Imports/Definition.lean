module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Lexical.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Thms
import Silmaril.Languages.Starlark.Modules.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (fileSlot globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive (compile_site)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call (ClosureAt)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
  (resolves_at runs_at)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (Capture Cell Slot State Outcome)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow finishState)

theorem wrapper_compiles {importName globals} (relay : WrapperDeclaration importName globals) (program : Program) :
    elaborateCommand ⟨(block importName globals).context, .global⟩ (.define relay.name relay.site.sourceSignature relay.site.source)
      program = .ok (.exec (.define relay.name program.size), program.push relay.site.declaration) := by
  have imported : Body.Operand relay.site.block (.scalar (.read importName))
      (Leaf.readOperand (fileSlot importName)) [fileSlot importName] :=
    .read relay.legalAlias
      (.enclosing (by change ¬ _ ∈ ([] : List String); simp) (by change _ ∈ [importName]; simp))
      (.enclosing (by change ¬ _ ∈ ([] : List String); simp) (by change _ ∈ [importName]; simp))
  have compiled : compileBody ⟨relay.site.block.context, .local⟩ relay.site.source program =
      .ok (relay.site.body, program) :=
    compileBody_plainReturn _ _ _ _ _
      (resolves_at _ imported relay.operands relay.keywords relay.star relay.mapping)
  exact elaborateCommand_nativeDefinition ⟨(block importName globals).context, .local⟩ .global
    relay.name relay.site.sourceSignature relay.site.source program (program.push relay.site.declaration)
    _ _ (compile_site relay.site .nil compiled)

theorem wrapper_returns {importName globals} (relay : WrapperDeclaration importName globals) {producer : Program} {consumer : ResolvedModule}
    {commands : List Modules.Resolve.Command} {seed : Program}
    (checked : resolve commands seed = .ok consumer) {callee : Callable}
    (extension : PreservesDeclarations producer consumer.program) (id : DeclarationId)
    (after : producer.size ≤ id)
    (known : callee.Linked producer) {installed defining : State} {origin aliasCell : Nat} {frozen : Bool}
    (record : ClosureAt callee.site callee.id defining installed origin)
    (aliasStored : installed.heap[aliasCell]? = some ⟨.binding (some (.function origin)), frozen⟩)
    (packed : State) (kept : Body.Keeps installed.heap.size installed packed) (assigned : List (Binding × Lists.Value)) :
    let capture : Capture := ⟨fileSlot importName, aliasCell, true⟩
    let active := activate packed relay.site.declaration [capture] assigned
    ∃ out, relay.Returns callee active out ∧
      Exec consumer.program (withoutDeclaration (List.range consumer.program.size) id)
        active relay.site.body.code out ∧
      Body.Keeps packed.heap.size packed (finishState (Leaf.returnTo packed out)) := by
  intro capture active
  let available := withoutDeclaration (List.range consumer.program.size) id
  have guarded : List.Subset (List.range producer.size) available := by
    intro index member
    have bound := List.mem_range.mp member
    have found : producer[index]? = some producer[index] := Array.getElem?_eq_getElem bound
    exact mem_withoutDeclaration.mpr ⟨List.mem_range.mpr (Array.getElem?_eq_some_iff.mp (extension _ _ found)).choose,
      Nat.ne_of_lt (Nat.lt_of_lt_of_le bound after)⟩
  have native := enter_callable_for checked known extension available guarded
  have extended := linked_extends known extension
  have present : callee.id ∈ available :=
    guarded (List.mem_range.mpr (Array.getElem?_eq_some_iff.mp known.1).choose)
  have captures : active.slots (fileSlot importName) = some (.captured aliasCell true) :=
    activate_capture packed relay.site.declaration [capture] capture assigned (by simp) (by change ¬ _ ∈ ([] : List Binding); simp)
  have stored := kept.2 _ _ (Array.getElem?_eq_some_iff.mp aliasStored).choose aliasStored
  have sameHeap (address : Nat) (cell : Cell) (found : packed.heap[address]? = some cell) :
      active.heap[address]? = some cell :=
    (Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper.activation_preserves packed
      relay.site.declaration [capture] assigned address (Array.getElem?_eq_some_iff.mp found).choose).trans found
  have aliasRead : active.bindingValue (fileSlot importName) = .ok (.function origin) := by
    simp [State.bindingValue, captures, Slot.address, sameHeap _ _ stored]
  have read := Body.Evaluates.read (state := active)
    (Assignment.ReadResolves.enclosing (block := relay.site.block) (name := importName)
      (by change ¬ _ ∈ ([] : List String); simp) (by change _ ∈ [importName]; simp))
  change Body.Evaluates _ _ _ _ (active.read (.bound (fileSlot importName))) at read
  rw [State.read, aliasRead] at read
  obtain ⟨packedRecord⟩ := keep_record record kept
  let reached : ClosureAt callee.site callee.id defining active origin := {
    packedRecord with
    recorded := sameHeap _ _ packedRecord.recorded
    live := fun selected member => by
      obtain ⟨value, flag, found⟩ := packedRecord.live selected member
      exact ⟨value, flag, sameHeap _ _ found⟩ }
  obtain ⟨result, source, exec, _, preserved⟩ :=
    runs_at callee.site callee.BodyRuns checked callee.id extended.1 available present
      native (fileSlot importName) read reached relay.operands relay.keywords relay.star relay.mapping
  have finished : finishState (result.resume (fun value => pure (Flow.returned value))) = finishState result := by
    cases result <;> rfl
  refine ⟨_, ⟨result, source, rfl⟩, .returnExpr exec, Body.returned_keeps packed relay.site.declaration
    [capture] assigned _ ?_⟩
  rw [finished]
  exact ⟨preserved.1, fun address cell _ found => preserved.2 address cell
    (Array.getElem?_eq_some_iff.mp found).choose found⟩

/-- Installation allocates the closure before the ordinary module write.
The heap extension alone keeps all earlier callable records. -/
theorem wrapper_allocates {importName globals} (relay : WrapperDeclaration importName globals) (program : Program) (id : Nat)
    (found : program[id]? = some relay.site.declaration) {state : State} {aliasCell : Nat}
    {value : Option Lists.Value} {frozen : Bool}
    (owned : state.slots (fileSlot importName) = some (.owned aliasCell))
    (stored : state.heap[aliasCell]? = some ⟨.binding value, frozen⟩) :
    ∃ grown, Body.Keeps state.heap.size state grown ∧
      Nonempty (ClosureAt relay.site id state grown state.heap.size) ∧
      let result := .ok Flow.next (grown.write (globalSlot relay.name) (.function state.heap.size))
      Lexical.DefinesFor (block importName globals) (globalSlot relay.name) id relay.site.free [] [] state result ∧
        Exec program (List.range program.size) state (.define (globalSlot relay.name) id) result := by
  let capture : Capture := ⟨fileSlot importName, aliasCell, true⟩
  have installed : Installs state relay.site.free [capture] := .cons (.enclosing owned) .nil
  let cell : Cell := ⟨.function ⟨id, [capture], []⟩, false⟩
  let grown : State := {state with heap := state.heap.push cell}
  have kept : Body.Keeps state.heap.size state grown := by
    exact ⟨rfl, fun address _ below present => by simp [grown, Array.getElem?_push, Nat.ne_of_lt below, present]⟩
  have source : Lexical.DefinesFor (block importName globals) (globalSlot relay.name) id relay.site.free [] [] state
      (.ok .next (grown.write (globalSlot relay.name) (.function state.heap.size))) := .installed .nil installed
  refine ⟨grown, kept, ⟨⟨[capture], [], false, rfl, Array.getElem?_push_size, installed, ?_⟩⟩, source,
    (Lexical.defines_agree program (List.range program.size) (globalSlot relay.name) id
      relay.site.parameters relay.site.declaration .nil found rfl source).1⟩
  intro selected member
  simp only [List.mem_singleton] at member
  subst selected
  exact ⟨value, frozen, kept.2 _ _ (Array.getElem?_eq_some_iff.mp stored).choose stored⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
