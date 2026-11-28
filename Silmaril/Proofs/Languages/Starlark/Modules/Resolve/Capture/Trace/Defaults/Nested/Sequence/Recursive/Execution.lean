module

public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Elaboration
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Capture Cell Value)
open Silmaril.Languages.Starlark.Lists.Iteration (finishState)

theorem runs {block : LexicalBlock} {source : Statement} {seed final : Program}
    {resolved : ResolvedBody} {emissions : Emissions}
    (profile : Elaborates block source seed resolved final emissions) (program : Program)
    (linked : PreservesDeclarations final program) (available : List DeclarationId)
    {before after : List Binding} {free : List FreeName} (selection : Selects block (before ++ resolved.reads ++ after) free)
    (state : State) {floor : Nat} (frame : Body.Frame block free floor state) :
    ∃ out, Runs block state source resolved.code out ∧ Body.Frame block free floor (finishState out) ∧
      Body.Keeps floor state (finishState out) ∧ Exec program available state resolved.code out ∧
      denoteBody program available resolved.code state = out := by
  induction profile generalizing state before after free with
  | straight body =>
    obtain ⟨out, ran, reached, kept, native, meaning⟩ := Body.body_agrees program available body state frame
    exact ⟨out, .straight ran, reached, kept, native, meaning⟩
  | @define parent leading leadingCode leadingReads rest seed childTable final tail descendants suffix
      site leadingProfile _ remaining _ ih =>
    have selectedDefinition : Selects parent ((before ++ leadingReads) ++ site.reads ++ (tail.reads ++ after)) free := by
      simpa only [List.append_assoc] using selection
    have selectedTail : Selects parent ((before ++ leadingReads ++ site.reads) ++ tail.reads ++ after) free := by
      simpa only [List.append_assoc] using selection
    have found := linked _ _ ((links remaining).1 _ _ Array.getElem?_push_size)
    refine Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.runs_definition program available leadingProfile site.target site.lexical
      (id := childTable.size) (childFree := site.free) frame ?_ ?_
    · intro active entered
      obtain ⟨captures, installed, _⟩ := installs site selectedDefinition entered
      obtain ⟨out, _, native, _, result⟩ := Nested.reached_site site.target site.lexical program available childTable.size
        site.declaration found rfl entered captures installed
      exact ⟨captures, out, installed, result, native⟩
    · intro active entered
      obtain ⟨out, ran, reached, kept, native, _⟩ := ih linked selectedTail active entered
      exact ⟨out, ran, reached, kept, native⟩

theorem runs_activated {parent : LexicalBlock} (site : Site parent) {seed final : Program}
    {emissions : Emissions} (profile : Elaborates site.block site.source seed site.body final emissions)
    (program : Program) (linked : PreservesDeclarations final program) (available : List DeclarationId)
    (caller defining : State) (captures : List Capture) (installed : Installs defining site.free captures)
    (cells : Body.CaptureCells caller captures) (assigned : List (Binding × Value)) :
    let active := activate caller site.declaration captures assigned
    ∃ out, Runs site.block active site.source site.body.code out ∧
      Body.Frame site.block site.free caller.heap.size (finishState out) ∧
      Exec program available active site.body.code out ∧ denoteBody program available site.body.code active = out ∧
      (let returned := finishState (Leaf.returnTo caller out)
       returned.slots = caller.slots ∧ returned.bindings = caller.bindings ∧
        ∀ (address : Nat) (cell : Cell), caller.heap[address]? = some cell → returned.heap[address]? = some cell) := by
  have codeLength : (site.defaults.map PlainPositionalDefault.value).length = site.parameters.optional.length := by
    simpa using congrArg List.length (Lexical.translates site.lexical).1
  have initial := Body.selected_frame site.block site.declaration
    (Body.signature_slots site.parameters site.locals _ codeLength) site.selects caller defining
    captures installed cells assigned
  have selection : Selects site.block ([] ++ site.body.reads ++ []) site.free := by simpa [Site.block] using site.selects
  obtain ⟨out, source, frame, kept, native, meaning⟩ :=
    runs profile program linked available selection _ initial
  refine ⟨out, source, frame, native, meaning, ?_⟩
  have preserved (address : Nat) (cell : Cell) (stored : caller.heap[address]? = some cell) :
      (finishState out).heap[address]? = some cell := by
    have low := (Array.getElem?_eq_some_iff.mp stored).choose
    have active := (Wrapper.activation_preserves caller site.declaration captures assigned address low).trans stored
    exact kept.2 address cell low active
  cases out <;> exact ⟨rfl, rfl, preserved⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive
