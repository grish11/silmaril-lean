module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.Defs
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Thms
public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Thms

import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall (DistinctOwned)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive (Site KeywordLexical lexical_defaults)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call (ClosureAt)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Value Capture)
open Silmaril.Languages.Starlark.Lists.Iteration (finishState)

theorem empty_live {block : LexicalBlock} (state : State) : Live (empty (block := block)) state := by
  intro name entry seen
  simp [empty] at seen

private theorem write_slots (state : State) (target : Binding) (value : Value) :
    (state.write target value).slots = state.slots := by
  unfold State.write
  split <;> try rfl
  split <;> rfl

private theorem at_after_keep {block : LexicalBlock} {entry : Entry block}
    {defining state next : State} {address : Nat} (record : ClosureAt entry.site entry.id defining state address)
    (kept : Body.Keeps state.heap.size state next) :
    Nonempty (ClosureAt entry.site entry.id defining next address) :=
  ⟨{ record with
      recorded := kept.2 _ _ (Array.getElem?_eq_some_iff.mp record.recorded).choose record.recorded
      live := fun capture member => by
        obtain ⟨value, frozen, cell⟩ := record.live capture member
        exact ⟨value, frozen, kept.2 _ _ (Array.getElem?_eq_some_iff.mp cell).choose cell⟩ }⟩

theorem keeps_live {block : LexicalBlock} {locals : Locals block} {state next : State}
    (live : Live locals state) (kept : Body.Keeps state.heap.size state next) : Live locals next := by
  intro name entry seen
  obtain ⟨slot, address, frozen, owner, cell, defining, ⟨record⟩⟩ := live name entry seen
  exact ⟨slot, address, frozen, (congrFun kept.1 _).trans owner,
    kept.2 _ _ (Array.getElem?_eq_some_iff.mp cell).choose cell, defining, at_after_keep record kept⟩

private theorem at_after_write {block : LexicalBlock} {entry : Entry block} {defining state : State}
    {address : Nat} (record : ClosureAt entry.site entry.id defining state address)
    (target : Binding) (value : Value) :
    Nonempty (ClosureAt entry.site entry.id defining (state.write target value) address) := by
  refine ⟨{ record with recorded := ?_, live := Body.capture_cells_written _ _ _ record.live }⟩
  by_cases slot : state.slots target = some (.owned address)
  · simp [State.write, slot, record.recorded]
  · exact (RootCall.write_other_cell _ _ _ _ slot).trans record.recorded

theorem write_live {block : LexicalBlock} {locals : Locals block} {state : State} {name : String}
    {entry : Option (Entry block)} (value : Value) (distinct : DistinctOwned state) (live : Live locals state)
    (new : ∀ known, entry = some known → ∃ slot previous frozen address defining,
      value = .function address ∧ state.slots (fileSlot name) = some (.owned slot) ∧
      state.heap[slot]? = some ⟨.binding previous, frozen⟩ ∧
      Nonempty (ClosureAt known.site known.id defining state address)) :
    Live (setLocal locals name entry) (state.write (fileSlot name) value) := by
  intro read known seen
  by_cases same : read = name
  · subst read
    obtain ⟨slot, previous, frozen, address, defining, rfl, owner, stored, ⟨record⟩⟩ :=
      new known (by simpa [setLocal] using seen)
    have valid := (Array.getElem?_eq_some_iff.mp stored).choose
    refine ⟨slot, address, frozen, (congrFun (write_slots _ _ _) _).trans owner, ?_, defining,
      at_after_write record _ _⟩
    simp [State.write, owner, stored, Array.getElem?_setIfInBounds_self_of_lt valid]
  · obtain ⟨slot, address, frozen, owner, stored, defining, ⟨record⟩⟩ :=
      live read known (by simpa [setLocal, same] using seen)
    have separated : state.slots (fileSlot name) ≠ some (.owned slot) := fun other =>
      same (congrArg Binding.name (distinct _ _ _ owner other))
    exact ⟨slot, address, frozen, (congrFun (write_slots _ _ _) _).trans owner,
      (RootCall.write_other_cell _ _ _ _ separated).trans stored, defining, at_after_write record _ _⟩

theorem evaluated_local {block : LexicalBlock} {locals : Locals block} {state : State}
    {name : String} {entry : Entry block} (live : Live locals state) (seen : locals name = some entry)
    (owned : name ∈ block.owned) :
    ∃ address defining, Body.Evaluates block state (.scalar (.read name)) (Leaf.readOperand (fileSlot name))
      (.ok (.function address) state) ∧ Nonempty (ClosureAt entry.site entry.id defining state address) := by
  obtain ⟨slot, address, frozen, owner, stored, defining, record⟩ := live name entry seen
  refine ⟨address, defining, ?_, record⟩
  have reads : state.read (.bound (fileSlot name)) = .ok (.function address) state := by
    simp only [State.read, State.bindingValue, owner, stored, Silmaril.Languages.Starlark.Lists.Slot.address]
  rw [← reads]
  exact .read (.owned owned)

theorem assigned_live {block : LexicalBlock} {locals : Locals block} {state middle : State} {name : String}
    {expression : Lowering.Resolve.SourceExpr} {code : Lowering.Expr} {entry : Option (Entry block)} {value : Value}
    (tracked : Tracks locals expression code entry)
    (ran : Body.Evaluates block state expression code (.ok value middle))
    (kept : Body.Keeps state.heap.size state middle)
    (live : Live locals state) (distinct : DistinctOwned state)
    {free : List FreeName} {floor : Nat} (frame : Body.Frame block free floor middle) (owned : name ∈ block.owned) :
    Live (setLocal locals name entry) (middle.write (fileSlot name) value) := by
  apply write_live value (by simpa [DistinctOwned, kept.1] using distinct) (keeps_live live kept)
  intro known tagged
  cases tracked with
  | forget => cases tagged
  | copy sourceOwned seen =>
    cases tagged
    obtain ⟨address, defining, read, record⟩ := evaluated_local live seen sourceOwned
    have unique {source : Lowering.Resolve.SourceExpr} {compiled : Lowering.Expr}
        {result : Silmaril.Languages.Starlark.Lists.Outcome Value}
        (term : Body.Evaluates block state source compiled result) :=
      Lowering.denoteExprWith_eq_of_evaluates (fun _ _ _ call => (exec_iff_denoteBody _ _ _ _ _).mp call)
        (Body.evaluates_with #[] [] (Lowering.coreClosureRuns #[] []) term)
    obtain ⟨rfl, rfl⟩ := EStateM.Result.ok.inj ((unique ran).symm.trans (unique read))
    obtain ⟨slot, previous, frozen, _, owner, stored⟩ := frame.owned name owned
    exact ⟨slot, previous, frozen, address, defining, rfl, owner, stored, record⟩

theorem installed_live {block : LexicalBlock} {locals : Locals block} {state installed : State}
    {formals : List PlainKeywordParameter} {varargs kwargs : Option String}
    (site : Site block formals varargs kwargs) (kw : KeywordLexical block formals)
    (id : DeclarationId) {captures : List Capture}
    (receipts : Installs state site.free captures) (cells : Body.CaptureCells state captures)
    (step : Nested.SiteResultFor block site.name site.defaultKeys site.defaultsInOrder id captures state (.ok .next installed))
    (live : Live locals state) (distinct : DistinctOwned state)
    {free : List FreeName} {floor : Nat} (frame : Body.Frame block free floor state) :
    Live (setLocal locals site.name (some ⟨id, formals, varargs, kwargs, site⟩)) installed := by
  cases step with
  | @installed saved next evaluated ran exactState _ _ =>
    rw [exactState]
    let record : Silmaril.Languages.Starlark.Lists.Cell := ⟨.function ⟨id, captures,
      site.defaultKeys.zip saved⟩, false⟩
    let grown : State := { evaluated with heap := evaluated.heap.push record }
    let address := evaluated.heap.size
    change Live _ (grown.write (fileSlot site.name) (.function address))
    have defaultsKept := Lexical.evaluates_keeps (lexical_defaults site kw) ran
    have growth : Body.Keeps evaluated.heap.size evaluated grown := by
      refine ⟨rfl, fun index cell below stored => ?_⟩
      simp [grown, Array.getElem?_push, Nat.ne_of_lt below, stored]
    have kept : Body.Keeps state.heap.size state grown := by
      refine ⟨growth.1.trans defaultsKept.1, fun index cell below stored => ?_⟩
      have next := defaultsKept.2 index cell below stored
      exact growth.2 index cell (Array.getElem?_eq_some_iff.mp next).choose next
    apply write_live (.function address) (by simpa [DistinctOwned, kept.1] using distinct) (keeps_live live kept)
    intro known same
    cases same
    obtain ⟨slot, previous, frozen, _, owner, stored⟩ := frame.owned site.name site.target
    have capturesLive : Body.CaptureCells grown captures := by
      intro capture member
      obtain ⟨value, frozen, cell⟩ := cells capture member
      exact ⟨value, frozen, kept.2 _ _ (Array.getElem?_eq_some_iff.mp cell).choose cell⟩
    refine ⟨slot, previous, frozen, address, state, rfl, (congrFun kept.1 _).trans owner,
      kept.2 _ _ (Array.getElem?_eq_some_iff.mp stored).choose stored, ?_⟩
    exact ⟨⟨captures, saved, false, Lexical.evaluated_length (lexical_defaults site kw) ran,
      Array.getElem?_push_size, receipts, capturesLive⟩⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance
