module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Defs
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Bindings.Heap
public import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.RootCall.Bindings

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Assignment (LexicalBlock)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Cell Slot Outcome Value)
open Silmaril.Languages.Starlark.Lists.Iteration (Flow finishState)
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve (SourceExpr)

private abbrev Direct (program : Program) (available : List DeclarationId)
    (state : State) (code : Lowering.Expr) (out : Outcome Value) :=
  Lowering.EvaluatesWith program available (fun _ _ _ => False) (fun _ => True) state code out

private theorem evaluates (program : Program) (available : List DeclarationId)
    {block : LexicalBlock} {state : State} {source : SourceExpr} {code : Lowering.Expr}
    {out : Outcome Value} (ran : Evaluates block state source code out) :
    Direct program available state code out := by
  induction ran with
  | read => exact .atom trivial .read
  | int => exact .atom trivial .scalar
  | index _ _ lhs rhs => exact .index lhs rhs
  | receiverError _ lhs => exact .indexReceiverError lhs
  | @list state element code out ran ih =>
    cases out with
    | error => exact .list (.headError ih)
    | ok => exact .list (.cons ih .empty)

theorem runs_sound (program : Program) (available : List DeclarationId)
    {block : LexicalBlock} {state : State} {source : Suite} {code : Silmaril.Languages.Starlark.Functions.Body}
    {out : Outcome Flow} (ran : Runs block state source code out) :
    Exec program available state code out := by
  have direct {state : State} {source : SourceExpr} {code : Lowering.Expr} {out : Outcome Value}
      (term : Evaluates block state source code out) : ExecExpr program available state code out :=
    .evaluates (fun _ _ _ impossible => impossible.elim) (evaluates program available term)
  induction ran with
  | ret term => exact .returnExpr (direct term)
  | assign term _ ih => exact .seq (.assignExpr (direct term)) ih
  | assignError term => exact .seqError (.assignExpr (direct term))

theorem prefix_sound (program : Program) (available : List DeclarationId)
    {block : LexicalBlock} {state : State} {source : List (String × SourceExpr)}
    {code : List (String × Lowering.Expr)} {result : Outcome Unit} (prefixRun : RunsPrefix block state source code result)
    (tail : Silmaril.Languages.Starlark.Functions.Body) (out : Outcome Flow)
    (continuation : ∀ state, result = .ok () state → Exec program available state tail out) :
    Exec program available state (prependCode code tail) (result.resume fun _ _ => out) := by
  have direct {state : State} {source : SourceExpr} {code : Lowering.Expr} {out : Outcome Value}
      (term : Evaluates block state source code out) : ExecExpr program available state code out :=
    .evaluates (fun _ _ _ impossible => impossible.elim) (evaluates program available term)
  induction prefixRun with
  | nil => exact continuation _ rfl
  | cons step _ ih => exact .seq (.assignExpr (direct step)) (ih continuation)
  | failed step => exact .seqError (.assignExpr (direct step))

theorem prefix_unique {block : LexicalBlock} {state : State} {source : List (String × SourceExpr)}
    {code : List (String × Lowering.Expr)} {a b : Outcome Unit}
    (first : RunsPrefix block state source code a) (second : RunsPrefix block state source code b) : a = b := by
  let tail : Silmaril.Languages.Starlark.Functions.Body := .returnExpr (.atom (.scalar (.int 0)))
  let finish : Outcome Unit → Outcome Flow := fun result =>
    result.resume fun _ state => .ok (.returned (.scalar (.int 0))) state
  have sound {result : Outcome Unit} (ran : RunsPrefix block state source code result) :
      Exec #[] [] state (prependCode code tail) (finish result) := by
    cases result with
    | error error residual =>
      exact prefix_sound #[] [] ran tail (.error error residual) (fun _ impossible => by cases impossible)
    | ok value residual =>
      cases value
      exact prefix_sound #[] [] ran tail (finish (.ok () residual)) (by
        intro reached equal
        cases equal
        exact .returnExpr (.evaluates (calls := fun _ _ _ => False) (fun _ _ _ h => h.elim) (.atom trivial .scalar)))
  have equal : finish a = finish b := ((exec_iff_denoteBody _ _ _ _ _).mp (sound first)).symm.trans
    ((exec_iff_denoteBody _ _ _ _ _).mp (sound second))
  cases a <;> cases b <;> simp_all [finish, Outcome.resume]

/-- The operand profile only extends the heap. In particular, each
existing slot and cell still denotes the same object after an error. -/
private def Extends (before after : State) : Prop :=
  after.slots = before.slots ∧
  ∀ (address : Nat) (cell : Cell), before.heap[address]? = some cell → after.heap[address]? = some cell

private theorem extend_refl (state : State) : Extends state state :=
  ⟨rfl, fun _ _ found => found⟩

private theorem extend_trans {first middle last : State} (firstStep : Extends first middle) (rest : Extends middle last) :
    Extends first last :=
  ⟨rest.1.trans firstStep.1, fun key cell found => rest.2 key cell (firstStep.2 key cell found)⟩

private theorem extend_push (state : State) (cell : Cell) : Extends state { state with heap := state.heap.push cell } := by
  refine ⟨rfl, ?_⟩
  intro address _ found
  have within := (Array.getElem?_eq_some_iff.mp found).choose
  simp [Array.getElem?_push, Nat.ne_of_lt within, found]

private theorem operands_total {block : LexicalBlock} {source : SourceExpr} {code : Lowering.Expr} {reads : List Binding}
    (scope : Operand block source code reads) (state : State) :
    ∃ out, Evaluates block state source code out ∧ Extends state (finishState out) := by
  induction scope generalizing state with
  | @read name binding origin legal lexical known =>
    exact ⟨_, .read lexical, by cases h : state.bindingValue binding <;>
      simpa [State.read, h, finishState] using extend_refl state⟩
  | int value => exact ⟨_, .int value, extend_refl _⟩
  | index _ _ head tail =>
    obtain ⟨out, first, keeps⟩ := head state
    cases out with
    | error => exact ⟨_, .receiverError first, keeps⟩
    | ok value middle =>
      obtain ⟨out, second, later⟩ := tail middle
      cases out with
      | error => exact ⟨_, .index first second, extend_trans keeps later⟩
      | ok key final =>
        exact ⟨_, .index first second, by
          change Extends state (finishState (Silmaril.Languages.Starlark.Lists.readIndex value key final))
          rw [RootCall.read_index_state]
          exact extend_trans keeps later⟩
  | list _ ih =>
    obtain ⟨out, item, kept⟩ := ih state
    cases out with
    | error => exact ⟨_, .list item, kept⟩
    | ok value middle => exact ⟨_, .list item, extend_trans kept (extend_push _ _)⟩

private theorem extends_keeps {state next : State} (floor : Nat) (kept : Extends state next) : Keeps floor state next :=
  ⟨kept.1, fun index cell _ found => kept.2 index cell found⟩

theorem keeps_trans {floor : Nat} {first middle last : State}
    (head : Keeps floor first middle) (tail : Keeps floor middle last) : Keeps floor first last :=
  ⟨tail.1.trans head.1, fun index cell low found => tail.2 index cell low (head.2 index cell low found)⟩

private theorem extend_frame {block : LexicalBlock} {free : List FreeName} {floor : Nat} {state next : State}
    (frame : Frame block free floor state) (kept : Extends state next) : Frame block free floor next := by
  constructor
  · intro name member
    obtain ⟨address, value, frozen, fresh, slot, cell⟩ := frame.owned name member
    exact ⟨address, value, frozen, fresh, kept.1 ▸ slot, kept.2 _ _ cell⟩
  · intro name member
    obtain ⟨address, value, frozen, bound, slot, cell⟩ := frame.captured name member
    exact ⟨address, value, frozen, bound, kept.1 ▸ slot, kept.2 _ _ cell⟩

theorem written_frame {block : LexicalBlock} {free : List FreeName} {floor : Nat}
    {state : State} {name : String} (member : name ∈ block.owned) (value : Value)
    (frame : Frame block free floor state) :
    Frame block free floor (state.write (fileSlot name) value) ∧ Keeps floor state (state.write (fileSlot name) value) := by
  obtain ⟨target, previous, frozen, fresh, owned, cell⟩ := frame.owned name member
  have other (index : Nat) (different : index ≠ target) :
      (state.write (fileSlot name) value).heap[index]? = state.heap[index]? :=
    RootCall.write_other_cell _ _ _ _ (by simp [owned, Ne.symm different])
  have same (index : Nat) (low : index < floor) : (state.write (fileSlot name) value).heap[index]? = state.heap[index]? :=
    other index (Nat.ne_of_lt (Nat.lt_of_lt_of_le low fresh))
  refine ⟨⟨?_, ?_⟩, slots_write _ _ _, fun index _ low found => (same index low).trans found⟩
  · intro key declared
    obtain ⟨index, previousValue, wasFrozen, low, slot, stored⟩ := frame.owned key declared
    have retained : (state.write (fileSlot name) value).slots (fileSlot key) = some (.owned index) := by
      rw [slots_write]
      exact slot
    by_cases sameTarget : index = target
    · subst index
      have within := (Array.getElem?_eq_some_iff.mp cell).choose
      refine ⟨target, some value, frozen, low, retained, ?_⟩
      simp only [State.write, owned, cell]
      exact Array.getElem?_setIfInBounds_self_of_lt within
    · exact ⟨index, previousValue, wasFrozen, low, retained, (other index sameTarget).trans stored⟩
  · intro key declared
    obtain ⟨index, value, frozen, bound, slot, stored⟩ := frame.captured key declared
    exact ⟨index, value, frozen, bound, by rw [slots_write]; exact slot, (same index bound).trans stored⟩

/-- Construct a trace from the independently elaborated body and the
entry frame. Each successful assignment advances the invariant. -/
theorem runs_total {block : LexicalBlock} {free : List FreeName} {floor : Nat}
    {source : Suite} {code : Silmaril.Languages.Starlark.Functions.Body} {reads : List Binding}
    (profile : Elaborates block source code reads) (state : State) (frame : Frame block free floor state) :
    ∃ out, Runs block state source code out ∧ Frame block free floor (finishState out) ∧
      Keeps floor state (finishState out) := by
  induction profile generalizing state with
  | ret operand =>
    obtain ⟨out, ran, kept⟩ := operands_total operand state
    cases out <;> exact ⟨_, .ret ran, extend_frame frame kept, extends_keeps floor kept⟩
  | assign owned operand _ ih =>
    obtain ⟨out, ran, kept⟩ := operands_total operand state
    cases out with
    | error => exact ⟨_, .assignError ran, extend_frame frame kept, extends_keeps floor kept⟩
    | ok value middle =>
      obtain ⟨valid, stable⟩ := written_frame owned value (extend_frame frame kept)
      obtain ⟨out, rest, valid, preserves⟩ := ih _ valid
      exact ⟨_, .assign ran rest, valid, keeps_trans (extends_keeps floor kept) (keeps_trans stable preserves)⟩

theorem prefix_total {block : LexicalBlock} {free : List FreeName} {floor : Nat}
    {source : List (String × SourceExpr)} {code : List (String × Lowering.Expr)} {reads : List Binding}
    (profile : ElaboratesPrefix block source code reads) (state : State) (frame : Frame block free floor state) :
    ∃ out, RunsPrefix block state source code out ∧ Frame block free floor (finishState out) ∧
      Keeps floor state (finishState out) := by
  induction profile generalizing state with
  | nil => exact ⟨_, .nil, frame, rfl, fun _ _ _ stored => stored⟩
  | cons owned operand _ ih =>
    obtain ⟨out, ran, kept⟩ := operands_total operand state
    cases out with
    | error => exact ⟨_, .failed ran, extend_frame frame kept, extends_keeps floor kept⟩
    | ok value middle =>
      obtain ⟨valid, stable⟩ := written_frame owned value (extend_frame frame kept)
      obtain ⟨out, rest, valid, preserves⟩ := ih _ valid
      exact ⟨_, .cons ran rest, valid, keeps_trans (extends_keeps floor kept) (keeps_trans stable preserves)⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body
