module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper.Defs

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Modules (fileSlot)
open Silmaril.Languages.Starlark.Functions (Program activate capturedSlots)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Wrapper
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding (Chain EmittedProgram)
open Silmaril.Languages.Starlark.Lists (Address Capture Cell Slot State)

local notation "Value" => Silmaril.Languages.Starlark.Lists.Value
local notation "ClosureFrame" => Silmaril.Languages.Starlark.Modules.Resolve.Capture.Forwarding.Frame

private def FreshOwned (bound : Nat) (state : State) : Prop :=
  bound ≤ state.heap.size ∧
  ∀ name address, state.slots name = some (.owned address) → bound ≤ address

private theorem pushed_read (state : State) (added : Cell) (index : Nat) (valid : index < state.heap.size) :
    (state.heap.push added)[index]? = state.heap[index]? := by
  simp [Array.getElem?_push, Nat.ne_of_lt valid]

private theorem allocate_fresh (bound : Nat) (state : State) (name : Binding) (fresh : FreshOwned bound state) :
    FreshOwned bound (state.allocateSlot name) := by
  refine ⟨Nat.le_trans fresh.1 (by simp [State.allocateSlot]), ?_⟩
  intro binding address found
  by_cases same : binding = name
  · have equal : state.heap.size = address := by simpa [State.allocateSlot, same] using found
    exact equal ▸ fresh.1
  · exact fresh.2 _ _ (by simpa [State.allocateSlot, same] using found)

private theorem allocate_all (names : List Binding) (bound : Nat) (state : State) (fresh : FreshOwned bound state) :
    let final := names.foldl State.allocateSlot state
    FreshOwned bound final ∧ ∀ index, index < bound → final.heap[index]? = state.heap[index]? := by
  induction names generalizing state with
  | nil => exact ⟨fresh, fun _ _ => rfl⟩
  | cons name rest ih =>
    have ⟨nextFresh, stable⟩ := ih _ (allocate_fresh bound state name fresh)
    exact ⟨nextFresh, fun index low => (stable index low).trans
      (pushed_read state _ index (Nat.lt_of_lt_of_le low fresh.1))⟩

private theorem write_low (bound : Nat) (state : State) (binding : Binding) (value : Value)
    (fresh : FreshOwned bound state) (index : Nat) (low : index < bound) :
    FreshOwned bound (state.write binding value) ∧ (state.write binding value).heap[index]? = state.heap[index]? := by
  unfold State.write
  split <;> try exact ⟨fresh, rfl⟩
  rename_i address found
  split <;> try exact ⟨fresh, rfl⟩
  have diff : address ≠ index := Nat.ne_of_gt (Nat.lt_of_lt_of_le low (fresh.2 _ _ found))
  exact ⟨⟨by simpa using fresh.1, fresh.2⟩, by simp [diff]⟩

private theorem write_fresh (bound : Nat) (state : State) (binding : Binding) (value : Value)
    (fresh : FreshOwned bound state) : FreshOwned bound (state.write binding value) := by
  unfold State.write
  split <;> try exact fresh
  split <;> try exact fresh
  exact ⟨by simpa using fresh.1, fresh.2⟩

private theorem write_all (arguments : List (Binding × Value)) (bound : Nat)
    (state : State) (fresh : FreshOwned bound state) :
    let final := arguments.foldl (fun next (name, value) => next.write name value) state
    FreshOwned bound final ∧ ∀ index, index < bound → final.heap[index]? = state.heap[index]? := by
  induction arguments generalizing state with
  | nil => exact ⟨fresh, fun _ _ => rfl⟩
  | cons head rest ih =>
    obtain ⟨finalFresh, last⟩ := ih _ (write_fresh bound state head.1 head.2 fresh)
    exact ⟨finalFresh, fun index low => (last index low).trans (write_low _ _ _ _ fresh index low).2⟩

private theorem activate_keeps (caller : State) (declaration : Silmaril.Languages.Starlark.Functions.Declaration)
    (captures : List Capture)
    (assigned : List (Binding × Value)) :
    let active := activate caller declaration captures assigned
    FreshOwned caller.heap.size active ∧ ∀ index, index < caller.heap.size → active.heap[index]? = caller.heap[index]? := by
  let blank := { caller with bindings := fun _ => none, slots := capturedSlots captures }
  have fresh : FreshOwned caller.heap.size blank := by
    refine ⟨Nat.le_refl _, ?_⟩
    intro binding address found
    simp only [blank, capturedSlots] at found
    cases lookup : captures.find? (fun capture => capture.binding == binding) <;> simp [lookup] at found
  obtain ⟨allocated, stable⟩ := allocate_all (declaration.signature.slots ++ declaration.locals)
    caller.heap.size blank fresh
  obtain ⟨finalFresh, fixed⟩ := write_all assigned caller.heap.size _ allocated
  exact ⟨finalFresh, fun index low => (fixed index low).trans (stable index low)⟩

theorem activation_fresh (caller : State) (declaration : Silmaril.Languages.Starlark.Functions.Declaration)
    (captures : List Capture) (assigned : List (Binding × Value)) (binding : Binding) (address : Address)
    (owned : (activate caller declaration captures assigned).slots binding = some (.owned address)) :
    caller.heap.size ≤ address :=
  (activate_keeps caller declaration captures assigned).1.2 binding address owned

theorem activation_preserves (caller : State) (declaration : Silmaril.Languages.Starlark.Functions.Declaration)
    (captures : List Capture) (assigned : List (Binding × Value)) (index : Nat) (low : index < caller.heap.size) :
    (activate caller declaration captures assigned).heap[index]? = caller.heap[index]? :=
  (activate_keeps caller declaration captures assigned).2 index low

theorem activated_write_preserves (caller : State) (frame : ClosureFrame) (captures : List Capture)
    (assigned : List (Binding × Value)) (target : Binding) (value : Value) (index : Nat)
    (low : index < caller.heap.size) :
    ((activate caller frame.declaration captures assigned).write target value).heap[index]? = caller.heap[index]? := by
  obtain ⟨fresh, fixed⟩ := activate_keeps caller frame.declaration captures assigned
  exact (write_low caller.heap.size _ target value fresh index low).2.trans (fixed index low)

theorem returned_preserves {seed : Program} {caller : State}
    {child : Chain} {frame childFrame : ClosureFrame}
    {rest : List ClosureFrame} {captures selected : List Capture} {assigned : List (Binding × Value)}
    {address : Address} {next : State}
    (returned : ReturnsChild seed caller child frame childFrame rest captures assigned selected
      (.ok (.function address) next)) :
    next.slots = caller.slots ∧
      ∀ index, index < caller.heap.size → next.heap[index]? = caller.heap[index]? := by
  cases returned
  refine ⟨rfl, ?_⟩
  intro index low
  let active := activate caller frame.declaration captures assigned
  obtain ⟨fresh, existing⟩ := activate_keeps caller frame.declaration captures assigned
  let added : Cell := ⟨.function ⟨(EmittedProgram seed rest).size, selected, []⟩, false⟩
  let grown := { active with heap := active.heap.push added }
  have grownFresh : FreshOwned caller.heap.size grown :=
    ⟨Nat.le_trans fresh.1 (by simp [grown, active]), fresh.2⟩
  have stable := (write_low caller.heap.size grown (fileSlot child.name) (.function active.heap.size)
    grownFresh index low).2
  exact stable.trans ((pushed_read active added index (Nat.lt_of_lt_of_le low fresh.1)).trans (existing index low))

theorem returned_assigns {seed : Program} {caller : State}
    {child : Chain} {frame childFrame : ClosureFrame}
    {rest : List ClosureFrame} {captures selected : List Capture} {assigned : List (Binding × Value)}
    {address : Address} {next : State}
    (returned : ReturnsChild seed caller child frame childFrame rest captures assigned selected
      (.ok (.function address) next))
    (destination : Binding) (slot : Address) (before : Option Value) (frozen : Bool)
    (owned : caller.slots destination = some (.owned slot))
    (cell : caller.heap[slot]? = some ⟨.binding before, frozen⟩) :
    (next.write destination (.function address)).bindingValue destination = .ok (.function address) := by
  obtain ⟨slots, stable⟩ := returned_preserves returned
  have retained := (stable slot (Array.getElem?_eq_some_iff.mp cell).choose).trans cell
  have own : next.slots destination = some (.owned slot) := slots ▸ owned
  have within := (Array.getElem?_eq_some_iff.mp retained).choose
  have written : next.write destination (.function address) =
      { next with heap := next.heap.setIfInBounds slot ⟨.binding (some (.function address)), frozen⟩ } := by
    simp [State.write, own, retained]
  rw [written]
  simp [State.bindingValue, own, Slot.address, within]

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Wrapper
