module

public import Silmaril.Proofs.Languages.Starlark.Functions.Lowering.Frame

public section

namespace Silmaril.Proofs.Languages.Starlark.Functions.Lowering

open Silmaril.Languages.Starlark (Binding)
open Silmaril.Languages.Starlark.Functions.Lowering
open Silmaril.Languages.Starlark.Lists

abbrev FrameAction {α : Type} (act : Meaning α) :=
  FrameIndependent act ∧ KeepsScope act

theorem actionPure {α : Type} (x : α) : FrameAction (pure x) :=
  ⟨framePure x, scopePure x⟩

theorem actionThrow {α : Type} (e : Error) : FrameAction (throw e : Meaning α) :=
  ⟨frameThrow e, scopeThrow e⟩

theorem actionBind {α β : Type} {act : Meaning α} {next : α → Meaning β}
    (h : FrameAction act) (k : ∀ a, FrameAction (next a)) :
    FrameAction (act >>= next) :=
  ⟨frameBind h.1 (fun a => (k a).1), scopeBind h.2 (fun a => (k a).2)⟩

theorem actionMap {α β : Type} (f : α → β) {act : Meaning α} (h : FrameAction act) :
    FrameAction (f <$> act) := by
  change FrameAction (act >>= fun a => pure (f a))
  exact actionBind h (fun _ => actionPure _)

theorem actionExcept {α : Type} (out : Except Error α) : FrameAction (fromExcept out) := by
  cases out
  · exact actionThrow _
  · exact actionPure _

theorem actionList (addr : Address) : FrameAction (listElements addr) :=
  ⟨frameList addr, scopeProject _ _⟩
theorem actionTuple (addr : Address) : FrameAction (tupleElements addr) :=
  ⟨frameTuple addr, scopeProject _ _⟩
theorem actionDict (addr : Address) : FrameAction (dictEntries addr) :=
  ⟨frameDict addr, scopeProject _ _⟩

theorem acquireAction (value : Value) : FrameAction (Iteration.acquireIterator value) := by
  cases value with
  | list => exact actionMap _ (actionMap _ (actionList _))
  | tuple => exact actionMap _ (actionMap _ (actionTuple _))
  | dict => exact actionMap _ (actionMap _ (actionDict _))
  | range => exact actionPure _
  | _ => exact actionMap _ (actionThrow _)

theorem actionAllocate (xs : List Value) : FrameAction (allocate xs) :=
  ⟨fun _ _ => rfl, fun _ => ⟨rfl, rfl⟩⟩
theorem actionAllocateTuple (xs : List Value) : FrameAction (allocateTuple xs) :=
  ⟨fun _ _ => rfl, fun _ => ⟨rfl, rfl⟩⟩
theorem actionAllocateDict (entries : List Entry) : FrameAction (allocateDict entries) :=
  ⟨fun _ _ => rfl, fun _ => ⟨rfl, rfl⟩⟩

private theorem key_rebind (s : State) (f : Binding → Option Value) (key : Value) :
    (rebind s f).keyOf key = s.keyOf key := by cases key <;> rfl

private theorem addEntry (entries : List Entry) (key value : Value) :
    FrameAction (addDisplayEntry entries key value) := by
  constructor
  · intro s f
    simp only [addDisplayEntry, key_rebind]
    cases hk : s.keyOf key with
    | error => rfl
    | ok code => by_cases existsKey : (findEntry code entries).isSome = true <;>
        simp [existsKey, mapFrame]
  · intro s
    simp only [addDisplayEntry]
    cases hk : s.keyOf key with
    | error => exact ⟨rfl, rfl⟩
    | ok code => by_cases existsKey : (findEntry code entries).isSome = true <;>
        simp [existsKey, SameScope, Iteration.finishState]

private theorem readSequenceAction (values : List Value) (index : Value) :
    FrameAction (readSequence values index) := by
  unfold readSequence
  exact actionBind (actionExcept _) fun _ => actionPure _

theorem indexAction (receiver index : Value) : FrameAction (readIndex receiver index) := by
  cases receiver with
  | scalar | builtin | function => exact actionThrow _
  | string | range => exact actionExcept _
  | list => exact actionBind (actionList _) (readSequenceAction · index)
  | tuple => exact actionBind (actionTuple _) (readSequenceAction · index)
  | dict address =>
    unfold readIndex readDict
    apply actionBind (actionDict address)
    intro entries
    constructor
    · intro s f
      dsimp only
      rw [key_rebind]
      cases h : s.keyOf index with
      | error => rfl
      | ok code => dsimp only; cases findEntry code entries <;> rfl
    · intro s
      dsimp only
      cases s.keyOf index with
      | error => exact ⟨rfl, rfl⟩
      | ok code => dsimp only; cases findEntry code entries <;> exact ⟨rfl, rfl⟩

theorem sliceAction (operands : List Value) : FrameAction (readSliceOperands operands) := by
  unfold readSliceOperands
  split
  next receiver start stop stride =>
    cases receiver with
    | list address =>
      exact actionBind (actionList address) fun _ => actionBind (actionExcept _) actionAllocate
    | tuple address =>
      exact actionBind (actionTuple address) fun _ => actionBind (actionExcept _) actionAllocateTuple
    | string | range => exact actionExcept _
    | _ => exact actionThrow _
  next => exact actionThrow _

theorem comparisonAction (op : ComparisonOp) (left right : Value) :
    FrameAction (Comparison.apply op left right) := by
  constructor
  · intro state bindings
    change Comparison.finish (Comparison.evaluate state.heap op left right) (rebind state bindings) =
      mapFrame (rebind · bindings) (Comparison.finish (Comparison.evaluate state.heap op left right) state)
    cases Comparison.evaluate state.heap op left right <;> rfl
  · intro state
    exact (actionExcept _).2 state

private theorem editAction (address : Address) (edit : Contents → Except Error Contents) :
    FrameAction (editCell address edit) := by
  unfold editCell
  have getScope : KeepsScope (getCell address) := by
    intro s
    unfold getCell
    cases s.heap[address]? <;> exact ⟨rfl, rfl⟩
  apply actionBind ⟨frameGetCell address, getScope⟩
  intro cell
  constructor
  · intro s f
    dsimp only
    by_cases frozen : cell.frozen = true
    · simp [frozen, mapFrame]
    · by_cases active : address ∈ s.iterators
      · simp [frozen, rebind, active, mapFrame]
      · simp [frozen, rebind, active, mapFrame]
        cases edit cell.contents
        · rfl
        · rename_i contents
          by_cases kind : cell.contents.sameMutableKind contents = true <;> simp [kind]
  · intro s
    dsimp only
    split
    · exact ⟨rfl, rfl⟩
    ·
      split
      · exact ⟨rfl, rfl⟩
      · split
        · exact ⟨rfl, rfl⟩
        · split <;> exact ⟨rfl, rfl⟩

theorem writeIndexScope (receiver index value : Value) : KeepsScope (writeIndex receiver index value) := by
  cases receiver with
  | list address =>
    unfold writeIndex updateCell
    apply scopeBind (actionList address).2
    intro elements
    exact scopeBind (actionExcept _).2 fun _ => (editAction _ _).2
  | dict address =>
    unfold writeIndex writeDict
    intro state
    exact (editAction address _).2 state
  | _ => exact scopeThrow _

theorem actionInsertDisplayEntry (receiver key value : Value) :
    FrameAction (insertDisplayEntry receiver key value) := by
  cases receiver with
  | dict address =>
    change FrameAction (dictEntries address >>= fun entries => addDisplayEntry entries key value >>= fun extended =>
      editCell address fun _ => .ok (.dict extended))
    exact actionBind (actionDict address) fun entries =>
      actionBind (addEntry entries key value) fun extended => editAction address (fun _ => .ok (.dict extended))
  | _ => exact actionThrow _

private theorem appendAction (address : Address) (value : Value) :
    FrameAction (appendAt address value) := by
  unfold appendAt updateCell
  apply actionBind
  · exact actionBind (actionList _) fun _ =>
      actionBind (actionExcept _) fun _ => editAction _ _
  · intro _
    exact actionPure _

theorem atomScope {α : Type} {code : Code α} (safe : AtomSafe code) :
    KeepsScope (denote code) := by
  induction safe with
  | bound =>
    intro s
    simp only [denote, State.read]
    split <;> exact ⟨rfl, rfl⟩
  | scalar | builtin | string | noEntries | empty | predeclared => exact scopePure _
  | list h ih => exact scopeBind ih fun _ => (actionAllocate _).2
  | tuple h ih => exact scopeBind ih fun _ => (actionAllocateTuple _).2
  | dict h ih => exact scopeBind ih fun _ => (actionAllocateDict _).2
  | entry _ _ _ e k v =>
    exact scopeBind e fun entries =>
      scopeBind k fun key => scopeBind v fun value => (addEntry entries key value).2
  | cons h₁ h₂ a b => exact scopeBind a fun _ => scopeBind b fun _ => scopePure _
  | index _ _ a b =>
    exact scopeBind a fun receiver =>
      scopeBind b fun index => (indexAction receiver index).2
  | slice _ ih => exact scopeBind ih fun operands => (sliceAction operands).2
  | compare _ _ left right =>
    exact scopeBind left fun a => scopeBind right fun b => (comparisonAction _ a b).2
  | append h₁ h₂ a b =>
    apply scopeBind a
    intro receiver
    cases receiver with
    | list address => exact scopeBind b fun value => (appendAction address value).2
    | _ => exact scopeThrow _

theorem atomTransport {α : Type} {code : Code α} (safe : AtomSafe code)
    {s t : State} (same : StateMatch 0 s t) :
    denote code t = mapFrame (rebind · t.bindings) (denote code s) := by
  induction safe generalizing s t with
  | bound safe =>
    simp only [denote, State.read, read_match same safe]
    split <;> simp [mapFrame, same_rebound same]
  | scalar | builtin | string | noEntries | empty | predeclared =>
    exact frameRun (framePure _) same
  | list h ih =>
    apply transportBind (ih same)
    intro a u _
    exact (actionAllocate a).1 u t.bindings
  | tuple h ih =>
    apply transportBind (ih same)
    intro a u _
    exact (actionAllocateTuple a).1 u t.bindings
  | dict h ih =>
    apply transportBind (ih same)
    intro a u _
    exact (actionAllocateDict a).1 u t.bindings
  | entry h₁ h₂ h₃ e k v =>
    apply transportBind (e same)
    intro entries u he
    have kept := atomScope h₁ s
    rw [he] at kept
    change SameScope u s at kept
    apply transportBind (k (scopeTransport same kept))
    intro key w hk
    have kept₂ := atomScope h₂ u
    change denote _ u = _ at hk
    rw [hk] at kept₂
    apply transportBind (v (scopeTransport same ⟨kept₂.1.trans kept.1, kept₂.2.trans kept.2⟩))
    intro value last _
    exact (addEntry entries key value).1 last t.bindings
  | cons h₁ h₂ a b =>
    apply transportBind (a same)
    intro head u he
    have kept := atomScope h₁ s
    rw [he] at kept
    change SameScope u s at kept
    apply transportBind (b (scopeTransport same kept))
    intro _ _ _
    rfl
  | index h₁ h₂ a b =>
    apply transportBind (a same)
    intro receiver u he
    have kept := atomScope h₁ s
    rw [he] at kept
    change SameScope u s at kept
    apply transportBind (b (scopeTransport same kept))
    intro index w _
    exact (indexAction receiver index).1 w t.bindings
  | slice _ ih =>
    apply transportBind (ih same)
    intro operands u _
    exact (sliceAction operands).1 u t.bindings
  | compare safeLeft _ left right =>
    apply transportBind (left same)
    intro a next ran
    have kept := atomScope safeLeft s
    rw [ran] at kept
    change SameScope next s at kept
    apply transportBind (right (scopeTransport same kept))
    intro b final _
    exact (comparisonAction _ a b).1 final t.bindings
  | append h₁ h₂ a b =>
    apply transportBind (a same)
    intro receiver u he
    cases receiver with
    | list address =>
      have kept := atomScope h₁ s
      rw [he] at kept
      change SameScope u s at kept
      apply transportBind (b (scopeTransport same kept))
      intro value w _
      exact (appendAction address value).1 w t.bindings
    | _ => rfl

end Silmaril.Proofs.Languages.Starlark.Functions.Lowering
