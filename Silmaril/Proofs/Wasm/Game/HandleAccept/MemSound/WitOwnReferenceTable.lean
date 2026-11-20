module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.ReferenceTable.Defs

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnReferenceTable

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime
open Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own
open Silmaril.Wasm.Game.HandleAccept.Wit
open ReferenceTable

variable {E : CoreEngine}

theorem lookup_ownerAt (store : CStore E) (inst : InstId) (resource : RtId) (slot : BitVec 32) :
    (snapshot store inst).lookup resource.idx slot =
      (ownerAt store inst resource slot).map Resources.Owned.representation := by
  unfold snapshot RT.lookup ownerAt
  cases observed : atSlot store inst slot with
  | none => simp [observed]
  | some entry =>
    obtain ⟨identity, handle⟩ := entry
    cases handle with
    | mk type rep own lends scope =>
      cases type
      cases resource
      simp [observed, guard, and_left_comm, and_comm]
      split <;> rfl

private theorem run_get {Value : Type} (store : CStore E) (next : CStore E → P E Unit Value) :
    Stored.Endpoints.Core.runLocal (getStore >>= next) store =
      Stored.Endpoints.Core.runLocal (next store) store := by rfl

private theorem run_modify {Value : Type} (store : CStore E) (update : CStore E → CStore E)
    (next : Unit → P E Unit Value) :
    Stored.Endpoints.Core.runLocal (modifyStore update >>= next) store =
      Stored.Endpoints.Core.runLocal (next ()) (update store) := by rfl

private theorem run_trap {Before Value : Type} (store : CStore E) (reason : TrapReason)
    (next : Before → P E Unit Value) :
    Stored.Endpoints.Core.runLocal (trap reason >>= next) store = (store, .error (.trapped reason)) := by rfl

theorem take_removes_first (limits : Component.Limits) (cx : LiftLowerContext E)
    (store : CStore E) (slot : BitVec 32) (resource : RtId) (instanceState : InstState)
    (identity : HandleObjId) (handle : ResourceHandle)
    (instanceGet : store.inst? cx.inst = some instanceState)
    (entryGet : instanceState.handles.get? slot.toNat = some (.resource identity))
    (objectGet : store.resHandle? identity = some handle) :
    Stored.Endpoints.Core.runLocal (Resources.take limits cx resource slot.toNat) store =
      (ArenaField.insts.modify store cx.inst (InstState.removeHandle slot.toNat),
        if handle.rt != resource then .error (.trapped .resourceTypeMismatch)
        else if handle.numLends != 0 then .error (.trapped .ownLent)
        else if !handle.own then .error (.trapped .notOwnHandle)
        else .ok ⟨identity, handle.rep⟩) := by
  have instanceGet' : ArenaField.insts.get? store cx.inst = some instanceState := instanceGet
  have objectGet' : ArenaField.resHandles.get?
      (ArenaField.insts.modify store cx.inst (InstState.removeHandle slot.toNat)) identity =
        some handle := objectGet
  simp only [Resources.take, Resources.takeWith, handlesRemove, getInst, getObj, bind_assoc, run_get,
    instanceGet', pure_bind, InstState.removeHandle?, Table.remove?, entryGet, Option.map_some,
    modifyInst, modifyObj, run_modify, expectResource, getResHandle, ArenaOps.updateSt, objectGet']
  unfold trapIf
  split <;> simp_all only [run_trap, pure_bind]
  split <;> simp_all only [run_trap, pure_bind]
  split <;> simp_all only [run_trap, Prog.pure_eq]
  rfl

private theorem atSlot_remove (store : CStore E) (inst : InstId) (slot query : BitVec 32)
    (instanceState : InstState) (entry : HandleEntry)
    (instanceGet : store.inst? inst = some instanceState)
    (entryGet : instanceState.handles.get? slot.toNat = some entry) :
    atSlot (ArenaField.insts.modify store inst (InstState.removeHandle slot.toNat)) inst query =
      if query = slot then none else atSlot store inst query := by
  have modified : (ArenaField.insts.modify store inst (InstState.removeHandle slot.toNat)).inst? inst =
      some (instanceState.removeHandle slot.toNat) := by
    change (Arena.modify store.insts inst.idx (InstState.removeHandle slot.toNat)).get? inst.idx = _
    rw [Arena.get?_modify_self]
    exact congrArg (Option.map (InstState.removeHandle slot.toNat)) instanceGet
  have resSame (identity : HandleObjId) :
      (ArenaField.insts.modify store inst (InstState.removeHandle slot.toNat)).resHandle? identity =
        store.resHandle? identity := rfl
  have handles : (instanceState.removeHandle slot.toNat).handles.get? query.toNat =
      if query = slot then none else instanceState.handles.get? query.toNat := by
    simp only [InstState.removeHandle, InstState.removeHandle?, Table.remove?, entryGet,
      Option.map_some, Option.getD_some]
    by_cases same : query = slot
    · subst query
      have within : slot.toNat < instanceState.handles.array.size := by
        by_contra! outside
        simp [Table.get?, Array.getElem?_eq_none outside] at entryGet
      simp [Table.get?, Array.getElem?_setIfInBounds_self_of_lt within]
    · have distinct : slot.toNat ≠ query.toNat := fun eq => same (BitVec.eq_of_toNat_eq eq.symm)
      simp [Table.get?, same, Array.getElem?_setIfInBounds_ne distinct]
  simp only [atSlot, modified, instanceGet, Option.bind_some, handles, resSame]
  by_cases same : query = slot <;> simp [same]

theorem kill_matches (table : RT) (store : CStore E) (inst : InstId) (slot : BitVec 32)
    (instanceState : InstState) (entry : HandleEntry) (matched : Matches table store inst)
    (instanceGet : store.inst? inst = some instanceState)
    (entryGet : instanceState.handles.get? slot.toNat = some entry) :
    Matches (table.killAll [slot])
      (ArenaField.insts.modify store inst (InstState.removeHandle slot.toNat)) inst := by
  intro resource query
  by_cases same : query = slot
  · subst query
    cases observed : table slot <;> simp [RT.lookup, RT.killAll, observed, ResEntry.kill,
      snapshot, atSlot_remove store inst slot slot instanceState entry instanceGet entryGet]
  · simpa [RT.lookup, RT.killAll, snapshot, same,
      atSlot_remove store inst slot query instanceState entry instanceGet entryGet] using matched resource query

private theorem checkedLookup_rep (table : RT) (resource : Nat) (slot : BitVec 32) (rep : Nat)
    (checked : lookupChecked table resource slot = .ok rep) : table.lookup resource slot = some rep := by
  cases found : table slot with
  | none => simp [lookupChecked, found] at checked
  | some entry =>
    by_cases live : entry.live = true
    · by_cases right : entry.ty = resource
      · simpa [lookupChecked, RT.lookup, found, live, right] using checked
      · simp [lookupChecked, found, live, right] at checked
    · have dead : entry.live = false := Bool.eq_false_of_not_eq_true live
      simp [lookupChecked, found, dead] at checked

theorem reserve_rep (table : RT) (resource : Nat) (slot : BitVec 32)
    (before after : Nested.Reservations) (rep : Nat)
    (reserved : (Nested.reserve table resource slot).run before = .ok (rep, after)) :
    table.lookup resource slot = some rep := by
  simp only [Nested.reserve, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get,
    set, pure, Except.pure, StateT.get, Except.bind] at reserved
  split at reserved
  · cases checked : lookupChecked table resource slot with
    | error issue => rw [checked] at reserved; cases reserved
    | ok value =>
      rw [checked] at reserved
      cases reserved
      exact checkedLookup_rep table resource slot rep checked
  · cases reserved

theorem lookup_refines_take (limits : Component.Limits) (cx : LiftLowerContext E) (store : CStore E)
    (table : RT) (resource : RtId) (slot : BitVec 32) (rep : Nat)
    (matched : Matches table store cx.inst)
    (found : table.lookup resource.idx slot = some rep) :
    ∃ owner : Resources.Owned resource,
      ownerAt store cx.inst resource slot = some owner ∧ owner.representation = rep ∧
      let updated := ArenaField.insts.modify store cx.inst (InstState.removeHandle slot.toNat)
      Stored.Endpoints.Core.runLocal (Resources.take limits cx resource slot.toNat) store = (updated, .ok owner) ∧
      Matches (table.killAll [slot]) updated cx.inst := by
  have projected := (lookup_ownerAt store cx.inst resource slot).symm.trans
    ((matched resource.idx slot).symm.trans found)
  cases instanceGet : store.inst? cx.inst with
  | none => simp [ownerAt, atSlot, instanceGet] at projected
  | some state =>
    cases entryGet : state.handles.get? slot.toNat with
    | none => simp [ownerAt, atSlot, instanceGet, entryGet] at projected
    | some entry =>
      cases entry <;> simp [atSlot, instanceGet, entryGet, ownerAt] at projected
      rename_i identity
      cases objectGet : store.resHandle? identity with
      | none => simp [objectGet] at projected
      | some handle =>
        simp [objectGet, guard] at projected
        split at projected
        · rename_i allowed
          have checks : handle.rt = resource ∧ handle.own = true ∧ handle.numLends = 0 := by
            simpa [and_assoc] using allowed
          have owner : ownerAt store cx.inst resource slot = some ⟨identity, handle.rep⟩ := by
            simp [ownerAt, atSlot, instanceGet, entryGet, objectGet, checks.1, checks.2.1, checks.2.2]
          refine ⟨_, owner, by simpa using projected, ?_, kill_matches table store cx.inst slot state _
            matched instanceGet entryGet⟩
          rw [take_removes_first limits cx store slot resource state identity handle instanceGet entryGet objectGet]
          simp [checks.1, checks.2.1, checks.2.2]
        · simp at projected

theorem reserve_refines_take (limits : Component.Limits) (cx : LiftLowerContext E) (store : CStore E)
    (table : RT) (resource : RtId) (slot : BitVec 32) (before after : Nested.Reservations) (rep : Nat)
    (matched : Matches table store cx.inst)
    (reserved : (Nested.reserve table resource.idx slot).run before = .ok (rep, after)) :
    ∃ owner : Resources.Owned resource,
      ownerAt store cx.inst resource slot = some owner ∧ owner.representation = rep ∧
      let updated := ArenaField.insts.modify store cx.inst (InstState.removeHandle slot.toNat)
      Stored.Endpoints.Core.runLocal (Resources.take limits cx resource slot.toNat) store = (updated, .ok owner) ∧
      Matches (table.killAll [slot]) updated cx.inst :=
  lookup_refines_take limits cx store table resource slot rep matched
    (reserve_rep table resource.idx slot before after rep reserved)

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnReferenceTable
