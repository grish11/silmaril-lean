module

public import Silmaril.Semantics.Arena.Mutable.Defs
public import Silmaril.Semantics.Arena.Thms

public section

namespace Silmaril.Proofs.Semantics.Arena.Mutable

open Silmaril.Semantics.Arena
open Silmaril.Semantics.Arena.Mutable

variable {Rep Target Key Name Obj : Type} {limit : Nat}

theorem run_simulates (lower : Rep → Target) (sourceStep : Rep → Key → Edit Name Obj → Except Fault Rep)
    (targetStep : Target → Key → Edit Name Obj → Except Fault Target) (key : Key)
    (stepLaw : ∀ state edit, (sourceStep state key edit).map lower = targetStep (lower state) key edit)
    (state : Rep) (change : Change Obj) :
    (change.run sourceStep key state).map lower = change.run targetStep key (lower state) := by
  cases change with
  | reserve => exact stepLaw _ _
  | replace => exact stepLaw _ _
  | remove => exact stepLaw _ _
  | insert obj =>
      have reserved := stepLaw state (.reserve none)
      unfold Change.run
      rw [← reserved]
      cases sourceStep state key (.reserve none) with
      | error fault => rfl
      | ok successor => exact stepLaw successor (.replace ⟨none, some obj⟩)

theorem run_raw [DecidableEq Key] (arena : State Key Name Obj) (key : Key) (change : Change Obj) :
    change.run State.step key arena = (change.apply (arena key)).map (arena.replaceAt key) := by
  cases change with
  | reserve => rfl
  | replace => rfl
  | remove => rfl
  | insert obj =>
      cases occupied : arena key <;>
        simp [Change.run, Change.apply, State.step, Edit.apply, Except.map, Except.bind, occupied, State.replaceAt]
      funext query
      by_cases equal : key = query <;> simp [State.replaceAt, equal]

theorem raw_spec [DecidableEq Key] {arena updated : State Key Name Obj} {key : Key} {change : Change Obj}
    (success : Access.raw.change key change arena = .ok ((), updated)) :
    change.apply (arena key) = .ok (updated key) ∧ ∀ query, key ≠ query → updated query = arena query := by
  change (change.run State.step key arena).map ((), ·) = _ at success
  rw [run_raw] at success
  cases localResult : change.apply (arena key) with
  | error fault => simp [localResult, Except.map] at success
  | ok cell =>
      have updatedAt : arena.replaceAt key cell = updated := by simpa [localResult, Except.map] using success
      subst updated
      exact ⟨by simp [State.replaceAt], fun query different => by simp [State.replaceAt, different]⟩

theorem array_change_simulates (arena : Dense limit Name Obj) (key : Nat) (change : Change Obj)
    (inside : key < limit) :
    ((Access.array limit).change key change arena).map (fun (_, updated) => ((), updated.toBounded.val)) =
      Access.raw.change key change arena.toBounded.val := by
  have localStep (state : Dense limit Name Obj) (edit : Edit Name Obj) :
      (state.step key edit).map (fun updated => updated.toBounded.val) = state.toBounded.val.step key edit := by
    have bounded := state.step_commutes key edit
    have abstract := state.toBounded.step_abstract inside edit
    rw [← bounded] at abstract
    cases ran : state.step key edit <;> rw [ran] at abstract <;> exact abstract
  have simulation := run_simulates (fun repr : Dense limit Name Obj => repr.toBounded.val)
    Dense.step State.step key localStep arena change
  change ((change.run Dense.step key arena).map ((), ·)).map _ = (change.run State.step key arena.toBounded.val).map _
  rw [← simulation]
  cases change.run Dense.step key arena <;> rfl

theorem array_change_outside (arena : Dense limit Name Obj) (key : Nat) (change : Change Obj)
    (outside : limit ≤ key) : (Access.array limit).change key change arena = .error .outOfBounds := by
  cases change <;> simp [Access.array, Access.ofSlots, Change.run, Dense.step, Nat.not_lt.mpr outside, Except.map, Except.bind]

theorem allocate_spec (arena : Growing Name Obj) (payload : Option Obj) :
    ∃ updated, Growing.allocate payload arena = .ok (arena.1, updated) ∧ updated.1 = arena.1 + 1 ∧
      arena.read arena.1 = none ∧ updated.read arena.1 = some payload ∧
      ∀ key, key < arena.1 → updated.read key = arena.read key := by
  let slot : Slot Name Obj := ⟨none, payload⟩
  let updated : Growing Name Obj := ⟨arena.1 + 1, arena.2.append slot⟩
  have agrees := arena.2.append_commutes slot
  have fresh := arena.2.toBounded.append_fresh slot
  refine ⟨updated, rfl, rfl, ?_, ?_, ?_⟩
  · change (arena.2.toBounded.val arena.1).map Slot.payload = none
    rw [fresh.1]
    rfl
  · change ((arena.2.append slot).toBounded.val arena.1).map Slot.payload = _
    rw [agrees, fresh.2]
    rfl
  · intro key inside
    change ((arena.2.append slot).toBounded.val key).map Slot.payload = _
    rw [agrees, arena.2.toBounded.append_read_old slot inside]
    rfl

end Silmaril.Proofs.Semantics.Arena.Mutable
