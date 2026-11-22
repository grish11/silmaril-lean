module

public import Silmaril.Semantics.Arena.Mutable.Defs
import Silmaril.Proofs.Semantics.Arena.Mutable

public section

namespace Silmaril.Semantics.Arena.Mutable

variable {Rep Key Name Obj Error Result : Type} {limit : Nat}

theorem Mutation.commit_error {edit : Mutation Rep Error Result} {state : Rep} {fault : Error}
    (failed : edit state = .error fault) : edit.commit state = (.error fault, state) := by
  simp [commit, failed]

/-- Exact local guard and slot policy, before committing a plain edit. -/
theorem Change.run_raw [DecidableEq Key] (arena : State Key Name Obj) (key : Key) (change : Change Obj) :
    change.run State.step key arena = (change.apply (arena key)).map (arena.replaceAt key) :=
  Proofs.Semantics.Arena.Mutable.run_raw arena key change

theorem Access.raw_spec [DecidableEq Key] {arena updated : State Key Name Obj} {key : Key} {change : Change Obj}
    (success : Access.raw.change key change arena = .ok ((), updated)) :
    change.apply (arena key) = .ok (updated key) ∧ ∀ query, key ≠ query → updated query = arena query :=
  Proofs.Semantics.Arena.Mutable.raw_spec success

@[simp] theorem Access.array_read (arena : Dense limit Name Obj) (key : Nat) :
    (Access.array limit).read arena key = Access.raw.read arena.toBounded.val key := rfl

/-- On in-bounds keys both backends return the same error or observed
successor, including the intermediate reservation in an insertion. -/
theorem Access.array_change_simulates (arena : Dense limit Name Obj) (key : Nat) (change : Change Obj)
    (inside : key < limit) :
    ((Access.array limit).change key change arena).map (fun (_, updated) => ((), updated.toBounded.val)) =
      Access.raw.change key change arena.toBounded.val :=
  Proofs.Semantics.Arena.Mutable.array_change_simulates arena key change inside

theorem Access.array_change_outside (arena : Dense limit Name Obj) (key : Nat) (change : Change Obj)
    (outside : limit ≤ key) : (Access.array limit).change key change arena = .error .outOfBounds :=
  Proofs.Semantics.Arena.Mutable.array_change_outside arena key change outside

theorem Growing.allocate_spec (arena : Growing Name Obj) (payload : Option Obj) :
    ∃ updated, Growing.allocate payload arena = .ok (arena.1, updated) ∧ updated.1 = arena.1 + 1 ∧
      arena.read arena.1 = none ∧ updated.read arena.1 = some payload ∧
      ∀ key, key < arena.1 → updated.read key = arena.read key :=
  Proofs.Semantics.Arena.Mutable.allocate_spec arena payload

end Silmaril.Semantics.Arena.Mutable
