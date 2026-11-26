module

import Silmaril.Languages.Starlark.Lists.GoDictionary.Thms
meta import Silmaril.Languages.Starlark.Lists.GoDictionary.Defs
meta import Silmaril.Languages.Starlark.Lists.Comparison.Defs

namespace Silmaril.Languages.Starlark.Lists.GoDictionary

deriving instance DecidableEq for Except

private def int (value : Int) : Value := .scalar (.int value)
private def float (bits : UInt64) : Value := .scalar (.float bits)

-- Raw words from the pinned Go oracle. The bucket's zero reservation happens
-- only after hashing the entire key.
#guard
  let vectors : List (Starlark.Value × UInt32) := [
    (.none, 0), (.bool false, 0), (.bool true, 1), (.int (-3), 0),
    (.int (-2147483649), 0x83000014), (.int (-2147483648), 0x8240000f),
    (.int 2147483647, 0x8180000a), (.int 2147483648, 0x8240000f),
    (.int 0, 0x0240000f), (.int 4294967296, 0x0240000f),
    (.int (-(2 ^ 80 + 1)), 0x03000014),
    (.float 0x8000000000000000, 0x0240000f), (.float 0x3ff8000000000000, 0x03000014),
    (.float 0xc00e000000000000, 0), (.float 1, 0x0240000f),
    (.float 0x43e0000000000001, 0x0240280f), (.float 0xc3e0000000000001, 0x0240280f),
    (.float 0x7ff0000000000000, 0x0018b071), (.float 0xfff0000000000000, 0x0018b071),
    (.float 0x7ff8000000000021, 0x0018b071), (.float 0xfff0000000000001, 0x0018b071)]
  vectors.all (fun (key, want) => scalarHash key == want) &&
    storedHash 0 == 1 && storedHash 1 == 1

#guard
  let heap : Heap := #[
    ⟨.tuple [] none, false⟩,
    ⟨.tuple [int 4294967296, float 0x7ff8000000000021] none, false⟩,
    ⟨.tuple [.scalar (.bool false), int 3, float 0xc00e000000000000, .tuple 1] none, false⟩,
    ⟨.tuple [.tuple 3] none, false⟩]
  hashKey heap (.tuple 0) = .ok 0x00345678 ∧
    hashKey heap (.tuple 2) = .ok 0x8ebb258c ∧
    hashKey heap (.tuple 3) = .error .tupleGraph ∧
    hashKey heap (.tuple 42) = .error (.runtime (.danglingAddress 42))

-- None, both Booleans and -3 share a stored hash. Lookup still compares
-- their distinct keys and visits the occupied slots in order.
#guard
  let keys : List Value := [.scalar .none, .scalar (.bool false), .scalar (.bool true), int (-3)]
  let fixture : Except Error Bool := do
    let bucket ← keys.foldlM (fun table key => set #[] table key key) Bucket.empty
    pure (decide (bucket.keys = keys ∧ (bucket.candidates 1).map (fun item => item.1.key) = keys.reverse ∧
      get #[] bucket (.scalar (.bool false)) = .ok (some (.scalar (.bool false))) ∧
      contains #[] bucket (.string "excluded") = .error (.unsupportedKey (.string "excluded"))))
  fixture = .ok true

-- Eight positive integer collisions fill the bucket. Replacing zero through
-- a float alias retains its original key and position even at capacity.
#guard
  let inputs := (List.range 8).map fun index => (int (Int.ofNat index * 4294967296), int (Int.ofNat index))
  let fixture : Except Error Bool := do
    let full ← inputs.foldlM (fun table (key, value) => set #[] table key value) Bucket.empty
    let replaced ← set #[] full (float 0x8000000000000000) (int 99)
    let keyOrder := inputs.map Prod.fst
    pure (decide (replaced.keys = keyOrder ∧
      (replaced.candidates 0x0240000f).map (fun item => item.1.key) = keyOrder.reverse ∧
      get #[] replaced (int 0) = .ok (some (int 99)) ∧
      get #[] replaced (int 4294967296) = .ok (some (int 1)) ∧
      (set #[] replaced (int 1) (int 88)).map Bucket.keys = .error .capacity))
  fixture = .ok true

private def nested (leaf : Value) : Meaning Value :=
  (List.range 10).foldlM (fun item _ => allocateTuple [item]) leaf

private def cyclicFixture : Meaning (Value × Value × Value × Value) := do
  let zero ← nested (int 0)
  let alias ← nested (float 0x8000000000000000)
  let collision ← nested (int 4294967296)
  let cycle ← allocateDict []
  writeIndex cycle (int 0) cycle
  pure (zero, alias, collision, cycle)

-- The real bucket selects the deep colliding candidate. A reached lookup
-- error becomes a miss for both observations, leaving a cyclic value unread.
#guard
  match cyclicFixture {} with
  | .error .. => false
  | .ok (deep, alias, collision, cycle) state =>
    let heap := state.heap
    let fixture : Except Error Bool := do
      let colliding ← set heap Bucket.empty collision (int 1)
      let left ← set heap Bucket.empty deep cycle
      let right ← set heap Bucket.empty alias cycle
      let shallow ← set heap Bucket.empty (int 0) cycle
      let compare := fun depth a b => (Comparison.equalAt heap depth a b).mapError Error.runtime
      pure (decide (hashKey heap deep = .ok 0xa77087e7 ∧ hashKey heap collision = .ok 0xa77087e7 ∧
        get heap colliding deep = .error (.runtime .comparisonDepth) ∧
        (set heap colliding deep (int 5)).map Bucket.keys = .error (.runtime .comparisonDepth) ∧
        contains heap colliding deep = .ok false ∧
        equalWith heap compare Comparison.defaultDepth left right = .ok false ∧
        equalWith heap compare Comparison.defaultDepth shallow shallow = .error (.runtime .comparisonDepth)))
    decide (fixture = .ok true)

end Silmaril.Languages.Starlark.Lists.GoDictionary
