module

import Silmaril.Languages.Starlark.Lists.Thms
meta import Silmaril.Languages.Starlark.Lists.Denotation.Defs

namespace Silmaril.Languages.Starlark.Lists.Comparison

deriving instance DecidableEq for Except

private def int (n : Int) : Value := .scalar (.int n)

private def result {α : Type} : Outcome α → Except Error α
  | .ok value _ => .ok value
  | .error error _ => .error error

private def item (key : String) (value : Value) : Entry := ⟨.string key, [.string key], value⟩

-- Distinct insertion positions and numeric key spellings match through the
-- table lookup. The reached values nest dictionaries, tuples and lists.
#guard
  let action : Meaning (List (Except Error Bool)) := do
    let smallLeft ← allocateDict [item "n" (int 0)]
    let smallRight ← allocateDict [item "n" (.scalar (.float 0x8000000000000000))]
    let xs ← allocate [smallLeft, int 3]
    let ys ← allocate [smallRight, .scalar (.float 0x4008000000000000)]
    let tx ← allocateTuple [xs]
    let ty ← allocateTuple [ys]
    let lhs ← allocateDict []
    let rhs ← allocateDict []
    let key := int 9007199254740992
    let floatKey : Value := .scalar (.float 0x4340000000000000)
    let flag : Value := .scalar (.bool false)
    writeIndex lhs key tx
    writeIndex lhs flag (int 1)
    writeIndex rhs flag (int 1)
    writeIndex rhs floatKey ty
    let before ← fun state => .ok (evaluate state.heap .eq lhs rhs) state
    writeIndex lhs floatKey (int 7)
    fun state => .ok [before, evaluate state.heap .eq lhs rhs, evaluate state.heap .ne lhs rhs] state
  result (action {}) = .ok [.ok true, .ok false, .ok true]

-- Membership reads keys only. In particular, the Boolean tag remains
-- distinct from zero and a cyclic value never consumes comparison depth.
#guard
  let action : Meaning (List (Except Error Bool)) := do
    let table ← allocateDict []
    let flag : Value := .scalar (.bool false)
    writeIndex table flag table
    let distinct ← fun state => .ok (evaluate state.heap .mem (int 0) table) state
    writeIndex table (int 0) table
    writeIndex table (int 9007199254740992) table
    let first ← allocateTuple [int 0, .scalar (.float 0x7ff8000000000021)]
    let same ← allocateTuple [.scalar (.float 0x8000000000000000), .scalar (.float 0xfff0000000000001)]
    writeIndex table first table
    let bad ← allocate [int 0]
    let badTuple ← allocateTuple [bad]
    let empty ← allocateDict []
    fun state => .ok [distinct, evaluate state.heap .mem flag table,
      evaluate state.heap .mem (.scalar (.float 0x8000000000000000)) table,
      evaluate state.heap .mem (.scalar (.float 0x4340000000000000)) table,
      evaluate state.heap .notMem (int 9007199254740993) table,
      evaluate state.heap .mem same table, evaluate state.heap .notMem same table,
      evaluate state.heap .mem bad empty, evaluate state.heap .notMem badTuple table,
      evaluate state.heap .mem table table] state
  result (action {}) = .ok [.ok false, .ok true, .ok true, .ok true, .ok true, .ok true, .ok false,
    .error (.unhashableKey (.list 3)), .error (.unhashableKey (.tuple 4)), .error (.unhashableKey (.dict 0))]

-- The receiver is read before key validation, and the raw lookup keeps
-- malformed reads, unhashability, and misses distinct.
#guard
  let heap : Heap := #[⟨.dict [], false⟩, ⟨.list [], true⟩]
  lookupDictionary heap 0 (.tuple 42) = .error (.danglingAddress 42) ∧
    lookupDictionary heap 0 (.tuple 1) = .error (.wrongCellKind 1) ∧
    lookupDictionary heap 0 (.list 1) = .error (.unhashableKey (.list 1)) ∧
    lookupDictionary heap 0 (int 1) = .ok none ∧
    evaluate heap .notMem (.list 1) (.dict 1) = .error (.wrongCellKind 1) ∧
    evaluate heap .mem (.tuple 42) (.dict 41) = .error (.danglingAddress 41)

-- Size, a missing key and the first unequal value can each mask a cycle.
-- Reversing the operands changes which entry the scan reaches first.
#guard
  let state : State := { heap := #[
    ⟨.dict [item "self" (.dict 0)], false⟩,
    ⟨.dict [item "self" (.dict 1)], false⟩,
    ⟨.dict [item "guard" (int 0), item "cycle" (.dict 0)], false⟩,
    ⟨.dict [item "cycle" (.dict 1), item "guard" (int 1)], false⟩,
    ⟨.dict [item "missing" (int 0), item "cycle" (.dict 0)], false⟩,
    ⟨.dict [], false⟩,
    ⟨.list [], false⟩] }
  evaluate state.heap .eq (.dict 0) (.dict 5) = .ok false ∧
    evaluate state.heap .eq (.dict 0) (.dict 0) = .error .comparisonDepth ∧
    evaluate state.heap .eq (.dict 2) (.dict 3) = .ok false ∧
    evaluate state.heap .eq (.dict 3) (.dict 2) = .error .comparisonDepth ∧
    evaluate state.heap .eq (.dict 4) (.dict 3) = .ok false ∧
    evaluate state.heap .ne (.dict 3) (.dict 4) = .error .comparisonDepth ∧
    evaluate state.heap .eq (.dict 42) (.dict 6) = .error (.danglingAddress 42) ∧
    evaluate state.heap .eq (.dict 5) (.dict 6) = .error (.wrongCellKind 6) ∧
    evaluate state.heap .eq (.dict 5) (.list 6) = .ok false ∧
    evaluate state.heap .mem (int 1) (.dict 5) = .ok false

-- Values consume the same budget through dictionary entries. Cached keys
-- match independently of the remaining depth of the value comparison.
#guard
  let action : Meaning (List (Except Error Bool)) := do
    let wrap := fun count (value : Value) =>
      (List.range count).foldlM (fun field _ => allocateDict [item "n" field]) value
    let nine ← wrap 9 (int 0)
    let nineFloat ← wrap 9 (.scalar (.float 0x8000000000000000))
    let ten ← allocateDict [item "n" nine]
    let tenFloat ← allocateDict [item "n" nineFloat]
    let keyWrap := fun (leaf : Value) =>
      (List.range 10).foldlM (fun key _ => allocateTuple [key]) leaf
    let key ← keyWrap (int 0)
    let floatKey ← keyWrap (.scalar (.float 0x8000000000000000))
    let collisionKey ← keyWrap (int 4294967296)
    let lhs ← allocateDict []
    let rhs ← allocateDict []
    let collision ← allocateDict []
    writeIndex lhs key (int 1)
    writeIndex rhs floatKey (int 1)
    let cached ← fun state => .ok (evaluate state.heap .eq lhs rhs) state
    writeIndex lhs key lhs
    writeIndex rhs floatKey rhs
    writeIndex collision collisionKey collision
    let .dict rhsAddress := rhs | throw .assignmentTarget
    let .dict collisionAddress := collision | throw .assignmentTarget
    fun state => fromExcept (do
      let candidates ← dictionaryEntries state.heap rhsAddress
      let colliding ← dictionaryEntries state.heap collisionAddress
      let bounded := probeKeys state.heap defaultDepth key candidates
      let boundedCollision := probeKeys state.heap defaultDepth key colliding
      pure [evaluate state.heap .eq nine nineFloat, evaluate state.heap .eq ten tenFloat,
        cached, evaluate state.heap .eq lhs rhs, equalAt state.heap 1 (.dict 0) (.dict 0),
        evaluate state.heap .mem key rhs, Option.isSome <$> bounded, .ok (lookupOrMiss bounded).isSome,
        evaluate state.heap .mem key collision, Option.isSome <$> boundedCollision]) state
  result (action {}) = .ok [.ok true, .error .comparisonDepth, .ok true,
    .error .comparisonDepth, .error .comparisonDepth,
    .ok true, .error .comparisonDepth, .ok false, .ok false, .error .comparisonDepth]

-- A supplied candidate order controls whether the successful comparison or
-- malformed address is reached first, independently of the cached codes.
#guard
  let heap : Heap := #[⟨.tuple [int 1] none, false⟩, ⟨.tuple [int 2] none, false⟩]
  let hit : Entry := ⟨.tuple 0, [], int 10⟩
  let miss : Entry := ⟨.tuple 1, [], int 20⟩
  let bad : Entry := ⟨.tuple 42, [], int 30⟩
  probeKeys heap defaultDepth (.tuple 0) [miss, hit, bad] = .ok (some hit) ∧
    probeKeys heap defaultDepth (.tuple 0) [miss, bad, hit] = .error (.danglingAddress 42)

private def actual : Binding := ⟨.global, "actual"⟩
private def expected : Binding := ⟨.global, "expected"⟩
private def events : Binding := ⟨.global, "events"⟩

private def initial : State :=
  { heap := #[⟨.list [int 1], false⟩, ⟨.list [int 1, int 2], false⟩,
      ⟨.dict [item "events" (.list 0)], false⟩, ⟨.dict [item "events" (.list 1)], false⟩]
    bindings := fun name => if name = actual then some (.dict 2)
      else if name = expected then some (.dict 3)
      else if name = events then some (.list 0) else none }

-- The right operand mutates a value reachable from the already evaluated
-- left dictionary. The comparison reads both dictionaries in the reached heap.
example :
    let mark : Expr := .append (.read (.bound events)) (.scalar (.int 2))
    let right : Expr := .index (.tuple (.cons mark (.cons (.read (.bound expected)) .empty)))
      (.scalar (.int 1))
    denote (.compare .eq (.read (.bound actual)) right) initial =
      .ok (.scalar (.bool true)) { initial with heap := #[
        ⟨.list [int 1, int 2], false⟩, ⟨.list [int 1, int 2], false⟩,
        ⟨.dict [item "events" (.list 0)], false⟩, ⟨.dict [item "events" (.list 1)], false⟩,
        ⟨.tuple [.scalar .none, .dict 3] none, false⟩] } := rfl

private def mutateThenRead (mark : Int) (binding : Binding) : Expr :=
  .index (.tuple (.cons (.append (.read (.bound events)) (.scalar (.int mark)))
    (.cons (.read (.bound binding)) .empty))) (.scalar (.int 1))

-- The two operand effects precede the key error. A failure in the right
-- operand takes priority over an error from validating the left value.
example : denote (.compare .notMem (mutateThenRead 2 events) (mutateThenRead 3 actual)) initial =
    .error (.unhashableKey (.list 0)) { initial with heap := #[
      ⟨.list [int 1, int 2, int 3], false⟩, ⟨.list [int 1, int 2], false⟩,
      ⟨.dict [item "events" (.list 0)], false⟩, ⟨.dict [item "events" (.list 1)], false⟩,
      ⟨.tuple [.scalar .none, .list 0] none, false⟩,
      ⟨.tuple [.scalar .none, .dict 2] none, false⟩] } := rfl

example :
    let missing : Binding := ⟨.global, "missing"⟩
    denote (.compare .mem (mutateThenRead 2 events) (.read (.bound missing))) initial =
      .error (.uninitialized missing) { initial with heap := #[
        ⟨.list [int 1, int 2], false⟩, ⟨.list [int 1, int 2], false⟩,
        ⟨.dict [item "events" (.list 0)], false⟩, ⟨.dict [item "events" (.list 1)], false⟩,
        ⟨.tuple [.scalar .none, .list 0] none, false⟩] } := rfl

end Silmaril.Languages.Starlark.Lists.Comparison
