module

import Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion.Thms
meta import Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion.Defs
meta import Silmaril.Languages.Starlark.Lists.Comparison.Defs

namespace Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion

deriving instance DecidableEq for Except

private def int (value : Int) : Value := .scalar (.int value)
private def collision (index : Nat) : Value := int (Int.ofNat index * 4294967296)
private def negativeZero : Value := .scalar (.float 0x8000000000000000)
private def hash : UInt32 := 0x0240000f

private def collisionOrder (table : Table) : List Value :=
  (table.candidates hash).map fun item => item.2.key

private def fill (initial : Table) (start count : Nat) : Except Error Table :=
  (List.range count).foldlM (fun table offset =>
    Deletion.set #[] table (collision (start + offset)) (int (Int.ofNat (start + offset)))) initial

-- Remove a primary cell and an overflow cell from two full blocks. A new
-- row takes the last overflow hole, then a float alias fills the primary
-- hole with a new key identity and appends to the iteration list.
#guard
  let fixture : Except Error Bool := do
    let full ← fill Table.empty 0 16
    let (removedZero, primaryHole) ← delete #[] full negativeZero
    let (removedOverflow, holes) ← delete #[] primaryHole (collision 12)
    let overflowFilled ← fill holes 16 1
    let reinserted ← Deletion.set #[] overflowFilled negativeZero (int 99)
    let home := holes.width.home hash
    pure (decide (removedZero = some (int 0) ∧ removedOverflow = some (int 12) ∧
      (holes.slots home).length = 16 ∧ holes.cells ⟨home, 7⟩ = none ∧ holes.cells ⟨home, 12⟩ = none ∧
      collisionOrder holes = [7, 6, 5, 4, 3, 2, 1, 8, 15, 14, 13, 11, 10, 9].map collision ∧
      (overflowFilled.cells ⟨home, 12⟩).map Row.key = some (collision 16) ∧
      (reinserted.cells ⟨home, 7⟩).map Row.key = some negativeZero ∧
      reinserted.keys = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16].map collision ++ [negativeZero] ∧
      Deletion.get #[] reinserted (int 0) = .ok (some (int 99))))
  fixture = .ok true

-- An empty overflow link is retained. The next two inserts scan the link
-- and fill slots fifteen and fourteen in that order.
#guard
  let fixture : Except Error Bool := do
    let nine ← fill Table.empty 0 9
    let (_, hole) ← delete #[] nine (collision 8)
    let twoMore ← fill hole 9 2
    let home := hole.width.home hash
    pure (decide (hole.extent home = 16 ∧ hole.cells ⟨home, 8⟩ = none ∧
      collisionOrder twoMore = [7, 6, 5, 4, 3, 2, 1, 0, 10, 9].map collision))
  fixture = .ok true

-- The other home grows the live count without filling the old holes.
-- Rehash starts with clean buckets and replays the surviving list.
#guard
  let fixture : Except Error Bool := do
    let full ← fill Table.empty 0 13
    let (_, primaryHole) ← delete #[] full (int 0)
    let (_, holes) ← delete #[] primaryHole (collision 12)
    let atThreshold ← [int 1, int 3].foldlM (fun table key => Deletion.set #[] table key key) holes
    let grown ← Deletion.set #[] atThreshold (int 5) (int 5)
    pure (decide (atThreshold.width = Growth.Width.two ∧ atThreshold.order.length = 13 ∧
      atThreshold.cells ⟨atThreshold.width.home hash, 7⟩ = none ∧
      grown.width = Growth.Width.two.double ∧
      collisionOrder grown = [8, 7, 6, 5, 4, 3, 2, 1, 9, 11, 10].map collision ∧
      grown.keys = (List.range 11).map (fun n => collision (n + 1)) ++ [int 1, int 3, int 5] ∧
      Deletion.get #[] grown (collision 12) = .ok none))
  fixture = .ok true

private def deep (leaf : Value) : Meaning Value :=
  (List.range 10).foldlM (fun item _ => allocateTuple [item]) leaf

private def depthFixture : Meaning (Value × Value × Value) := do
  let left ← deep (int 0)
  let collision ← deep (int 4294967296)
  let cycle ← allocateDict []
  writeIndex cycle (int 0) cycle
  pure (left, collision, cycle)

#guard
  match depthFixture {} with
  | .error .. => false
  | .ok (deep, collision, cycle) state =>
    let heap := state.heap
    let compare := fun depth a b => (Comparison.equalAt heap depth a b).mapError Error.runtime
    let fixture : Except Error Bool := do
      let start ← Deletion.set heap Table.empty collision cycle
      let withExtra ← Deletion.set heap start (int 1) (int 1)
      let (_, right) ← delete heap withExtra (int 1)
      let (miss, untouched) ← delete heap right (int 0)
      let left ← Deletion.set heap Table.empty deep cycle
      pure (decide (miss = none ∧ untouched.order = right.order ∧ untouched.keys = right.keys ∧
        (delete heap right (.list 42)).map Prod.fst = .error (.unsupportedKey (.list 42)) ∧
        (delete heap right deep).map Prod.fst = .error (.runtime .comparisonDepth) ∧
        Deletion.get heap right deep = .error (.runtime .comparisonDepth) ∧
        Deletion.equalWith heap compare Comparison.defaultDepth left right = .ok false))
    decide (fixture = .ok true)

end Silmaril.Languages.Starlark.Lists.GoDictionary.Deletion
