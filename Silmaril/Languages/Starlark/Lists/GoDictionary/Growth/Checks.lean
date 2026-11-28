module

import Silmaril.Languages.Starlark.Lists.GoDictionary.Growth.Thms
meta import Silmaril.Languages.Starlark.Lists.GoDictionary.Growth.Defs
meta import Silmaril.Languages.Starlark.Lists.Comparison.Defs

namespace Silmaril.Languages.Starlark.Lists.GoDictionary.Growth

deriving instance DecidableEq for Except

private def int (value : Int) : Value := .scalar (.int value)
private def collision (index : Nat) : Value := int (Int.ofNat index * 4294967296)

private def addCollisions (table : Table) (start count : Nat) : Except Error Table :=
  (List.range count).foldlM (fun current n =>
    Growth.set #[] current (collision (start + n)) (int (Int.ofNat (start + n)))) table

-- Eight collisions fill the primary chain. The ninth starts overflow at slot
-- zero; later entries fill its suffix. Replacement leaves both layouts fixed.
#guard
  let fixture : Except Error Bool := do
    let full ← addCollisions Table.empty 0 8
    let replaced ← Growth.set #[] full (.scalar (.float 0x8000000000000000)) (int 99)
    let grown ← addCollisions replaced 8 1
    let filled ← addCollisions grown 9 4
    let overflowReplaced ← Growth.set #[] filled (collision 8) (int 88)
    let second ← addCollisions overflowReplaced 13 5
    let hash : UInt32 := 0x0240000f
    let slotIndices : List (Option Nat) := (grown.slots hash).map (fun slot => slot.map Prod.snd)
    let expectedKeys := (List.range 13).map collision
    pure (decide (full.width = .one ∧ replaced.width = .one ∧ grown.width = .two ∧
      slotIndices = [some 7, some 6, some 5, some 4, some 3, some 2, some 1, some 0, some 8]
        ++ (List.replicate 7 none : List (Option Nat)) ∧
      (overflowReplaced.candidates hash).map Prod.snd = [7, 6, 5, 4, 3, 2, 1, 0, 8, 12, 11, 10, 9] ∧
      overflowReplaced.keys = expectedKeys ∧ Growth.get #[] overflowReplaced (int 0) = .ok (some (int 99)) ∧
      Growth.get #[] overflowReplaced (collision 8) = .ok (some (int 88)) ∧
      second.width = Width.two.double ∧ (second.slots hash).length = 24 ∧
      (second.candidates hash).map Prod.snd = [7, 6, 5, 4, 3, 2, 1, 0, 8, 15, 14, 13, 12, 11, 10, 9, 16, 17] ∧
      second.keys = (List.range 18).map collision ∧
      Growth.get #[] second (int 0) = .ok (some (int 99)) ∧
      Growth.get #[] second (collision 8) = .ok (some (int 88)) ∧
      Growth.get #[] second (collision 16) = .ok (some (int 16))))
  fixture = .ok true

-- The first key has an even hash. Rehash moves it to the other bucket and the
-- ninth key fits in the primary chain of the odd bucket.
#guard
  let fixture : Except Error Bool := do
    let even ← Growth.set #[] Table.empty (int 1) (int 0)
    let full ← addCollisions even 1 7
    let replaced ← Growth.set #[] full (.scalar (.float 0x3ff0000000000000)) (int 99)
    let grown ← addCollisions replaced 8 1
    let oddHash : UInt32 := 0x0240000f
    let evenHash : UInt32 := 0x03000014
    let remaining := (List.range 8).map fun index => collision (index + 1)
    pure (decide (replaced.width = .one ∧ grown.width = .two ∧
      (grown.slots oddHash).length = 8 ∧ (grown.slots evenHash).length = 8 ∧
      (grown.candidates oddHash).map Prod.snd = [8, 7, 6, 5, 4, 3, 2, 1] ∧
      (grown.candidates evenHash).map Prod.snd = [0] ∧ grown.keys = int 1 :: remaining ∧
      Growth.get #[] grown (int 1) = .ok (some (int 99))) &&
      (List.range 8).all (fun n => decide (Growth.get #[] grown (collision (n+1)) = .ok (some (int (Int.ofNat (n+1)))))))
  fixture = .ok true

-- The first row shares a home through width two. Removing it from the
-- collision chain at width four promotes row eight into the primary bucket.
#guard
  let fixture : Except Error Bool := do
    let first ← Growth.set #[] Table.empty (int 2) (int 0)
    let full ← addCollisions first 1 12
    let replaced ← Growth.set #[] full (.scalar (.float 0x4000000000000000)) (int 99)
    let grown ← addCollisions replaced 13 1
    let hash : UInt32 := 0x0240000f
    pure (decide (replaced.width = .two ∧ grown.width = Width.two.double ∧
      (replaced.candidates hash).map Prod.snd = [7, 6, 5, 4, 3, 2, 1, 8, 12, 11, 10, 9] ∧
      (grown.candidates hash).map Prod.snd = [8, 7, 6, 5, 4, 3, 2, 1, 9, 13, 12, 11, 10] ∧
      grown.keys = int 2 :: (List.range 13).map (fun n => collision (n + 1)) ∧
      Growth.get #[] grown (int 2) = .ok (some (int 99))) &&
      (List.range 13).all (fun n => decide (Growth.get #[] grown (collision (n + 1)) =
        .ok (some (int (Int.ofNat (n + 1)))))))
  fixture = .ok true

private def deep (leaf : Value) : Meaning Value :=
  (List.range 10).foldlM (fun item _ => allocateTuple [item]) leaf

private def cycleFixture : Meaning (Value × Value × Value) := do
  let key ← deep (int 0)
  let same ← deep (.scalar (.float 0x8000000000000000))
  let cycle ← allocateDict []
  writeIndex cycle (int 0) cycle
  pure (key, same, cycle)

-- Confirm both the pre-growth abort and the lookup-error mask after growing.
#guard
  match cycleFixture {} with
  | .error .. => false
  | .ok (key, alias, cycle) state =>
    let heap := state.heap
    let fill := fun (table : Table) (size : Nat) =>
      (List.range size).foldlM (fun current n =>
        Growth.set heap current (int (Int.ofNat n)) cycle) table
    let compare := fun depth a b => (Comparison.equalAt heap depth a b).mapError Error.runtime
    let fixture : Except Error Bool := do
      let leftStart ← Growth.set heap Table.empty key cycle
      let rightStart ← Growth.set heap Table.empty alias cycle
      let rightFull ← fill rightStart 7
      let rightSecondFull ← fill rightStart 12
      let left ← fill leftStart 13
      let right ← fill rightStart 13
      let shallow ← fill Table.empty 14
      pure (decide (rightFull.width = .one ∧ rightSecondFull.width = .two ∧ right.width = Width.two.double ∧
        (Growth.set heap rightFull key cycle).map Table.keys = .error (.runtime .comparisonDepth) ∧
        (Growth.set heap rightSecondFull key cycle).map Table.keys = .error (.runtime .comparisonDepth) ∧
        Growth.get heap right key = .error (.runtime .comparisonDepth) ∧ Growth.contains heap right key = .ok false ∧
        Growth.equalWith heap compare Comparison.defaultDepth left right = .ok false ∧
        Growth.equalWith heap compare Comparison.defaultDepth shallow shallow = .error (.runtime .comparisonDepth)))
    decide (fixture = .ok true)

end Silmaril.Languages.Starlark.Lists.GoDictionary.Growth
