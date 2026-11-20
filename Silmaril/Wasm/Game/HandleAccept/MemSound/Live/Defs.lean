module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Defs

/-!
# Non-vacuity of the memory-observing examples: concrete hosts

The soundness theorems of `Silmaril.Wasm.Game.HandleAccept.MemSound` (`hiMod_sound`,
`pairMod_sound`, `itemsMod_sound`) are upper bounds on languages. This topic exhibits concrete
traced sessions (`Silmaril.Wasm.Game.IOAccept.TSession`) in which the expected trees are
accepted, against hosts of the admitted classes `ReplyEnvs (ShapedReply shape)`.

* `countEnv out`: a **counting host**. Its state is an `i32` counter `q`; it answers every call
  of host code `k` in the caller's store (memory untouched) with the values `out k q`, and moves
  to `q + 1`. It never diverges. The counter is the next fresh handle: started at `base pol`
  (one past the policy's failure sentinel, if any), the handles it returns are not the sentinel.
* `itemsEnv h₁ h₂`: a host of the `items` reader: every call of host code `0` (`items(h, 0)` in
  `itemsMod`) writes, in the caller's memory `0`, the canonical-ABI `list<i32>` of the two
  handles `h₁ h₂` through the return pointer `0` (`itemsBytes`: the words `8, 2` at `[0, 8)`,
  then `h₁, h₂` at `[8, 16)`, little-endian) and returns nothing; other calls return nothing in
  the caller's store.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Live

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Accept.Handle Silmaril.Wasm.Game.HandleAccept.Memory

/-- **A counting host**: answers host code `k` in state `q` with `out k q` in the caller's store,
then moves to `q + 1`. -/
def countEnv (out : Nat → BitVec 32 → List Val) : SEnv UImp where
  S := BitVec 32
  Ans q e a q' := q' = q + 1 ∧ a = ⟨e.store, .values (out e.target q)⟩
  Div _ _ := False

/-- The first handle of a counting host for the policy `pol`: one past its sentinel. -/
def base (pol : Policy (BitVec 32)) : BitVec 32 := pol.sentinel.getD 0 + 1

/-- One handle from host code `0`, nothing otherwise (`hiMod`). -/
def hiOut : Nat → BitVec 32 → List Val
  | 0, q => [.i32 q]
  | _, _ => []

/-- One handle from host codes `0` and `1`, nothing otherwise (`pairMod`). -/
def pairOut : Nat → BitVec 32 → List Val
  | 0, q => [.i32 q]
  | 1, q => [.i32 q]
  | _, _ => []

/-- A little-endian `i32` store at byte `a`. -/
abbrev put32 (B : ByteArray) (a : Nat) (v : BitVec 32) : Option ByteArray :=
  Memory.store B a (count := IntType.i32.width / 8) (v.setWidth _)

/-- The `list<i32>` of `h₁ h₂` returned through the pointer `0`: `(8, 2)` at `[0, 8)`, the
handles at `[8, 16)`. -/
def itemsBytes (h₁ h₂ : BitVec 32) (B : ByteArray) : Option ByteArray :=
  (put32 B 0 8).bind fun B => (put32 B 4 2).bind fun B => (put32 B 8 h₁).bind fun B =>
    put32 B 12 h₂

/-- The store after the host wrote `itemsBytes` into memory `0` (unchanged if it cannot). -/
def itemsStore (h₁ h₂ : BitVec 32) (s : Store Nat) : Store Nat :=
  ((s.mems[0]?).bind fun mi =>
    (itemsBytes h₁ h₂ mi.bytes).map fun b => s.setMem 0 { mi with bytes := b }).getD s

/-- **A host of the `items` reader** returning the two handles `h₁ h₂`. -/
def itemsEnv (h₁ h₂ : BitVec 32) : SEnv UImp where
  S := Unit
  Ans _ e a _ := a = ⟨if e.target = 0 then itemsStore h₁ h₂ e.store else e.store, .values []⟩
  Div _ _ := False

end Silmaril.Wasm.Game.HandleAccept.MemSound.Live
