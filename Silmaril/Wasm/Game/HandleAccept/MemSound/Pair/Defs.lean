module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Hi.Defs

/-!
# A module building the list `(a b)` through `sexp(ptr, len)`

`pairMod` imports `sexp.symbol : [i32 i32] → [i32]` (import `0`),
`sexp.sexp : [i32 i32] → [i32]` (import `1`) and `sexp.accept : [i32] → []` (import `2`), has one memory of one page, and
exports `run : [] → []` with two `i32` locals:

```wat
(func $run (local $a i32) (local $b i32)
  (i32.store8 (i32.const 16) (i32.const 0x61))                     ;; "a" at 16
  (local.set $a (call $symbol (i32.const 16) (i32.const 1)))
  (i32.store8 (i32.const 16) (i32.const 0x62))                     ;; "b" at 16
  (local.set $b (call $symbol (i32.const 16) (i32.const 1)))
  (i32.store (i32.const 0) (local.get $a))                         ;; list<i32> at 0:
  (i32.store (i32.const 4) (local.get $b))                         ;;   [$a, $b]
  (call $accept (call $sexp (i32.const 0) (i32.const 2))))
```

The two handles are stored after both `symbol` calls have returned, right before `sexp(0, 2)`:
the admitted hosts may rewrite memory at every call (`pairReply`: they keep the code and the
number of memories, return one `i32` from `symbol` and `sexp` and nothing from `accept`).

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.Pair

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Formats
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound.Hi

/-- The body of `run`. -/
def pairBody : List Instr :=
  [.intConst .i32 16, .intConst .i32 0x61, .intStore .i32 (some .i8) ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 16, .intConst .i32 1, .call ⟨0⟩, .localSet ⟨0⟩,
   .intConst .i32 16, .intConst .i32 0x62, .intStore .i32 (some .i8) ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 16, .intConst .i32 1, .call ⟨0⟩, .localSet ⟨1⟩,
   .intConst .i32 0, .localGet ⟨0⟩, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 4, .localGet ⟨1⟩, .intStore .i32 none ⟨0⟩ ⟨0, 0⟩,
   .intConst .i32 0, .intConst .i32 2, .call ⟨1⟩, .call ⟨2⟩]

/-- **The module.** -/
def pairMod : Module where
  types := [tySym, tyAcc, tyRun]
  imports := [⟨"sexp", "symbol", .func ⟨0⟩⟩, ⟨"sexp", "sexp", .func ⟨0⟩⟩,
    ⟨"sexp", "accept", .func ⟨1⟩⟩]
  memories := [⟨.i32, ⟨1, none⟩⟩]
  funcs := [⟨⟨2⟩, [.i32, .i32], pairBody⟩]
  exports := [⟨"run", .func ⟨3⟩⟩]

/-- The shape of the values returned by host code `k`: one `i32` from `symbol` and `sexp`,
nothing from `accept`. -/
def pairShape (k : Nat) (vs : List Val) : Prop :=
  (k = 0 ∨ k = 1 → ∃ c, vs = [.i32 c]) ∧ (k = 2 → vs = [])

/-- The admitted host replies. -/
def pairReply : UCall Nat → UReply → Prop := ShapedReply pairShape

/-- The symbol `a`. -/
def symA : MemAtom := ⟨.symbol, by decide, "a"⟩

/-- The symbol `b`. -/
def symB : MemAtom := ⟨.symbol, by decide, "b"⟩

/-- The list `(a b)`. -/
def pairTree : SymStrBytesSExp := SExp.ofList [.atom symA, .atom symB]

end Silmaril.Wasm.Game.HandleAccept.MemSound.Pair
