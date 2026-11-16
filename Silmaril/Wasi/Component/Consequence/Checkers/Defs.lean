module

public import Silmaril.Wasi.Component.Consequence.Defs

/-! # Specification checker components

Components for protocol 1 (exported `check(ax, stmt) -> bool`), as **specification strategies**
(`Silmaril.Games.Strategy.generate`): Lean definitions of the plays, with no compiled component
binary and no core module behind them. Their theorems
(`Silmaril.Wasi.Component.Consequence.Checkers.Thms`) are about these strategies, read through
`exportCheck`; they say nothing about any compiled artifact.

* `answerChecker enc ans`: a call of `check` with the encoding `enc q` of a query may return
  `ans q`, and nothing else.
* `emptyChecker enc`: answers `false` to every encoded query. Its consequence relation is empty,
  and every query completes: its execution status is `SCT`, not `CAX`.
* `silentChecker`: never answers. Its relation is empty too, but no query completes: `CAX`, with
  `THM` holding vacuously.
* `memberChecker encL encC`: assumptions `list<T>`, statement `T`; answers whether the statement
  is one of the assumptions — the membership (assumption) rule over finite lists, and nothing
  else.
* `u32s?`, `u32Enc`, `u32Dec`: a concrete encoding, `list<u32>` assumptions and `u32` statements.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Consequence

open Silmaril.Games Silmaril.Wasi.Accept
open Silmaril.Wasm.Component (Val)

/-- The `check` function of the specification checkers. -/
def checkFn : FnName := ⟨"", "check"⟩

/-- **A specification one-shot checker**: a call of `check` with the encoding of a query `q`
may return `ans q`, and nothing else. -/
def answerChecker {Q : Type} (enc : Q → List Val) (ans : Q → Bool) :
    Strategy (nsig ∅) (nsig {checkFn}) :=
  Strategy.generate {s | ∃ q, s = [.inr (.ask (⟨checkFn, rfl⟩, enc q)),
    .inr (.ans (⟨checkFn, rfl⟩, enc q) (some [.bool (ans q)]))]}

/-- **The empty checker**: answers `false` to every encoded query. -/
def emptyChecker {Q : Type} (enc : Q → List Val) : Strategy (nsig ∅) (nsig {checkFn}) :=
  answerChecker enc fun _ => false

/-- **The silent checker**: never answers. -/
def silentChecker : Strategy (nsig ∅) (nsig {checkFn}) := Strategy.generate ∅

/-- **The membership checker**: is the statement one of the assumptions? -/
def memberChecker {C : Type} [DecidableEq C] (encL : List C → Val) (encC : C → Val) :
    Strategy (nsig ∅) (nsig {checkFn}) :=
  answerChecker (fun q : List C × C => [encL q.1, encC q.2]) fun q => decide (q.2 ∈ q.1)

/-! ## A concrete encoding: `list<u32>` and `u32` -/

/-- A `list<u32>` value: a record of `u32`s. -/
def u32s? (v : Val) : Option (List (BitVec 32)) := (ofRecord? v).bind (·.mapM ofU32?)

/-- The encoding of a query `(list<u32>, u32)`. -/
def u32Enc (q : List (BitVec 32) × BitVec 32) : List Val := [.record (q.1.map .u32), .u32 q.2]

/-- The decoding of `check(ax: list<u32>, stmt: u32)` arguments. -/
def u32Dec : List Val → Option (List (BitVec 32) × BitVec 32) := args2 u32s? ofU32?

end Silmaril.Wasi.Consequence

namespace Silmaril.Wasi.Consequence

open Silmaril.Games

/-- The membership checker at `list<u32>` assumptions and `u32` statements. -/
def memberU32 : Strategy (nsig ∅) (nsig {checkFn}) :=
  memberChecker (fun xs => .record (xs.map .u32)) .u32

/-- The empty checker at `list<u32>` assumptions and `u32` statements. -/
def emptyU32 : Strategy (nsig ∅) (nsig {checkFn}) := emptyChecker u32Enc

end Silmaril.Wasi.Consequence
