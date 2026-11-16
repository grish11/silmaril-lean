module

public import Silmaril.Games.Institution.Defs

/-!
# A non-Wasm system in the institution of game semantics: a counter cell

A counter cell offers two operations: `get` (answered by a natural number) and `inc`
(answered by `()`). It is the game `cellGame = (Sig.empty, cellSig)`: it serves `get` and
`inc` and calls nothing.

* `counter n`: the cell started at `n`, the strategy of a small transition system `lts n`.
  Its state is the pending question and the current value.
* Sentences:
  * `Exact n`: a `get` answers the number of `inc`s so far, counting from `n`;
  * `Mono`: successive `get` answers never decrease.
* `anyMono`: the loose specification, the join of all strategies satisfying `□ Mono`.
* A signature morphism `ι : getGame ⟶ cellGame` exposes only `get` (`getOnly`). The reduct of
  a counter along it is a constant oracle (`ConstAns n`).

The theorems are in `Silmaril.Games.Examples.Counter.Examples`. This module does not import Wasm.
-/

@[expose] public section

namespace Silmaril.Games.Examples.Counter

open Silmaril.Games

/-- The operations of the cell. -/
inductive CellOp : Type
  /-- Read the value. -/
  | get
  /-- Increment the value. -/
  | inc
  deriving DecidableEq

/-- Answers: `get` returns a number, `inc` returns `()`. -/
def cellAr : CellOp → Type
  | .get => ℕ
  | .inc => Unit

/-- The signature of the cell. -/
def cellSig : Sig.{0} := ⟨CellOp, cellAr⟩

/-- The game of the cell: serve `cellSig`, call nothing. -/
abbrev cellGame : Game.{0} := ⟨Sig.empty, cellSig⟩

/-- Moves of the cell game. -/
abbrev CMove : Type := Move Sig.empty cellSig

/-- The answer `k` to `get`. -/
def getA (k : ℕ) : CMove := .inr (.ans (m := CellOp.get) k)

/-- The answer to `inc`. -/
def incA : CMove := .inr (.ans (m := CellOp.inc) ())

/-- Transitions of the cell: accept a question, then answer it. -/
inductive CStep : Option CellOp × ℕ → Option CMove → Option CellOp × ℕ → Prop
  /-- Accept the question `q`. -/
  | ask (q : CellOp) (k : ℕ) : CStep (none, k) (some (.inr (.ask q))) (some q, k)
  /-- Answer `get` with the current value. -/
  | get (k : ℕ) : CStep (some .get, k) (some (getA k)) (none, k)
  /-- Answer `inc` and increment. -/
  | inc (k : ℕ) : CStep (some .inc, k) (some incA) (none, k + 1)

/-- The transition system of the cell started at `n`. -/
def lts (n : ℕ) : LTS Sig.empty cellSig := ⟨Option CellOp × ℕ, (none, n), CStep⟩

/-- **The counter started at `n`**. -/
def counter (n : ℕ) : Strategy Sig.empty cellSig := Strategy.ofLTS (lts n)

/-! ## Sentences -/

/-- The answer of a move, if it answers `get`. -/
def getVal? : CMove → Option ℕ
  | .inr (.ans .get v) => some v
  | _ => none

/-- The count after a move: one more after an answer to `inc`. -/
def bump : CMove → ℕ → ℕ
  | .inr (.ans .inc _), k => k + 1
  | _, k => k

/-- `exactFrom k s`: counting from `k`, every `get` in `s` answers the current count. -/
def exactFrom : ℕ → List CMove → Prop
  | _, [] => True
  | k, o :: s => (∀ v, getVal? o = some v → v = k) ∧ exactFrom (bump o k) s

/-- `monoFrom k s`: every `get` in `s` answers at least `k` and at least every earlier
answer. -/
def monoFrom : ℕ → List CMove → Prop
  | _, [] => True
  | k, o :: s => (∀ v, getVal? o = some v → k ≤ v) ∧ monoFrom ((getVal? o).getD k) s

/-- A `get` answers the number of `inc`s so far, counting from `n`. -/
def Exact (n : ℕ) : Set (List CMove) := {s | exactFrom n s}

/-- Successive `get` answers never decrease. -/
def Mono : Set (List CMove) := {s | monoFrom 0 s}

/-- **The loose specification**: the most permissive strategy satisfying `□ Mono`. -/
def anyMono : Strategy Sig.empty cellSig := sSup {σ | (GSen.box Mono).holds σ}

/-! ## Exposing `get` only -/

/-- A read-only oracle: one operation, answered by a number. -/
def getOnly : Sig.{0} := ⟨Unit, fun _ => ℕ⟩

/-- The game of the read-only oracle. -/
abbrev getGame : Game.{0} := ⟨Sig.empty, getOnly⟩

/-- The oracle's operation is `get`. -/
def upGet : Sig.Hom getOnly cellSig := ⟨fun _ => CellOp.get, fun _ n => n⟩

/-- The game morphism exposing only `get`. -/
def ι : getGame ⟶ cellGame := ⟨Sig.Hom.id Sig.empty, upGet⟩

/-- Every answer of the oracle is `n`. -/
def ConstAns (n : ℕ) : Set (List (Move Sig.empty getOnly)) :=
  {p | ∀ v : ℕ, (.inr (.ans (m := ()) v) : Move Sig.empty getOnly) ∈ p → v = n}

end Silmaril.Games.Examples.Counter
