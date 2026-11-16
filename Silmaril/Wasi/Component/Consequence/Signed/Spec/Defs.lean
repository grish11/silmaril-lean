module

public import Silmaril.Wasi.Component.Consequence.Signed.Defs

/-! # Specification components for the signed protocols

Specification strategies (`Silmaril.Games.Strategy.generate`): Lean definitions of their plays,
with no compiled component and no core module behind them.

* `batchEmitter enc L`: on a call of its export `run`, it may emit the literals of any `l ∈ L` by
  calling its imports `pos(enc a)` / `neg(enc a)`, each answered `[]` by the host, then call
  `done()`. Its batches are exactly `L` (`Silmaril.Wasi.Component.Consequence.Signed.Spec.Thms`).
* `idChecker`: an exported `check(conj: list<variant { pos(u32), neg(u32) }>, disj: …) -> bool`
  answering whether the two lists share a formula (the identity axiom), and nothing else.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Consequence

open Silmaril.Games
open Silmaril.Consequence (Signed)
open Silmaril.Wasm.Component (Val)

/-- The import `pos`. -/
def posFn : FnName := ⟨"", "pos"⟩
/-- The import `neg`. -/
def negFn : FnName := ⟨"", "neg"⟩
/-- The import `done`. -/
def doneFn : FnName := ⟨"", "done"⟩
/-- The export `run`. -/
def runFn : FnName := ⟨"", "run"⟩

/-- The imports of the batch emitter. -/
abbrev batchImports : Set FnName := {posFn, negFn, doneFn}

/-- The batch protocol over `pos`, `neg`, `done`, with no reset. -/
def specBatchFns : BatchFns := { pos := posFn, neg := negFn, done := doneFn }

variable {V : Type}

/-- The moves emitting one literal: the call and the host's answer `[]`. -/
def litMoves (enc : V → Val) : Signed V → List (Move (nsig batchImports) (nsig {runFn}))
  | .pos a => [.inl (.ask (⟨posFn, by simp⟩, [enc a])),
      .inl (.ans (⟨posFn, by simp⟩, [enc a]) (some []))]
  | .neg a => [.inl (.ask (⟨negFn, by simp⟩, [enc a])),
      .inl (.ans (⟨negFn, by simp⟩, [enc a]) (some []))]

/-- The play emitting the batch `l`: `run` is called, the literals are emitted, `done` is called. -/
def emitPlay (enc : V → Val) (l : List (Signed V)) :
    List (Move (nsig batchImports) (nsig {runFn})) :=
  .inr (.ask (⟨runFn, rfl⟩, [])) :: l.flatMap (litMoves enc) ++
    [.inl (.ask (⟨doneFn, by simp⟩, []))]

/-- **The batch emitter**: emits any batch of `L`. -/
def batchEmitter (enc : V → Val) (L : Set (List (Signed V))) :
    Strategy (nsig batchImports) (nsig {runFn}) :=
  Strategy.generate {s | ∃ l ∈ L, s = emitPlay enc l}

/-- The encoding of a two-list query of signed `u32`s. -/
def signedPairEnc (q : List (Signed (BitVec 32)) × List (Signed (BitVec 32))) : List Val :=
  [.record (q.1.map signedU32), .record (q.2.map signedU32)]

/-- A list of signed `u32`s. -/
def signedList? (v : Val) : Option (List (Signed (BitVec 32))) :=
  (Accept.ofRecord? v).bind (·.mapM signedU32?)

/-- **The identity checker**: `check(Γ, Δ)` answers whether `Γ` and `Δ` share a formula. -/
def idChecker : Strategy (nsig ∅) (nsig {checkFn}) :=
  answerChecker signedPairEnc fun q => decide (∃ x ∈ q.1, x ∈ q.2)

end Silmaril.Wasi.Consequence
