module

public import Silmaril.Games.Abstract.StratThread.Defs

/-!
# The own divergences and productive streams of a Core 3.0 core module: definitions

`stream p₀ a ω`: the plays of a round's productive stream after the play `p₀`, the question `a`
and then the import calls `ω 0, ω 1, …`; its limit is the infinite play of the stream.
`prependStream l c`: the stream `c` after the list `l`. The
theorems are in `Silmaril.Wasm.Abstract.NodeDiv.Thms`.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.NodeDiv

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs

/-- The plays of a round's productive stream after the play `p₀`: at stage `k`, the question
`a`, then the first `k` import calls of `ω`. -/
def stream {E F : Sig.{0}} (p₀ : List (Move E F)) (a : F.Op) (ω : ℕ → Call E) :
    Chain (Move E F) :=
  fun k => p₀ ++ .inr (.ask a) :: callMoves (streamTake ω k)

/-- The stream `c` after the list `l`: `l` first, then `c`. -/
def prependStream {α : Type} (l : List α) (c : ℕ → α) : ℕ → α :=
  fun k => if h : k < l.length then l[k] else c (k - l.length)

end Silmaril.Wasm.Abstract.NodeDiv
