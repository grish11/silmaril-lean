module

public import Silmaril.Semantics.Acceptors.Defs
public import Silmaril.Semantics.StreamMonitors.Defs

/-!
# Incremental acceptors on unbounded chunk streams

This module connects the finite-trace specification of incremental acceptors
(`Silmaril.Semantics.Acceptors`) with chunk streams and their monitor verdicts
(`Silmaril.Semantics.Streams`, `Silmaril.Semantics.StreamMonitors`).

An unbounded session feeds an acceptor the chunks of `cs : ωSequence χ`, one by one, and
asks `accepted()` after each one. `Acceptor.boundaryAnswer A cs n` is the answer after
the first `n` chunks. `Acceptor.boundaryTrace cs n` is the finite client trace
`process c₀, query, …, process cₙ₋₁, query` of the first `n` rounds.
`Acceptor.view cs` is the stream of symbol chunks.

Infinite sessions have no separate semantics here: every statement is about all finite
prefixes of the session, which is all a client can observe. The theorems in
`Silmaril.Semantics.StreamAcceptors.Thms` show that a correct acceptor's answers are
the monitor's answers. Its safety, Büchi and co-Büchi verdicts are then those of
`StreamMonitors`, including that liveness verdicts need progress.
-/

@[expose] public section

namespace Silmaril.Acceptor

open Cslib Silmaril.Streams

universe u v w

variable {σ : Type u} {χ : Type v} {α : Type w}

/-- The answer of `accepted()` after processing the first `n` chunks from `init`. -/
def boundaryAnswer (A : Acceptor σ χ) (cs : ωSequence χ) (n : ℕ) : Bool :=
  (A.query ((cs.take n).foldl A.process A.init)).1

/-- The client trace of the first `n` rounds of `process c` followed by `query`. -/
def boundaryTrace (cs : ωSequence χ) (n : ℕ) : List (Event χ) :=
  (cs.take n).flatMap fun c => [.process c, .query]

/-- The stream of chunks, read as lists of symbols. -/
def view [ChunkView χ α] (cs : ωSequence χ) : Chunks α := cs.map ChunkView.toList

end Silmaril.Acceptor
