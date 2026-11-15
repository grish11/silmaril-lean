module

public import Silmaril.Semantics.Streams.Defs

/-!
# Monitoring chunk streams: safety and liveness verdicts

A monitor for a finite language `L : Language α` is asked, after each chunk, whether
the input delivered so far is in `L`. This is what an `accepted()` query after every
`process(chunk)` call observes. On an unbounded chunk stream the answers form an
infinite sequence of booleans, and three verdicts summarise it:

* `AlwaysAt L cs`: every answer is yes. This is the *safety* reading: a violation is
  witnessed by a finite prefix.
* `InfOftenAt L cs`: infinitely many answers are yes. This is the Büchi or *liveness*
  reading.
* `EventuallyAlwaysAt L cs`: all answers from some point on are yes. This is the
  co-Büchi reading; for a terminating stream it is the answer after the end of input.

These are compared with the corresponding properties of the infinite word the
stream delivers in the limit:

* `safetyω L`: every finite prefix is in `L`.
* CSLib's `L↗ω` (`Cslib.ωLanguage.omegaLim`): infinitely many prefixes are in `L`.

Two things make the comparison inexact, and the theorems in
`Silmaril.Semantics.StreamMonitors.Thms` state each with its hypotheses:

1. A monitor sees only prefixes at chunk boundaries. Coarse chunks can hide a
   violation inside a chunk.
2. A stream that is not `Progressive` delivers a finite word, so infinitely many yes
   answers on a stalled stream are about one finite word repeated, not about an
   infinite word. Liveness verdicts need the progress (chunk fairness) hypothesis.

## Scope

These are verdicts on data. Relating a concrete implementation's `accepted()`
answers to `cs.prefixAt n ∈ L` is the job of an acceptor correctness theorem
(see the incremental acceptor topic) or of a concrete bridge.
-/

@[expose] public section

namespace Silmaril.Streams

open Cslib

universe u

variable {α : Type u}

/-- The safety ω-language of `L`: infinite words all of whose finite prefixes are in `L`. -/
def safetyω (L : Language α) : ωLanguage α := ⟨{s | ∀ n, s.take n ∈ L}⟩

namespace Chunks

/-- Every chunk-boundary query answers yes. -/
def AlwaysAt (L : Language α) (cs : Chunks α) : Prop := ∀ n, cs.prefixAt n ∈ L

/-- Infinitely many chunk-boundary queries answer yes. -/
def InfOftenAt (L : Language α) (cs : Chunks α) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ cs.prefixAt n ∈ L

/-- From some chunk on, every chunk-boundary query answers yes. -/
def EventuallyAlwaysAt (L : Language α) (cs : Chunks α) : Prop :=
  ∃ N, ∀ n, N ≤ n → cs.prefixAt n ∈ L

end Chunks

end Silmaril.Streams
