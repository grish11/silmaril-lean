module

public import Silmaril.Semantics.Streams.Defs
public import Silmaril.Semantics.Acceptors.Defs

/-!
# Token streams: streaming transducers between alphabets

Streaming formats are usually specified in two layers: a byte (or character) stream is
cut into tokens or events, and a language over the *token alphabet* says which token
sequences are valid. This module is the generic bridge between the two layers. It knows
nothing about any concrete format: concrete lexers, token types and grammars (JSON,
CBOR, JSONL, …) instantiate it.

* `Transducer ρ α τ`: a streaming transducer with state `ρ`. `step` reads one symbol and
  *commits* some tokens. `flush` gives the tokens still pending if the input ended now,
  without committing them (for example a number token that the next symbol could still
  extend).
* `Transducer.emitted w`: the tokens committed after input `w`. These grow monotonically
  with the input. `Transducer.tokenize w = emitted w ++ flush (state w)` is the
  tokenization of `w` as a *whole* input, and it is not monotone in general.
* `Transducer.pull T L`: the symbol language whose tokenization lies in the token language
  `L`. It is `Silmaril.Accept.pullSome` along the graph of `tokenize`.
* `Transducer.tokenChunks T cs`: the tokens committed by each chunk of an unbounded
  stream. `Transducer.Productive T cs` says that infinitely many chunks commit a token.
  A progressive input stream need not be productive: a transducer may buffer forever,
  for example inside an unterminated string.
* `Acceptor.lex T B`: a symbol acceptor that runs `T` and feeds committed tokens to a
  token acceptor `B`. Its `query` answers on a *copy* of the state extended by the flushed
  tokens, so querying commits nothing. An implementation whose `accepted()` commits the
  flushed tokens is not pure, and the `Acceptors` counterexamples (`finalizing`) apply.

## Scope

Each transducer step emits a finite list of tokens and the state is arbitrary. Nothing
here bounds memory or token sizes (see the stream-bounds topic). Nothing here claims
that a concrete lexer or component implements a given `Transducer`.
-/

@[expose] public section

namespace Silmaril.Streams

universe u v w x

/-- A streaming transducer from symbols `α` to tokens `τ`, with state `ρ`. -/
structure Transducer (ρ : Type u) (α : Type v) (τ : Type w) where
  /-- The state before any input. -/
  init : ρ
  /-- Read one symbol: the next state and the tokens it commits. -/
  step : ρ → α → ρ × List τ
  /-- The pending tokens if the input ended in this state (not committed). -/
  flush : ρ → List τ

namespace Transducer

variable {ρ : Type u} {α : Type v} {τ : Type w}

/-- Run from state `s` over a finite input: the final state and the committed tokens. -/
def run (T : Transducer ρ α τ) : ρ → List α → ρ × List τ
  | s, [] => (s, [])
  | s, a :: w =>
    let r := T.run (T.step s a).1 w
    (r.1, (T.step s a).2 ++ r.2)

/-- The state after input `w`. -/
def state (T : Transducer ρ α τ) (w : List α) : ρ := (T.run T.init w).1

/-- The tokens committed after input `w`. -/
def emitted (T : Transducer ρ α τ) (w : List α) : List τ := (T.run T.init w).2

/-- The tokenization of `w` as a whole input: committed tokens, then the flushed ones. -/
def tokenize (T : Transducer ρ α τ) (w : List α) : List τ := T.emitted w ++ T.flush (T.state w)

/-- The symbol words whose tokenization is in the token language `L`. -/
def pull (T : Transducer ρ α τ) (L : Language τ) : Language α := {w | T.tokenize w ∈ L}

/-- The tokens committed by each chunk of an unbounded chunk stream. -/
def tokenChunks (T : Transducer ρ α τ) (cs : Chunks α) : Chunks τ :=
  fun n => (T.run (T.state (cs.prefixAt n)) (cs n)).2

/-- Infinitely many chunks commit at least one token. -/
def Productive (T : Transducer ρ α τ) (cs : Chunks α) : Prop := (T.tokenChunks cs).Progressive

end Transducer

end Silmaril.Streams

namespace Silmaril.Acceptor

open Silmaril.Streams

universe u v w x

variable {ρ : Type u} {α : Type v} {τ : Type w} {σ : Type x}

/-- Run a transducer and feed its committed tokens to a token acceptor. A query answers
for the input with the pending tokens flushed, on a copy: it commits nothing. -/
def lex (T : Transducer ρ α τ) (B : Acceptor σ τ) : Acceptor (ρ × σ) α where
  init := (T.init, B.init)
  process p a := ((T.step p.1 a).1, (T.step p.1 a).2.foldl B.process p.2)
  query p := ((B.query ((T.flush p.1).foldl B.process p.2)).1, p)
  reset _ := (T.init, B.init)

end Silmaril.Acceptor
