module

public import Mathlib.Computability.Language

/-!
# Incremental acceptors

An *incremental acceptor* is a state machine with the small API that streaming
parsers and validators usually expose to a host language:

* `process(chunk)` feeds the next chunk of input,
* `accepted() -> Bool` asks whether the input seen so far is in the language,
* `reset()` forgets the input and starts over.

This file specifies such acceptors against a language `L : Language α`
(a set of finite words, Mathlib's `Language α = Set (List α)`).

## Chunks

Input arrives in chunks of a type `χ`; `ChunkView χ α` says how a chunk reads
as a finite list of symbols. Chunks may be empty. Instances are given for
`List α`, `Array α` and `ByteArray` (symbols `UInt8`). There is no `String`
instance because `String.toList` is not computable in this toolchain.

## Acceptors and traces

`Acceptor σ χ` has an initial state and three operations. `query` returns the
answer *and* a new state, so the model also covers APIs whose `accepted()`
finalises, consumes or caches something. `Acceptor.Pure` says that `query`
does not change the state.

A client session is a trace `List (Event χ)` of `process c`, `query` and
`reset` events. `Acceptor.run` executes a trace and collects the answers of the
queries in order. The specification `specObs L tr` answers each query with
membership in `L` of the concatenation of all chunks since the last reset
(`pending` lists those chunks).

## Correctness notions

From strongest to weakest:

* `CorrectInterleaved A L`: on *every* trace, with arbitrary interleavings of
  `process`, `query` and `reset`, `A` gives the specified answers.
* `CorrectImmediate A L`: as above, but only on traces of the `Immediate`
  protocol, where each `process` is immediately followed by a single `query`,
  plus at most one query directly at the start or after a `reset`.
* `CorrectFold A L`: processing any list of chunks from the initial state and
  then querying once gives the right answer. This says nothing about `reset`,
  repeated queries or processing after a query.

`CorrectInterleaved` implies both others. For a `Pure` acceptor with a sound
reset (`ResetSound`: the state after `reset` is observationally equivalent to
the initial state) all three are equivalent (`Thms`). Without purity they are
not: `answerOnce` is `CorrectFold` and `CorrectImmediate` but not
`CorrectInterleaved`, and `finalizing` is `CorrectFold` but not
`CorrectImmediate`.

## Symbol-at-a-time acceptors

`Acceptor.ofSymbols` turns an acceptor for single symbols into a chunk acceptor
by folding over the symbols of each chunk; `Acceptor.toSymbols` restricts a
chunk acceptor to singleton chunks. `SymbolCorrect` is `CorrectFold` for
single-symbol input.

## Scope

This is a generic specification framework for finite inputs. It does not model
concurrency, failures or traps, resource limits, or the execution of any
concrete Wasm component. A concrete bridge (for example WIT `stream<u8>` or
`list<u8>` arguments of a Wasm component) is separate work and should
instantiate `Acceptor` and `ChunkView`. Infinite streams, safety and liveness
are a separate topic.
-/

@[expose] public section

namespace Silmaril

universe u v w

/-- How a chunk of type `χ` reads as a finite list of symbols of type `α`.
Chunks may be empty. -/
class ChunkView (χ : Type v) (α : outParam (Type w)) where
  /-- The symbols of a chunk, in order. -/
  toList : χ → List α

namespace ChunkView

variable {α : Type w}

instance instList : ChunkView (List α) α := ⟨id⟩

instance instArray : ChunkView (Array α) α := ⟨Array.toList⟩

instance instByteArray : ChunkView ByteArray UInt8 := ⟨fun b => b.data.toList⟩

end ChunkView

/-- An incremental acceptor with state `σ` reading chunks of type `χ`.

`query` returns the answer to "is the input so far accepted?" together with the
next state, so that it can model a finalising or caching `accepted()`. -/
structure Acceptor (σ : Type u) (χ : Type v) where
  /-- The state before any input. -/
  init : σ
  /-- Feed one chunk. -/
  process : σ → χ → σ
  /-- Answer whether the input so far is accepted, and the next state. -/
  query : σ → Bool × σ
  /-- Discard the input so far. -/
  reset : σ → σ

namespace Acceptor

/-- One client call. -/
inductive Event (χ : Type v) where
  | process (c : χ)
  | query
  | reset
  deriving DecidableEq, Repr

variable {σ : Type u} {χ : Type v} {α : Type w}

/-- Run a trace from state `s`: the answers to the queries, in order, and the final state. -/
def run (A : Acceptor σ χ) : σ → List (Event χ) → List Bool × σ
  | s, [] => ([], s)
  | s, .process c :: tr => A.run (A.process s c) tr
  | s, .query :: tr =>
      let r := A.run (A.query s).2 tr
      ((A.query s).1 :: r.1, r.2)
  | s, .reset :: tr => A.run (A.reset s) tr

/-- `query` leaves the state unchanged. -/
def Pure (A : Acceptor σ χ) : Prop :=
  ∀ s, (A.query s).2 = s

/-- Two states are observationally equivalent: every trace gives the same answers. -/
def ObsEq (A : Acceptor σ χ) (s t : σ) : Prop :=
  ∀ tr, (A.run s tr).1 = (A.run t tr).1

/-- After `reset`, from any state, the acceptor behaves like its initial state.
This holds in particular when `reset` returns `init` (`ResetSound.of_eq`). -/
def ResetSound (A : Acceptor σ χ) : Prop :=
  ∀ s, A.ObsEq (A.reset s) A.init

/-- The chunks processed since the last reset, starting from pending chunks `p`. -/
def pendingFrom : List χ → List (Event χ) → List χ
  | p, [] => p
  | p, .process c :: tr => pendingFrom (p ++ [c]) tr
  | p, .query :: tr => pendingFrom p tr
  | _, .reset :: tr => pendingFrom [] tr

/-- The chunks processed since the last reset of a trace. -/
def pending (tr : List (Event χ)) : List χ :=
  pendingFrom [] tr

/-- Restrict a chunk acceptor to single symbols, given a way `single` to make a
one-symbol chunk. -/
def toSymbols (A : Acceptor σ χ) (single : α → χ) : Acceptor σ α where
  init := A.init
  process s a := A.process s (single a)
  query := A.query
  reset := A.reset

/-- Membership of a word in `L`, as a `Bool`. A definition rather than a bare
`decide` so that rewriting the word does not have to transport the instance. -/
def member (L : Language α) [DecidablePred (· ∈ L)] (w : List α) : Bool :=
  decide (w ∈ L)

variable [ChunkView χ α]

/-- Specified answers of a trace when the input since the last reset is `w`. -/
def specFrom (L : Language α) [DecidablePred (· ∈ L)] :
    List α → List (Event χ) → List Bool
  | _, [] => []
  | w, .process c :: tr => specFrom L (w ++ ChunkView.toList c) tr
  | w, .query :: tr => member L w :: specFrom L w tr
  | _, .reset :: tr => specFrom L [] tr

/-- Specified answers of a trace: each query answers whether the concatenation of
the chunks since the last reset (`pending`) is in `L`. -/
def specObs (L : Language α) [DecidablePred (· ∈ L)] (tr : List (Event χ)) : List Bool :=
  specFrom L [] tr

/-- The symbol-level trace: each chunk becomes one `process [a]` per symbol `a`
(empty chunks disappear); queries and resets are kept. -/
def toSymbolTrace (tr : List (Event χ)) : List (Event (List α)) :=
  tr.flatMap fun
    | .process c => (ChunkView.toList c).map fun a => .process [a]
    | .query => [.query]
    | .reset => [.reset]

/-- Traces of the immediate-query protocol. `Immediate fresh tr`: `fresh` holds at
the start and right after a `reset`, where one query is allowed on its own;
otherwise every query directly follows a `process`, and every `process` is
directly followed by a query. -/
inductive Immediate : Bool → List (Event χ) → Prop
  | nil (b : Bool) : Immediate b []
  | step (b : Bool) (c : χ) {tr : List (Event χ)} :
      Immediate false tr → Immediate b (.process c :: .query :: tr)
  | query {tr : List (Event χ)} : Immediate false tr → Immediate true (.query :: tr)
  | reset (b : Bool) {tr : List (Event χ)} : Immediate true tr → Immediate b (.reset :: tr)

/-- Correct on every interleaving of `process`, `query` and `reset`. -/
def CorrectInterleaved (A : Acceptor σ χ) (L : Language α) [DecidablePred (· ∈ L)] : Prop :=
  ∀ tr : List (Event χ), (A.run A.init tr).1 = specObs L tr

/-- Correct on traces of the immediate-query protocol. -/
def CorrectImmediate (A : Acceptor σ χ) (L : Language α) [DecidablePred (· ∈ L)] : Prop :=
  ∀ tr : List (Event χ), Immediate true tr → (A.run A.init tr).1 = specObs L tr

/-- Processing any list of chunks from `init` and then querying once is correct. -/
def CorrectFold (A : Acceptor σ χ) (L : Language α) [DecidablePred (· ∈ L)] : Prop :=
  ∀ cs : List χ, (A.query (cs.foldl A.process A.init)).1 = member L (cs.flatMap ChunkView.toList)

/-- `CorrectFold` for an acceptor reading one symbol at a time. -/
def SymbolCorrect (B : Acceptor σ α) (L : Language α) [DecidablePred (· ∈ L)] : Prop :=
  ∀ w : List α, (B.query (w.foldl B.process B.init)).1 = member L w

/-- A chunk acceptor that feeds each chunk to `B` symbol by symbol. -/
def ofSymbols (B : Acceptor σ α) : Acceptor σ χ where
  init := B.init
  process s c := (ChunkView.toList c).foldl B.process s
  query := B.query
  reset := B.reset

/-- The reference acceptor: remember the input, answer by membership. Every language
with decidable membership has this (possibly infinite-state) correct acceptor. -/
def reference (L : Language α) [DecidablePred (· ∈ L)] : Acceptor (List α) χ where
  init := []
  process w c := w ++ ChunkView.toList c
  query w := (member L w, w)
  reset _ := []

/-- Counterexample: like `reference`, but a query answers only once; a second query
without intervening input answers `false`. -/
def answerOnce (L : Language α) [DecidablePred (· ∈ L)] : Acceptor (List α × Bool) χ where
  init := ([], false)
  process s c := (s.1 ++ ChunkView.toList c, false)
  query s := (!s.2 && member L s.1, (s.1, true))
  reset _ := ([], false)

/-- Counterexample: like `reference`, but a query finalises and discards the input. -/
def finalizing (L : Language α) [DecidablePred (· ∈ L)] : Acceptor (List α) χ where
  init := []
  process w c := w ++ ChunkView.toList c
  query w := (member L w, [])
  reset _ := []

end Acceptor

end Silmaril
