module

public import Silmaril.Semantics.Accept.Rel.Defs

/-!
# Relational acceptance of export-driven client sessions

A host drives a component instance through its exported entrypoints: `process(a)` (or
`input(a)`) feeds an input and returns nothing, `output() : Q` answers a query, and `reset()`
returns the instance to its initial state. This file says which input/answer pairs such a
session *relates*, with answers of an arbitrary type `Q` (so nondeterministic, `Option`,
`Except` or WIT `result` answers are all covered; the Bool-answer specialisation with
`Language` correctness is the separate incremental-acceptor development of draft PR #255).

## Trace model

* `Call A Q`: a top-level call that *returned*, with its observed answer: `feed a`,
  `query q` or `reset`.
* A session model is `T : Set (List (Call A Q))`: the call sequences a fresh instance can
  perform, each call returning. A call that traps or does not return is not recorded and nothing
  follows it: traps are modelled by *absence*, so every relation below is a
  successful-return relation. There is no concurrency (calls are sequential) and every
  session starts from a fresh instance.

## Segments

`segments T` are the reset-free suffixes `w` with `pre ++ w ∈ T`, where `pre = []` or `pre`
ends in `reset`: what a client observes between two resets. `freshSegments T` keeps only
`pre = []` (the reset-free traces of `T`).

## Relations (over a trace set; the segment versions apply them to `segments T`)

| fresh | over segments | relates |
| --- | --- | --- |
| `freshFeedQuery T` | `feedQuery T` | `a` to `q` when `[feed a, query q]` |
| `freshFeedsQuery T` | `feedsQuery T` | `as` to `q` when `as.map feed ++ [query q]` (strict) |
| `freshFeedsQueryAny T` | `feedsQueryAny T` | `as` to `q` when `w ++ [query q]`, `feeds w = as` |

Hypotheses on a model: `PrefixClosed T`, `QueryDrop T` (an answered query can be removed),
`QueryInsert T` (an answer available at a point can be inserted there), `QueryPure T` (both),
`ResetSound T` (after a reset the instance behaves as fresh).

## Chunked input

Feeding chunks `List α` (for bytes, `ByteChunk = List UInt8`): `flatRel R` relates the
*flattened* input to the answers of `R : List (List α) -|> Q`, and `FlatInvariant R` says the
answers depend only on the flattened input. `chunksQuery T := feedsQuery T`,
`flatQuery T := flatRel (chunksQuery T)` and `ChunkInvariant T := FlatInvariant (chunksQuery T)`.

## Deterministic models

`Machine S A Q` (initial state, step, answer) generates a session model `Machine.traces` in
which queries answer `answer s`, feeds step and resets return to the initial state; it is
prefix-closed, query-pure and reset-sound (`Thms`). `Machine.chunked` feeds a chunk element
by element and is chunk-invariant.
-/

@[expose] public section

namespace Silmaril.Accept

universe u v w

open scoped SetRel

/-- A top-level call of a session that returned, with its observed answer. -/
inductive Call (A : Type u) (Q : Type v) where
  /-- `process(a)` / `input(a)`: feed `a`, returning nothing. -/
  | feed (a : A)
  /-- `output()`: the query returned `q`. -/
  | query (q : Q)
  /-- `reset()`: return to the initial state. -/
  | reset
  deriving DecidableEq

namespace Call

variable {A : Type u} {Q : Type v}

/-- The fed value of a call, if it is a feed. -/
def feed? : Call A Q → Option A
  | .feed a => some a
  | _ => none

end Call

open Call

variable {A : Type u} {Q : Type v}

/-- The fed values of a call sequence, in order (queries and resets skipped). -/
def feeds (w : List (Call A Q)) : List A := w.filterMap Call.feed?

/-! ## Segments -/

/-- Reset-free suffixes after the start or after a reset: `w` with `pre ++ w ∈ T`, where `pre`
is empty or ends in `reset`. -/
def segments (T : Set (List (Call A Q))) : Set (List (Call A Q)) :=
  {w | reset ∉ w ∧ ∃ pre, (pre = [] ∨ ∃ p, pre = p ++ [reset]) ∧ pre ++ w ∈ T}

/-- The reset-free traces of `T`: segments starting at a fresh instance. -/
def freshSegments (T : Set (List (Call A Q))) : Set (List (Call A Q)) := {w | reset ∉ w ∧ w ∈ T}

/-! ## Relations -/

/-- (5) `input(a)` then `output()` from a fresh instance. -/
def freshFeedQuery (T : Set (List (Call A Q))) : A -|> Q := {p | [feed p.1, query p.2] ∈ T}

/-- (6) `process(a₁) … process(aₙ)` then `output()` from a fresh instance, no intermediate
queries. -/
def freshFeedsQuery (T : Set (List (Call A Q))) : List A -|> Q :=
  {p | p.1.map feed ++ [query p.2] ∈ T}

/-- (6), interleaved: feeds `as` with arbitrary intermediate queries, then `output()` answers
`q`, from a fresh instance. -/
def freshFeedsQueryAny (T : Set (List (Call A Q))) : List A -|> Q :=
  {p | ∃ w, reset ∉ w ∧ feeds w = p.1 ∧ w ++ [query p.2] ∈ T}

/-- (5) over every segment of a session. -/
def feedQuery (T : Set (List (Call A Q))) : A -|> Q := freshFeedQuery (segments T)

/-- (6) over every segment of a session. -/
def feedsQuery (T : Set (List (Call A Q))) : List A -|> Q := freshFeedsQuery (segments T)

/-- (6), interleaved, over every segment of a session. -/
def feedsQueryAny (T : Set (List (Call A Q))) : List A -|> Q := freshFeedsQueryAny (segments T)

/-! ## Hypotheses on a session model -/

/-- Every prefix of a trace is a trace. -/
def PrefixClosed (T : Set (List (Call A Q))) : Prop := ∀ u v, u ++ v ∈ T → u ∈ T

/-- Removing an answered query leaves a trace: queries do not change later behaviour. -/
def QueryDrop (T : Set (List (Call A Q))) : Prop :=
  ∀ u v q, u ++ query q :: v ∈ T → u ++ v ∈ T

/-- A query answer available after `u` can be inserted after `u` in any continuation. -/
def QueryInsert (T : Set (List (Call A Q))) : Prop :=
  ∀ u v q, u ++ [query q] ∈ T → u ++ v ∈ T → u ++ query q :: v ∈ T

/-- Queries are observations: they can be dropped and (when answerable) inserted. -/
def QueryPure (T : Set (List (Call A Q))) : Prop := QueryDrop T ∧ QueryInsert T

/-- After a returned reset the instance behaves as a fresh one. -/
def ResetSound (T : Set (List (Call A Q))) : Prop :=
  ∀ pre w, pre ++ [reset] ∈ T → (pre ++ reset :: w ∈ T ↔ w ∈ T)

/-! ## Chunked input -/

/-- A chunk of bytes, as fed by one `process(bytes)` call. -/
abbrev ByteChunk : Type := List UInt8

section Chunks

variable {α : Type w}

/-- Relate the flattened input to the answers of a chunk relation. -/
def flatRel (R : List (List α) -|> Q) : List α -|> Q :=
  {p | ∃ cs : List (List α), cs.flatten = p.1 ∧ (cs, p.2) ∈ R}

/-- The answers of `R` depend only on the flattened input, not on chunk boundaries. -/
def FlatInvariant (R : List (List α) -|> Q) : Prop :=
  ∀ cs cs' : List (List α), ∀ q, cs.flatten = cs'.flatten → ((cs, q) ∈ R ↔ (cs', q) ∈ R)

/-- (7) Chunks fed one per `process` call, then `output()`, over every segment. -/
abbrev chunksQuery (T : Set (List (Call (List α) Q))) : List (List α) -|> Q := feedsQuery T

/-- (7) The flattened input of the chunks fed before `output()`. -/
abbrev flatQuery (T : Set (List (Call (List α) Q))) : List α -|> Q := flatRel (chunksQuery T)

/-- (7) Answers depend only on the flattened input. -/
abbrev ChunkInvariant (T : Set (List (Call (List α) Q))) : Prop := FlatInvariant (chunksQuery T)

end Chunks

/-! ## Deterministic session models -/

/-- A deterministic component: an initial state, a step per fed value and an answer per state. -/
structure Machine (S : Type w) (A : Type u) (Q : Type v) where
  /-- The state of a fresh instance (and after `reset`). -/
  init : S
  /-- The effect of `process(a)`. -/
  step : S → A → S
  /-- The answer of `output()`. -/
  answer : S → Q

namespace Machine

variable {S : Type w} (m : Machine S A Q)

/-- The call sequence returns, from state `s`, with the recorded answers. -/
def Run : S → List (Call A Q) → Prop
  | _, [] => True
  | s, feed a :: t => Run (m.step s a) t
  | s, query q :: t => q = m.answer s ∧ Run s t
  | _, reset :: t => Run m.init t

/-- The state after a call sequence from `s`. -/
def after : S → List (Call A Q) → S
  | s, [] => s
  | s, feed a :: t => after (m.step s a) t
  | s, query _ :: t => after s t
  | _, reset :: t => after m.init t

/-- The session model of the machine: the call sequences a fresh instance returns from. -/
def traces : Set (List (Call A Q)) := {t | m.Run m.init t}

/-- The answer after feeding `as` to a fresh instance. -/
def respond (as : List A) : Q := m.answer (as.foldl m.step m.init)

/-- Feed a chunk element by element. -/
def chunked {α : Type u} (init : S) (step : S → α → S) (answer : S → Q) :
    Machine S (List α) Q :=
  ⟨init, fun s c => c.foldl step s, answer⟩

end Machine

end Silmaril.Accept
