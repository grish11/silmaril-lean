module

public import Silmaril.Semantics.Accept.Session.Thms

/-! # Relational acceptance of client sessions: worked examples and regression tests

A summing component (`sumM`), status-carrying answers, and three counterexamples: a model
where a query changes later answers (`queryCounter`), one where `reset` does not restore the
fresh behaviour (`badReset`), and one where chunk boundaries matter (`chunkCount`). Every
`example` is checked when the library builds.
-/

@[expose] public section

namespace Silmaril.Accept.SessionExamples

open Silmaril.Accept Silmaril.Accept.Call
open scoped SetRel

/-! ## A summing component -/

/-- `process(n)` adds `n`; `output()` answers the running sum. -/
def sumM : Machine ℕ ℕ ℕ := ⟨0, (· + ·), id⟩

example : ([1, 2, 3], 6) ∈ feedsQuery sumM.traces := by
  rw [Machine.feedsQuery_traces]; rfl

example : ([1, 2], 4) ∉ feedsQuery sumM.traces := by
  rw [Machine.feedsQuery_traces]; simp [Machine.respond, sumM]

example : (4, 4) ∈ feedQuery sumM.traces := by rw [Machine.feedQuery_traces]; rfl

/-- A session with a reset: the second segment starts from zero. -/
example : [feed 5, query 5, reset, feed 1, feed 2, query 3] ∈ sumM.traces := by
  simp [Machine.mem_traces, Machine.Run, sumM]

example : [feed 5, reset, query 5] ∉ sumM.traces := by
  simp [Machine.mem_traces, Machine.Run, sumM]

/-- The segment after the reset, directly from the definition. -/
example : [feed 1, feed 2, query 3] ∈ segments sumM.traces :=
  ⟨by simp, [feed 5, query 5, reset], .inr ⟨[feed 5, query 5], rfl⟩,
    by simp [Machine.mem_traces, Machine.Run, sumM]⟩

/-- Interleaved queries, directly from the definition. -/
example : ([1, 2], 3) ∈ feedsQueryAny sumM.traces :=
  ⟨[feed 1, query 1, feed 2], by simp, rfl,
    freshSegments_subset_segments ⟨by simp, by simp [Machine.mem_traces, Machine.Run, sumM]⟩⟩

example : feedsQueryAny sumM.traces = feedsQuery sumM.traces :=
  feedsQueryAny_eq_of_queryPure sumM.queryPure_traces

/-! ## Status-carrying answers -/

/-- Answers the sum while it is at most `10`, `none` afterwards. -/
def capM : Machine ℕ ℕ (Option ℕ) := ⟨0, (· + ·), fun s => if s ≤ 10 then some s else none⟩

example : ([3, 4], 7) ∈ someVals (feedsQuery capM.traces) := by
  rw [mem_someVals, Machine.feedsQuery_traces]; rfl

/-- `[5, 6]` only ever answers `none`: it has no successful value. -/
example : ([5, 6] : List ℕ) ∉ (someVals (feedsQuery capM.traces)).dom :=
  not_mem_dom_someVals fun c hc => by
    rw [Machine.feedsQuery_traces] at hc; simp [ofTotal, Machine.respond, capM] at hc; simp [← hc]

/-- A WIT-style `result<u32, string>` answer: `inl` is `ok`. -/
def witM : Machine ℕ ℕ (ℕ ⊕ String) :=
  ⟨0, (· + ·), fun s => if s % 2 = 0 then .inl s else .inr "odd"⟩

example : ([1, 3], 4) ∈ inlVals (feedsQuery witM.traces) := by
  rw [mem_inlVals, Machine.feedsQuery_traces]; rfl

example : ([1, 2], 3) ∉ inlVals (feedsQuery witM.traces) := by
  rw [mem_inlVals, Machine.feedsQuery_traces]; simp [ofTotal, Machine.respond, witM]

/-- An `Except`-valued answer. -/
def exM : Machine ℕ ℕ (Except String ℕ) :=
  ⟨0, (· + ·), fun s => if s < 5 then .ok s else .error "big"⟩

example : ([2], 2) ∈ okVals (feedsQuery exM.traces) := by
  rw [mem_okVals, Machine.feedsQuery_traces]; rfl

/-! ## Counterexample: a query that changes later answers -/

/-- `output()` answers how many times it was called before. -/
def queryCounter : Set (List (Call Unit ℕ)) := {[], [query 0], [query 0, query 1]}

theorem queryCounter_segments : segments queryCounter = freshSegments queryCounter :=
  segments_eq_freshSegments_of_resetFree fun t ht => by
    rcases ht with rfl | rfl | rfl <;> simp

/-- Without `QueryDrop`, an intermediate query changes the relation. -/
theorem feedsQueryAny_ne_feedsQuery : feedsQueryAny queryCounter ≠ feedsQuery queryCounter := by
  intro h
  have hany : (([] : List Unit), 1) ∈ feedsQueryAny queryCounter := by
    rw [feedsQueryAny, queryCounter_segments, freshFeedsQueryAny_freshSegments]
    exact ⟨[query 0], by simp, rfl, by simp [queryCounter]⟩
  rw [h, feedsQuery, queryCounter_segments, freshFeedsQuery_freshSegments] at hany
  simp [queryCounter] at hany

/-! ## Counterexample: an unsound reset -/

/-- A fresh instance answers `0`, but after a reset it answers `1`. -/
def badReset : Set (List (Call Unit ℕ)) :=
  {[], [query 0], [query 0, reset], [query 0, reset, query 1]}

theorem not_resetSound_badReset : ¬ ResetSound badReset := fun h => by
  have := (h [query 0] [query 1] (by simp [badReset])).1 (by simp [badReset])
  simp [badReset] at this

/-- Without `ResetSound`, the segment relation is not the fresh one. -/
theorem feedsQuery_ne_fresh_badReset : feedsQuery badReset ≠ freshFeedsQuery badReset := by
  intro h
  have hseg : (([] : List Unit), 1) ∈ feedsQuery badReset :=
    ⟨by simp, [query 0, reset], .inr ⟨[query 0], rfl⟩, by simp [badReset]⟩
  rw [h] at hseg
  simp [badReset] at hseg

/-! ## Chunked input -/

/-- Answers the number of chunks fed, so chunk boundaries matter. -/
def chunkCount : Machine ℕ (List ℕ) ℕ := ⟨0, fun n _ => n + 1, id⟩

example : ([[1, 2]], 1) ∈ chunksQuery chunkCount.traces := by
  rw [chunksQuery, Machine.feedsQuery_traces]; rfl

example : ([[1], [2]], 1) ∉ chunksQuery chunkCount.traces := by
  rw [chunksQuery, Machine.feedsQuery_traces]; simp [Machine.respond, chunkCount]

theorem not_chunkInvariant_chunkCount : ¬ ChunkInvariant chunkCount.traces := fun h => by
  have := (h [[1, 2]] [[1], [2]] 1 rfl).1 (by rw [chunksQuery, Machine.feedsQuery_traces]; rfl)
  rw [chunksQuery, Machine.feedsQuery_traces] at this
  simp [Machine.respond, chunkCount] at this

/-- An empty chunk is still a `process` call: `[[]]` flattens to `[]` but answers `1`. -/
example : (([] : List ℕ), 1) ∈ flatQuery chunkCount.traces :=
  ⟨[[]], rfl, by rw [chunksQuery, Machine.feedsQuery_traces]; rfl⟩

example : (([] : List (List ℕ)), 1) ∉ chunksQuery chunkCount.traces := by
  rw [chunksQuery, Machine.feedsQuery_traces]; simp [Machine.respond, chunkCount]

/-- Sums bytes, fed in chunks element by element. -/
def byteSum : Machine ℕ ByteChunk ℕ := Machine.chunked 0 (fun s (x : UInt8) => s + x.toNat) id

example : ChunkInvariant byteSum.traces := Machine.chunkInvariant_chunked

example : ([[1, 2], [3]], 6) ∈ chunksQuery byteSum.traces := by
  rw [chunksQuery, Machine.feedsQuery_traces]; rfl

/-- Under invariance the flattened, one-chunk and byte-at-a-time relations agree. -/
example : (([1, 2, 3] : List UInt8), 6) ∈ flatQuery byteSum.traces :=
  mem_flatQuery_of_mem_chunksQuery (cs := [[1, 2], [3]])
    (by rw [chunksQuery, Machine.feedsQuery_traces]; rfl)

example {xs : List UInt8} {q : ℕ} :
    (xs, q) ∈ flatQuery byteSum.traces ↔ ([xs], q) ∈ chunksQuery byteSum.traces :=
  FlatInvariant.mem_flatRel_iff_single Machine.chunkInvariant_chunked

example {xs : List UInt8} {q : ℕ} : (xs, q) ∈ flatQuery byteSum.traces ↔
    (xs.map (fun x => [x]), q) ∈ chunksQuery byteSum.traces :=
  FlatInvariant.mem_flatRel_iff_singletons Machine.chunkInvariant_chunked

example : (([[1], [2], [3]] : List ByteChunk), 6) ∈ chunksQuery byteSum.traces := by
  rw [chunksQuery, Machine.feedsQuery_traces]; rfl

end Silmaril.Accept.SessionExamples
