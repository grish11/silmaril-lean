module

public import Silmaril.Semantics.Accept.Session.Defs
public import Silmaril.Semantics.Accept.Success.Thms
import Silmaril.Proofs.Semantics.Accept.Session.Basic

/-!
# Relational acceptance of client sessions: laws

* membership: `mem_feedQuery`, `mem_feedsQuery`, `mem_feedsQueryAny` and their `fresh`
  versions; (5) is (6) at singletons (`mem_feedQuery_iff_feedsQuery`);
* segments and resets: `freshSegments_subset_segments`, `freshFeedsQuery_subset_feedsQuery`;
  under `ResetSound` and `PrefixClosed` the segment relations are the fresh ones
  (`segments_eq_freshSegments`, `feedsQuery_eq_fresh`, …), and also for reset-free models;
* interleaved queries: `feedsQuery_subset_feedsQueryAny`, and equality under `QueryDrop`
  (`feedsQueryAny_eq`, `feedsQueryAny_eq_of_queryPure`);
* status filters through `Silmaril.Semantics.Accept.Success`: `mem_someVals_feedsQuery`,
  `mem_okVals_feedsQuery`, `mem_inlVals_feedsQuery` and the `feedQuery` versions;
* chunked input: `mem_flatRel_of_mem`, `FlatInvariant.mem_iff`, `flatInvariant_iff`, the
  one-chunk and element-at-a-time forms (`FlatInvariant.flatRel_eq_single`,
  `FlatInvariant.flatRel_eq_singletons`), empty chunks (`FlatInvariant.cons_nil`), and the
  session forms for `chunksQuery`/`flatQuery`;
* deterministic models: `Machine.traces` is prefix-closed, query-pure and reset-sound, and
  its relations are the graph of `Machine.respond` (`Machine.feedsQuery_traces`);
  `Machine.chunked` is chunk-invariant.

Counterexamples (a model where an intermediate query matters, one where a reset does not
restore the fresh behaviour, and one where chunk boundaries matter) are in `Examples`.
-/

@[expose] public section

namespace Silmaril.Accept

universe u v w x

open scoped SetRel
open Call

variable {A : Type u} {Q : Type v} {T : Set (List (Call A Q))}

/-! ## Membership -/

section Mem

variable {a : A} {as : List A} {q : Q} {w : List (Call A Q)}

theorem mem_segments : w ∈ segments T ↔
    reset ∉ w ∧ ∃ pre, (pre = [] ∨ ∃ p, pre = p ++ [reset]) ∧ pre ++ w ∈ T := Iff.rfl

@[simp] theorem mem_freshSegments : w ∈ freshSegments T ↔ reset ∉ w ∧ w ∈ T := Iff.rfl

@[simp] theorem mem_freshFeedQuery : (a, q) ∈ freshFeedQuery T ↔ [feed a, query q] ∈ T := Iff.rfl

@[simp] theorem mem_freshFeedsQuery :
    (as, q) ∈ freshFeedsQuery T ↔ as.map feed ++ [query q] ∈ T := Iff.rfl

@[simp] theorem mem_freshFeedsQueryAny :
    (as, q) ∈ freshFeedsQueryAny T ↔ ∃ w, reset ∉ w ∧ feeds w = as ∧ w ++ [query q] ∈ T :=
  Iff.rfl

@[simp] theorem mem_feedQuery : (a, q) ∈ feedQuery T ↔ [feed a, query q] ∈ segments T := Iff.rfl

@[simp] theorem mem_feedsQuery :
    (as, q) ∈ feedsQuery T ↔ as.map feed ++ [query q] ∈ segments T := Iff.rfl

@[simp] theorem mem_feedsQueryAny : (as, q) ∈ feedsQueryAny T ↔
    ∃ w, reset ∉ w ∧ feeds w = as ∧ w ++ [query q] ∈ segments T := Iff.rfl

/-- (5) is (6) at singletons. -/
theorem mem_feedQuery_iff_feedsQuery : (a, q) ∈ feedQuery T ↔ ([a], q) ∈ feedsQuery T := Iff.rfl

theorem mem_freshFeedQuery_iff_freshFeedsQuery :
    (a, q) ∈ freshFeedQuery T ↔ ([a], q) ∈ freshFeedsQuery T := Iff.rfl

@[simp] theorem feeds_map_feed : feeds (as.map feed : List (Call A Q)) = as := by
  induction as <;> simp_all [feeds, Call.feed?]

end Mem

/-! ## Segments and resets -/

section Segments

variable {S S' : Set (List (Call A Q))}

theorem freshSegments_subset_segments : freshSegments T ⊆ segments T :=
  fun _ ⟨hw, hT⟩ => ⟨hw, [], .inl rfl, hT⟩

theorem freshFeedsQuery_mono (h : S ⊆ S') : freshFeedsQuery S ⊆ freshFeedsQuery S' :=
  fun _ hp => h hp

theorem freshFeedsQueryAny_mono (h : S ⊆ S') : freshFeedsQueryAny S ⊆ freshFeedsQueryAny S' :=
  fun _ ⟨w, hw, hf, hS⟩ => ⟨w, hw, hf, h hS⟩

@[simp] theorem freshFeedQuery_freshSegments :
    freshFeedQuery (freshSegments T) = freshFeedQuery T := by
  ext ⟨a, q⟩; simp

@[simp] theorem freshFeedsQuery_freshSegments :
    freshFeedsQuery (freshSegments T) = freshFeedsQuery T := by ext ⟨as, q⟩; simp

@[simp] theorem freshFeedsQueryAny_freshSegments :
    freshFeedsQueryAny (freshSegments T) = freshFeedsQueryAny T := by ext ⟨as, q⟩; simp; grind

theorem freshFeedQuery_subset_feedQuery : freshFeedQuery T ⊆ feedQuery T :=
  freshFeedQuery_freshSegments (T := T) ▸ fun _ hp => freshSegments_subset_segments hp

theorem freshFeedsQuery_subset_feedsQuery : freshFeedsQuery T ⊆ feedsQuery T :=
  freshFeedsQuery_freshSegments (T := T) ▸ freshFeedsQuery_mono freshSegments_subset_segments

theorem freshFeedsQueryAny_subset_feedsQueryAny : freshFeedsQueryAny T ⊆ feedsQueryAny T :=
  freshFeedsQueryAny_freshSegments (T := T) ▸ freshFeedsQueryAny_mono freshSegments_subset_segments

/-- Under a sound reset and prefix closure, segments are the reset-free traces. -/
theorem segments_eq_freshSegments (hR : ResetSound T) (hP : PrefixClosed T) :
    segments T = freshSegments T :=
  Proofs.Semantics.Accept.Session.segments_eq_freshSegments hR hP

/-- A model with no reset has the reset-free traces as segments. -/
theorem segments_eq_freshSegments_of_resetFree (h : ∀ t ∈ T, reset ∉ t) :
    segments T = freshSegments T :=
  Proofs.Semantics.Accept.Session.segments_eq_freshSegments_of_resetFree h

theorem feedQuery_eq_fresh (hR : ResetSound T) (hP : PrefixClosed T) :
    feedQuery T = freshFeedQuery T := by
  rw [feedQuery, segments_eq_freshSegments hR hP, freshFeedQuery_freshSegments]

theorem feedsQuery_eq_fresh (hR : ResetSound T) (hP : PrefixClosed T) :
    feedsQuery T = freshFeedsQuery T := by
  rw [feedsQuery, segments_eq_freshSegments hR hP, freshFeedsQuery_freshSegments]

theorem feedsQueryAny_eq_fresh (hR : ResetSound T) (hP : PrefixClosed T) :
    feedsQueryAny T = freshFeedsQueryAny T := by
  rw [feedsQueryAny, segments_eq_freshSegments hR hP, freshFeedsQueryAny_freshSegments]

end Segments

/-! ## Interleaved queries -/

theorem freshFeedsQuery_subset_freshFeedsQueryAny : freshFeedsQuery T ⊆ freshFeedsQueryAny T :=
  fun ⟨as, _⟩ hp => ⟨as.map feed, by simp, feeds_map_feed, hp⟩

theorem feedsQuery_subset_feedsQueryAny : feedsQuery T ⊆ feedsQueryAny T :=
  freshFeedsQuery_subset_freshFeedsQueryAny

theorem QueryPure.queryDrop (h : QueryPure T) : QueryDrop T := h.1

theorem QueryPure.queryInsert (h : QueryPure T) : QueryInsert T := h.2

/-- Dropping queries is compatible with segments. -/
theorem queryDrop_segments (h : QueryDrop T) : QueryDrop (segments T) :=
  Proofs.Semantics.Accept.Session.queryDrop_segments h

theorem freshFeedsQueryAny_eq (h : QueryDrop T) : freshFeedsQueryAny T = freshFeedsQuery T :=
  (Proofs.Semantics.Accept.Session.freshFeedsQueryAny_subset h).antisymm
    freshFeedsQuery_subset_freshFeedsQueryAny

/-- When answered queries can be dropped, intermediate queries do not change the relation. -/
theorem feedsQueryAny_eq (h : QueryDrop T) : feedsQueryAny T = feedsQuery T :=
  freshFeedsQueryAny_eq (queryDrop_segments h)

theorem feedsQueryAny_eq_of_queryPure (h : QueryPure T) : feedsQueryAny T = feedsQuery T :=
  feedsQueryAny_eq h.queryDrop

/-! ## Status filters -/

section Status

variable {β : Type w} {ε : Type x} {a : A} {as : List A} {b : β}

@[simp] theorem mem_someVals_feedsQuery {T : Set (List (Call A (Option β)))} :
    (as, b) ∈ someVals (feedsQuery T) ↔ as.map feed ++ [query (some b)] ∈ segments T := by simp

@[simp] theorem mem_okVals_feedsQuery {T : Set (List (Call A (Except ε β)))} :
    (as, b) ∈ okVals (feedsQuery T) ↔ as.map feed ++ [query (.ok b)] ∈ segments T := by simp

@[simp] theorem mem_inlVals_feedsQuery {T : Set (List (Call A (β ⊕ ε)))} :
    (as, b) ∈ inlVals (feedsQuery T) ↔ as.map feed ++ [query (.inl b)] ∈ segments T := by simp

@[simp] theorem mem_someVals_feedQuery {T : Set (List (Call A (Option β)))} :
    (a, b) ∈ someVals (feedQuery T) ↔ [feed a, query (some b)] ∈ segments T := by simp

@[simp] theorem mem_okVals_feedQuery {T : Set (List (Call A (Except ε β)))} :
    (a, b) ∈ okVals (feedQuery T) ↔ [feed a, query (.ok b)] ∈ segments T := by simp

@[simp] theorem mem_inlVals_feedQuery {T : Set (List (Call A (β ⊕ ε)))} :
    (a, b) ∈ inlVals (feedQuery T) ↔ [feed a, query (.inl b)] ∈ segments T := by simp

end Status

/-! ## Chunked input -/

section Chunks

variable {α : Type w} {R : List (List α) -|> Q} {cs : List (List α)} {xs : List α} {q : Q}

theorem mem_flatRel : (xs, q) ∈ flatRel R ↔ ∃ cs, cs.flatten = xs ∧ (cs, q) ∈ R := Iff.rfl

/-- `flatRel R` is the image of `R` along `List.flatten`. -/
theorem flatRel_eq_image : flatRel R = Prod.map List.flatten id '' R := by
  ext ⟨xs, q⟩; simp only [mem_flatRel, Set.mem_image, Prod.exists, Prod.map, Prod.mk.injEq]
  grind

theorem mem_flatRel_of_mem (h : (cs, q) ∈ R) : (cs.flatten, q) ∈ flatRel R := ⟨cs, rfl, h⟩

theorem FlatInvariant.mem_iff (h : FlatInvariant R) : (cs, q) ∈ R ↔ (cs.flatten, q) ∈ flatRel R :=
  ⟨mem_flatRel_of_mem, fun ⟨cs', he, h'⟩ => (h cs' cs q he).1 h'⟩

theorem flatInvariant_iff : FlatInvariant R ↔ ∀ cs q, (cs.flatten, q) ∈ flatRel R → (cs, q) ∈ R :=
  ⟨fun h _ _ => h.mem_iff.2, fun h cs cs' q he =>
    ⟨fun hc => h cs' q (he ▸ mem_flatRel_of_mem hc), fun hc => h cs q (he ▸ mem_flatRel_of_mem hc)⟩⟩

/-- Under invariance the flat relation is the one-chunk relation. -/
theorem FlatInvariant.mem_flatRel_iff_single (h : FlatInvariant R) :
    (xs, q) ∈ flatRel R ↔ ([xs], q) ∈ R := by simpa using (h.mem_iff (cs := [xs])).symm

/-- Under invariance the flat relation is the element-at-a-time relation. -/
theorem FlatInvariant.mem_flatRel_iff_singletons (h : FlatInvariant R) :
    (xs, q) ∈ flatRel R ↔ (xs.map (fun x => [x]), q) ∈ R := by
  have e : (xs.map fun x => [x]).flatten = xs := by induction xs <;> simp_all
  simpa [e] using (h.mem_iff (cs := xs.map (fun x => [x])) (q := q)).symm

theorem FlatInvariant.flatRel_eq_single (h : FlatInvariant R) :
    flatRel R = {p | ([p.1], p.2) ∈ R} := by ext ⟨xs, q⟩; exact h.mem_flatRel_iff_single

theorem FlatInvariant.flatRel_eq_singletons (h : FlatInvariant R) :
    flatRel R = {p | (p.1.map (fun x => [x]), p.2) ∈ R} := by
  ext ⟨xs, q⟩; exact h.mem_flatRel_iff_singletons

/-- Under invariance an empty chunk changes nothing. -/
theorem FlatInvariant.cons_nil (h : FlatInvariant R) : ([] :: cs, q) ∈ R ↔ (cs, q) ∈ R :=
  h _ _ q (by simp)

theorem FlatInvariant.append_nil (h : FlatInvariant R) : (cs ++ [[]], q) ∈ R ↔ (cs, q) ∈ R :=
  h _ _ q (by simp)

variable {T : Set (List (Call (List α) Q))}

theorem mem_flatQuery_of_mem_chunksQuery (h : (cs, q) ∈ chunksQuery T) :
    (cs.flatten, q) ∈ flatQuery T := mem_flatRel_of_mem h

/-- (7) Under chunk invariance, a chunked session answers exactly as its flattened input. -/
theorem ChunkInvariant.mem_chunksQuery_iff (h : ChunkInvariant T) :
    (cs, q) ∈ chunksQuery T ↔ (cs.flatten, q) ∈ flatQuery T := FlatInvariant.mem_iff h

theorem ChunkInvariant.flatQuery_eq_single (h : ChunkInvariant T) :
    flatQuery T = {p | ([p.1], p.2) ∈ chunksQuery T} := FlatInvariant.flatRel_eq_single h

theorem ChunkInvariant.flatQuery_eq_singletons (h : ChunkInvariant T) :
    flatQuery T = {p | (p.1.map (fun x => [x]), p.2) ∈ chunksQuery T} :=
  FlatInvariant.flatRel_eq_singletons h

/-- With a sound reset, chunk invariance over segments is chunk invariance from fresh. -/
theorem chunkInvariant_iff_fresh (hR : ResetSound T) (hP : PrefixClosed T) :
    ChunkInvariant T ↔ FlatInvariant (freshFeedsQuery T) := by
  rw [ChunkInvariant, chunksQuery, feedsQuery_eq_fresh hR hP]

end Chunks

/-! ## Deterministic session models -/

namespace Machine

variable {S : Type w} (m : Machine S A Q)

theorem mem_traces {t : List (Call A Q)} : t ∈ m.traces ↔ m.Run m.init t := Iff.rfl

theorem prefixClosed_traces : PrefixClosed m.traces :=
  Proofs.Semantics.Accept.Session.prefixClosed_traces m

theorem queryPure_traces : QueryPure m.traces :=
  ⟨Proofs.Semantics.Accept.Session.queryDrop_traces m,
    Proofs.Semantics.Accept.Session.queryInsert_traces m⟩

theorem resetSound_traces : ResetSound m.traces :=
  Proofs.Semantics.Accept.Session.resetSound_traces m

theorem segments_traces : segments m.traces = freshSegments m.traces :=
  segments_eq_freshSegments m.resetSound_traces m.prefixClosed_traces

theorem mem_freshFeedsQuery_traces {as : List A} {q : Q} :
    (as, q) ∈ freshFeedsQuery m.traces ↔ m.respond as = q :=
  Proofs.Semantics.Accept.Session.mem_freshFeedsQuery_traces m

/-- A deterministic model relates feeds to the answer after them, across resets. -/
theorem feedsQuery_traces : feedsQuery m.traces = ofTotal m.respond := by
  rw [feedsQuery_eq_fresh m.resetSound_traces m.prefixClosed_traces]
  ext ⟨as, q⟩; exact m.mem_freshFeedsQuery_traces

theorem feedsQueryAny_traces : feedsQueryAny m.traces = ofTotal m.respond := by
  rw [feedsQueryAny_eq_of_queryPure m.queryPure_traces, feedsQuery_traces]

theorem feedQuery_traces : feedQuery m.traces = ofTotal fun a => m.respond [a] := by
  ext ⟨a, q⟩; exact mem_feedQuery_iff_feedsQuery.trans (by rw [feedsQuery_traces]; rfl)

theorem respond_chunked {α : Type u} {init : S} {step : S → α → S} {answer : S → Q}
    {cs : List (List α)} :
    (chunked init step answer).respond cs = answer (cs.flatten.foldl step init) := by
  simp [respond, chunked, List.foldl_flatten]

/-- Feeding a chunk element by element is chunk-invariant. -/
theorem chunkInvariant_chunked {α : Type u} {init : S} {step : S → α → S} {answer : S → Q} :
    ChunkInvariant (chunked init step answer).traces := fun cs cs' q he => by
  simp only [chunksQuery, feedsQuery_traces, ofTotal, Function.mem_graph, respond_chunked, he]

end Machine

end Silmaril.Accept
