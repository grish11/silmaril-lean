module

public import Silmaril.Semantics.Accept.Session.Defs

/-! # Proofs: segments, query purity and deterministic session models -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Accept.Session

open Silmaril.Accept Silmaril.Accept.Call

universe u v w

variable {A : Type u} {Q : Type v} {T : Set (List (Call A Q))}

/-! ## Segments -/

theorem segments_eq_freshSegments (hR : ResetSound T) (hP : PrefixClosed T) :
    segments T = freshSegments T := by
  ext w
  constructor
  · rintro ⟨hw, pre, hpre | ⟨p, rfl⟩, hT⟩
    · subst hpre; exact ⟨hw, hT⟩
    · exact ⟨hw, (hR p w (hP _ w hT)).1 (by simpa using hT)⟩
  · rintro ⟨hw, hT⟩; exact ⟨hw, [], .inl rfl, hT⟩

theorem segments_eq_freshSegments_of_resetFree (h : ∀ t ∈ T, reset ∉ t) :
    segments T = freshSegments T := by
  ext w
  constructor
  · rintro ⟨hw, pre, hpre | ⟨p, rfl⟩, hT⟩
    · subst hpre; exact ⟨hw, hT⟩
    · exact absurd (by simp) (h _ hT)
  · rintro ⟨hw, hT⟩; exact ⟨hw, [], .inl rfl, hT⟩

theorem queryDrop_segments (h : QueryDrop T) : QueryDrop (segments T) := by
  rintro u v q ⟨hw, pre, hpre, hT⟩
  refine ⟨by simp_all, pre, hpre, ?_⟩
  simpa using h (pre ++ u) v q (by simpa using hT)

/-! ## Dropping queries -/

theorem drop_queries (h : QueryDrop T) : ∀ (w u v : List (Call A Q)), reset ∉ w →
    u ++ w ++ v ∈ T → u ++ (feeds w).map feed ++ v ∈ T
  | [], _, _, _, hT => by simpa [feeds] using hT
  | feed a :: w, u, v, hw, hT => by
      have := drop_queries h w (u ++ [feed a]) v (by simp_all) (by simpa using hT)
      simpa [feeds, List.filterMap_cons, Call.feed?] using this
  | query q :: w, u, v, hw, hT => by
      have := drop_queries h w u v (by simp_all)
        (by simpa using h u (w ++ v) q (by simpa using hT))
      simpa [feeds, List.filterMap_cons, Call.feed?] using this
  | reset :: _, _, _, hw, _ => absurd List.mem_cons_self hw

theorem freshFeedsQueryAny_subset (h : QueryDrop T) : freshFeedsQueryAny T ⊆ freshFeedsQuery T := by
  rintro ⟨as, q⟩ ⟨w, hw, rfl, hT⟩
  show _ ∈ T
  simpa using drop_queries h w [] [query q] hw (by simpa using hT)

/-! ## Deterministic session models -/

section Machine

variable {S : Type w} (m : Machine S A Q)

theorem run_append : ∀ (s : S) (u v : List (Call A Q)),
    m.Run s (u ++ v) ↔ m.Run s u ∧ m.Run (m.after s u) v
  | s, [], v => by simp [Machine.Run, Machine.after]
  | s, feed a :: u, v => by
      simp only [List.cons_append, Machine.Run, Machine.after]; exact run_append _ u v
  | s, query q :: u, v => by
      simp only [List.cons_append, Machine.Run, Machine.after]; rw [run_append s u v, and_assoc]
  | s, reset :: u, v => by
      simp only [List.cons_append, Machine.Run, Machine.after]; exact run_append _ u v

theorem run_feeds : ∀ (s : S) (as : List A) (v : List (Call A Q)),
    m.Run s (as.map feed ++ v) ↔ m.Run (as.foldl m.step s) v
  | _, [], _ => Iff.rfl
  | s, a :: as, v => by
      simp only [List.map_cons, List.cons_append, Machine.Run, List.foldl_cons]
      exact run_feeds (m.step s a) as v

theorem prefixClosed_traces : PrefixClosed m.traces :=
  fun u v h => ((run_append m _ u v).1 h).1

theorem queryDrop_traces : QueryDrop m.traces := fun u v q h => by
  have h1 := (run_append m m.init u (query q :: v)).1 h
  simp only [Machine.Run] at h1
  exact (run_append m _ u v).2 ⟨h1.1, h1.2.2⟩

theorem queryInsert_traces : QueryInsert m.traces := fun u v q hq h => by
  have h1 := (run_append m m.init u [query q]).1 hq
  have h2 := (run_append m m.init u v).1 h
  simp only [Machine.Run] at h1
  exact (run_append m _ u (query q :: v)).2 ⟨h2.1, by simp only [Machine.Run]; exact ⟨h1.2.1, h2.2⟩⟩

theorem resetSound_traces : ResetSound m.traces := fun pre w hpre => by
  have h1 := ((run_append m m.init pre [reset]).1 hpre).1
  show m.Run m.init (pre ++ reset :: w) ↔ m.Run m.init w
  rw [run_append]; simp only [Machine.Run]; exact ⟨And.right, fun h => ⟨h1, h⟩⟩

theorem mem_freshFeedsQuery_traces {as : List A} {q : Q} :
    (as, q) ∈ freshFeedsQuery m.traces ↔ m.respond as = q := by
  show m.Run m.init (as.map feed ++ [query q]) ↔ _
  rw [run_feeds]; simp [Machine.Run, Machine.respond, eq_comm]

end Machine

end Silmaril.Proofs.Semantics.Accept.Session
