module

public import Silmaril.Semantics.TrackA.Concurrency.Projection.Defs
import Silmaril.Semantics.TrackA.Concurrency.Thms

public section

namespace Silmaril.Proofs.Semantics.TrackA.Concurrency.Projection

open Silmaril.Semantics.TrackA.Concurrency
open Silmaril.Semantics.TrackA.Concurrency.Projection

variable {T L R : Type} {xs ys : List (Event T L R)}

theorem observe_inter (outer inner : Interface L R) (xs : List (Event T L R)) :
    (outer.inter inner).observe xs = inner.observe (outer.observe xs) := by
  simp only [Interface.observe, List.filter_filter]
  congr
  funext e
  cases e.action <;> simp [Interface.exposes, Interface.inter, Bool.and_comm]

theorem observedRun_inter [DecidableEq T] [DecidableEq L] [DecidableEq R]
    (outer inner : Interface L R) {start finish : Config T L R} :
    (outer.inter inner).ObservedRun start ys finish ↔
      ∃ mid, outer.ObservedRun start mid finish ∧ inner.observe mid = ys := by
  constructor
  · rintro ⟨xs, run, visible⟩
    exact ⟨_, ⟨xs, run, rfl⟩, (observe_inter outer inner xs).symm.trans visible⟩
  · rintro ⟨_, ⟨xs, run, rfl⟩, visible⟩
    exact ⟨xs, run, (observe_inter outer inner xs).trans visible⟩

theorem interface_retains_iff (view : Interface L R) (k : Fin xs.length) :
    (view.projection xs).Retains k ↔ view.exposes xs[k.val].action = true := by
  have member : k ∈ view.positions xs ↔ view.exposes xs[k.val].action = true := by
    simp [Interface.positions]
  rw [← member, List.mem_iff_getElem]
  constructor
  · rintro ⟨i, eq⟩
    exact ⟨i.val, _, eq⟩
  · rintro ⟨i, bound, eq⟩
    exact ⟨⟨i, by simpa [view.observe_eq_map xs] using bound⟩, eq⟩

variable (p : Projection xs ys) {profile : RaceProfile}

private theorem index_lt_iff {i j : Fin ys.length} : p.index i < p.index j ↔ i < j :=
  p.mono.lt_iff_lt

theorem conflicts_eq [DecidableEq T] [DecidableEq R] (i j : Fin ys.length) :
    conflicts ys[i.val] ys[j.val] = conflicts xs[(p.index i).val] xs[(p.index j).val] := by
  rw [p.event_eq i, p.event_eq j]

variable [DecidableEq R]

private theorem overwrite_iff {i j : Fin xs.length} {loc : R} :
    ((xs.take j).drop (i.val + 1)).any (fun e => e.action.writesTo loc) = true ↔
      HasOverwrite xs i j loc := by
  have length : (xs.take j).length = j := List.length_take_of_le (Nat.le_of_lt j.isLt)
  simp only [HasOverwrite, List.any_eq_true, List.mem_iff_getElem, List.length_drop, length]
  constructor
  · rintro ⟨event, ⟨k, bound, rfl⟩, writes⟩
    have within : i.val + 1 + k < j.val := by omega
    exact ⟨⟨i.val + 1 + k, Nat.lt_trans within j.isLt⟩, by change i.val < i.val + 1 + k; omega, within,
      by simpa only [List.getElem_drop, List.getElem_take] using writes⟩
  · rintro ⟨k, after, before, writes⟩
    have after' : i.val < k.val := after
    have before' : k.val < j.val := before
    let offset := k.val - (i.val + 1)
    have bound : offset < j.val - (i.val + 1) := by dsimp [offset]; omega
    have eq : i.val + 1 + offset = k.val := by dsimp [offset]; omega
    have sliceBound : offset < ((xs.take j).drop (i.val + 1)).length := by
      simpa only [List.length_drop, length] using bound
    refine ⟨((xs.take j).drop (i.val + 1))[offset], ⟨offset, bound, rfl⟩, ?_⟩
    simp only [List.getElem_drop, List.getElem_take]
    have eventEq : xs[i.val + 1 + offset] = xs[k.val] := getElem_congr_idx eq
    rwa [eventEq]

private theorem overwrite_to_source {i j : Fin ys.length} {loc : R}
    (h : HasOverwrite ys i j loc) : HasOverwrite xs (p.index i) (p.index j) loc := by
  obtain ⟨k, after, before, writes⟩ := h
  exact ⟨p.index k, p.mono after, p.mono before, p.event_eq k ▸ writes⟩

private theorem atomicSync_iff {i j : Fin xs.length} :
    atomicSync xs i j xs[i.val].action xs[j.val].action = true ↔
      ∃ (loc : R) (v w : Nat), xs[i.val].action = .write .scAtomic loc v ∧
        xs[j.val].action = .read .scAtomic loc w ∧ ¬ HasOverwrite xs i j loc := by
  cases a : xs[i.val].action <;> cases b : xs[j.val].action <;> simp [atomicSync]
  next mode loc v otherMode other w =>
    cases mode <;> cases otherMode <;> simp [← overwrite_iff]
    exact fun _ => eq_comm

private theorem atomic_to_observed {i j : Fin ys.length}
    (sync : atomicSync xs (p.index i) (p.index j) xs[(p.index i).val].action
      xs[(p.index j).val].action = true) :
    atomicSync ys i j ys[i.val].action ys[j.val].action = true := by
  obtain ⟨loc, v, w, write, read, clear⟩ := atomicSync_iff.mp sync
  exact atomicSync_iff.mpr ⟨loc, v, w, by rwa [p.event_eq i], by rwa [p.event_eq j],
    fun overwrite => clear (overwrite_to_source p overwrite)⟩

private theorem atomic_to_source {i j : Fin ys.length} (covers : p.CoversOverwrites)
    (sync : atomicSync ys i j ys[i.val].action ys[j.val].action = true) :
    atomicSync xs (p.index i) (p.index j) xs[(p.index i).val].action
      xs[(p.index j).val].action = true := by
  obtain ⟨loc, v, w, write, read, clear⟩ := atomicSync_iff.mp sync
  exact atomicSync_iff.mpr ⟨loc, v, w, by rwa [← p.event_eq i], by rwa [← p.event_eq j],
    fun overwrite => clear (covers i j loc v w write read overwrite)⟩

theorem atomicSync_eq (covers : p.CoversOverwrites) (i j : Fin ys.length) :
    atomicSync ys i j ys[i.val].action ys[j.val].action =
      atomicSync xs (p.index i) (p.index j) xs[(p.index i).val].action xs[(p.index j).val].action :=
  Bool.eq_iff_iff.mpr ⟨atomic_to_source p covers, atomic_to_observed p⟩

variable [DecidableEq T] [DecidableEq L]

private abbrev Edge (profile : RaceProfile) (xs : List (Event T L R)) (a b : Fin xs.length) :=
  direct profile xs a b = true

private abbrev Path (profile : RaceProfile) (xs : List (Event T L R)) :=
  Relation.TransGen (Edge profile xs)

private theorem edge_iff {a b : Fin xs.length} :
    Edge profile xs a b ↔ a < b ∧ (xs[a.val].thread = xs[b.val].thread ∨
      mutexSync xs[a.val].action xs[b.val].action = true ∨
      profile = .mixed ∧ atomicSync xs a b xs[a.val].action xs[b.val].action = true) := by
  change direct profile xs a b = true ↔ _
  cases profile <;> by_cases lt : a.val < b.val <;>
    simp [direct, lt, or_assoc, Fin.lt_def]

private theorem edge_to_observed {i j : Fin ys.length}
    (edge : Edge profile xs (p.index i) (p.index j)) : Edge profile ys i j := by
  obtain ⟨lt, kinds⟩ := edge_iff.mp edge
  refine edge_iff.mpr ⟨(index_lt_iff p).mp lt, ?_⟩
  rcases kinds with order | mutex | ⟨mixed, atomic⟩
  · exact .inl (by rwa [p.event_eq i, p.event_eq j])
  · exact .inr (.inl (by rwa [p.event_eq i, p.event_eq j]))
  · exact .inr (.inr ⟨mixed, atomic_to_observed p atomic⟩)

private theorem edge_to_source (covers : profile = .mixed → p.CoversOverwrites)
    {i j : Fin ys.length} (edge : Edge profile ys i j) : Edge profile xs (p.index i) (p.index j) := by
  obtain ⟨lt, kinds⟩ := edge_iff.mp edge
  refine edge_iff.mpr ⟨p.mono lt, ?_⟩
  rcases kinds with order | mutex | ⟨mixed, atomic⟩
  · exact .inl (by rwa [← p.event_eq i, ← p.event_eq j])
  · exact .inr (.inl (by rwa [← p.event_eq i, ← p.event_eq j]))
  · exact .inr (.inr ⟨mixed, atomic_to_source p (covers mixed) atomic⟩)

theorem direct_eq (covers : profile = .mixed → p.CoversOverwrites) (i j : Fin ys.length) :
    direct profile ys i j = direct profile xs (p.index i) (p.index j) :=
  Bool.eq_iff_iff.mpr ⟨edge_to_source p covers, edge_to_observed p⟩

private theorem direct_bounds {a b : Nat} (edge : direct profile xs a b = true) :
    a < xs.length ∧ b < xs.length := by
  unfold direct at edge
  split at edge
  next lt =>
    by_cases bound : b < xs.length
    · exact ⟨lt.trans bound, bound⟩
    · simp [List.getElem?_eq_none (Nat.le_of_not_gt bound)] at edge
  next => simp at edge

private theorem path_of_transGen {a b : Nat}
    (path : Relation.TransGen (fun i j => direct profile xs i j = true) a b)
    (ha : a < xs.length) (hb : b < xs.length) : Path profile xs ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction path with
  | single edge => exact .single edge
  | tail _ edge ih => exact .tail (ih (direct_bounds edge).1) edge

private theorem hb_iff_path {a b : Fin xs.length} :
    happensBefore profile xs a b = true ↔ Path profile xs a b := by
  rw [happensBefore_iff_transGen]
  exact ⟨fun path => path_of_transGen path a.isLt b.isLt,
    fun path => Relation.TransGen.lift Fin.val (fun _ _ edge => edge) a b path⟩

theorem happensBefore_to_source (covers : profile = .mixed → p.CoversOverwrites)
    {i j : Fin ys.length} (hb : happensBefore profile ys i j = true) :
    happensBefore profile xs (p.index i) (p.index j) = true :=
  hb_iff_path.mpr (Relation.TransGen.lift p.index
    (fun _ _ edge => edge_to_source p covers edge) i j (hb_iff_path.mp hb))

private abbrev ProgramOrder (xs : List (Event T L R)) (a b : Fin xs.length) :=
  a < b ∧ xs[a.val].thread = xs[b.val].thread

omit [DecidableEq T] [DecidableEq L] [DecidableEq R] in
private theorem join_order {a b c : Fin xs.length}
    (ab : ProgramOrder xs a b) (bc : b = c ∨ ProgramOrder xs b c) : ProgramOrder xs a c := by
  rcases bc with rfl | ⟨lt, thread⟩
  · exact ab
  · exact ⟨ab.1.trans lt, ab.2.trans thread⟩

private theorem append_order {i k j : Fin ys.length} (path : Path profile ys i k)
    (last : p.index k = p.index j ∨ ProgramOrder xs (p.index k) (p.index j)) :
    Path profile ys i j := by
  rcases last with eq | order
  · rwa [← p.mono.injective eq]
  · exact .tail path (edge_to_observed p (edge_iff.mpr ⟨order.1, .inl order.2⟩))

/-- Compress same-thread stretches between retained synchronization endpoints. -/
private theorem project_path (keeps : p.KeepsCrossThreadEdges profile)
    {i j : Fin ys.length} {b : Fin xs.length} (path : Path profile xs (p.index i) b)
    (last : b = p.index j ∨ ProgramOrder xs b (p.index j)) : Path profile ys i j := by
  induction path generalizing j with
  | @single b edge =>
    have lt := (edge_iff.mp edge).1
    by_cases same : xs[(p.index i).val].thread = xs[b.val].thread
    · have order := join_order (xs := xs) ⟨lt, same⟩ last
      exact .single (edge_to_observed p (edge_iff.mpr ⟨order.1, .inl order.2⟩))
    · obtain ⟨k, rfl⟩ := (keeps _ _ same edge).2
      exact append_order p (.single (edge_to_observed p edge)) last
  | @tail a b _ edge ih =>
    have lt := (edge_iff.mp edge).1
    by_cases same : xs[a.val].thread = xs[b.val].thread
    · exact ih (.inr (join_order ⟨lt, same⟩ last))
    · obtain ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩ := keeps _ _ same edge
      exact append_order p (.tail (ih (.inl rfl)) (edge_to_observed p edge)) last

theorem happensBefore_to_observed (keeps : p.KeepsCrossThreadEdges profile)
    {i j : Fin ys.length} (hb : happensBefore profile xs (p.index i) (p.index j) = true) :
    happensBefore profile ys i j = true :=
  hb_iff_path.mpr (project_path p keeps (hb_iff_path.mp hb) (.inl rfl))

omit [DecidableEq R] in
private theorem mutexSync_iff {a b : Action L R} :
    mutexSync a b = true ↔ ∃ k, a = .release k ∧ b = .acquire k := by
  cases a <;> cases b <;> simp [mutexSync]
  next l k => exact eq_comm

theorem interface_keepsCrossThreadEdges (view : Interface L R)
    (sync : view.CoversSynchronization profile xs) :
    (view.projection xs).KeepsCrossThreadEdges profile := by
  intro a b different edge
  rw [interface_retains_iff, interface_retains_iff]
  obtain ⟨_, order | mutex | ⟨mixed, atomic⟩⟩ := edge_iff.mp edge
  · exact (different order).elim
  · obtain ⟨k, release, acquire⟩ := mutexSync_iff.mp mutex
    exact ⟨by rw [release]; exact sync.1 a k (.inr release),
      by rw [acquire]; exact sync.1 b k (.inl acquire)⟩
  · obtain ⟨loc, v, w, write, read, _⟩ := atomicSync_iff.mp atomic
    exact ⟨by rw [write]; exact sync.2 mixed a loc v (.inr write),
      by rw [read]; exact sync.2 mixed b loc w (.inl read)⟩

omit [DecidableEq L] in
private theorem exposes_write (view : Interface L R) {action : Action L R} {loc : R}
    (visible : view.resource loc = true) (writes : action.writesTo loc = true) :
    view.exposes action = true := by
  cases action <;> simp_all [Action.writesTo, Interface.exposes]

omit [DecidableEq T] [DecidableEq L] in
theorem interface_coversOverwrites (view : Interface L R)
    (sync : view.CoversSynchronization .mixed xs) :
    (view.projection xs).CoversOverwrites := by
  let p := view.projection xs
  intro i j loc v _ write _ overwrite
  change (view.observe xs)[i.val].action = _ at write
  have sourceWrite : xs[(p.index i).val].action = .write .scAtomic loc v := by
    rwa [← p.event_eq i]
  obtain ⟨k, after, before, writes⟩ := overwrite
  have visible := exposes_write view (sync.2 rfl (p.index i) loc v (.inr sourceWrite)) writes
  obtain ⟨mid, rfl⟩ := (interface_retains_iff view k).mpr visible
  exact ⟨mid, (index_lt_iff p).mp after, (index_lt_iff p).mp before,
    by rwa [p.event_eq mid]⟩

private theorem racePair_iff {i j : Fin xs.length} :
    racePair profile xs i j = true ↔ i < j ∧ conflicts xs[i.val] xs[j.val] = true ∧
      happensBefore profile xs i j = false ∧
      (profile = .mixed → (xs[i.val].action.isAtomic && xs[j.val].action.isAtomic) = false) := by
  cases profile <;> by_cases lt : i.val < j.val <;>
    simp [racePair, lt, Fin.lt_def, and_assoc]
  cases xs[i.val].action.isAtomic <;> simp

theorem racePair_to_observed (covers : profile = .mixed → p.CoversOverwrites)
    {i j : Fin ys.length} (race : racePair profile xs (p.index i) (p.index j) = true) :
    racePair profile ys i j = true := by
  obtain ⟨lt, conflict, unordered, mode⟩ := racePair_iff.mp race
  refine racePair_iff.mpr ⟨(index_lt_iff p).mp lt, (conflicts_eq p i j).trans conflict,
    Bool.eq_false_iff.mpr (fun hb => Bool.eq_false_iff.mp unordered
      (happensBefore_to_source p covers hb)), ?_⟩
  intro mixed
  rw [p.event_eq i, p.event_eq j]
  exact mode mixed

theorem racePair_to_source (keeps : p.KeepsCrossThreadEdges profile)
    {i j : Fin ys.length} (race : racePair profile ys i j = true) :
    racePair profile xs (p.index i) (p.index j) = true := by
  obtain ⟨lt, conflict, unordered, mode⟩ := racePair_iff.mp race
  refine racePair_iff.mpr ⟨p.mono lt, (conflicts_eq p i j).symm.trans conflict,
    Bool.eq_false_iff.mpr (fun hb => Bool.eq_false_iff.mp unordered
      (happensBefore_to_observed p keeps hb)), ?_⟩
  intro mixed
  rw [← p.event_eq i, ← p.event_eq j]
  exact mode mixed

theorem hasRace_to_source (keeps : p.KeepsCrossThreadEdges profile)
    (race : hasRace profile ys = true) : hasRace profile xs = true := by
  obtain ⟨i, j, lt, bound, pair⟩ := hasRace_iff.mp race
  let a : Fin ys.length := ⟨i, lt.trans bound⟩
  let b : Fin ys.length := ⟨j, bound⟩
  exact hasRace_iff.mpr ⟨p.index a, p.index b, p.mono (show a < b from lt), (p.index b).isLt,
    racePair_to_source p keeps (i := a) (j := b) pair⟩

theorem hasRace_to_observed (covers : profile = .mixed → p.CoversOverwrites)
    (conflictsCovered : p.CoversConflicts) (race : hasRace profile xs = true) :
    hasRace profile ys = true := by
  obtain ⟨i, j, lt, bound, pair⟩ := hasRace_iff.mp race
  let a : Fin xs.length := ⟨i, lt.trans bound⟩
  let b : Fin xs.length := ⟨j, bound⟩
  have conflict := (racePair_iff.mp (show racePair profile xs a b = true from pair)).2.1
  obtain ⟨⟨a', eqA⟩, ⟨b', eqB⟩⟩ := conflictsCovered a b lt conflict
  have ordered : p.index a' < p.index b' := by rwa [eqA, eqB]
  refine hasRace_iff.mpr ⟨a', b', (index_lt_iff p).mp ordered, b'.isLt,
    racePair_to_observed p covers ?_⟩
  rwa [eqA, eqB]

theorem classify_eq (keeps : p.KeepsCrossThreadEdges profile)
    (covers : profile = .mixed → p.CoversOverwrites) (conflictsCovered : p.CoversConflicts) :
    classify profile ys = classify profile xs := by
  unfold classify
  rw [show hasRace profile ys = hasRace profile xs from Bool.eq_iff_iff.mpr
    ⟨hasRace_to_source p keeps, hasRace_to_observed p covers conflictsCovered⟩]

end Silmaril.Proofs.Semantics.TrackA.Concurrency.Projection
