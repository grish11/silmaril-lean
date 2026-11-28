module

public import Silmaril.Semantics.ReadWrite.Observations.Defs
import Silmaril.Semantics.ReadWrite.Thms

public section
namespace Silmaril.Proofs.Semantics.ReadWrite.Observations

open Silmaril.Semantics.ReadWrite

universe u v w
variable {Address : Type u} {Value : Type v} {State : Type w}
variable {trace gap : Trace Address Value} {address : Address}
variable {earlier later : Value} {access : Access Address Value State} {initial final : State}

theorem lastWrite_eq_none_iff [DecidableEq Address] :
    trace.lastWrite address = none ↔ ¬ trace.Defs address := by
  induction trace with
  | nil => simp [Trace.lastWrite, Trace.Defs, Trace.writes]
  | cons event rest ih =>
    cases event with
    | read => exact ih
    | write p value =>
      have single : Trace.Defs [Event.write p value] address ↔ p = address := by
        simp [Trace.Defs, Trace.writes, eq_comm]
      rw [show Event.write p value :: rest = [Event.write p value] ++ rest from rfl,
        Trace.defs_append, not_or, single]
      cases found : Trace.lastWrite rest address with
      | none =>
        have outside := ih.mp found
        by_cases eq : p = address <;>
          simp [Trace.lastWrite, found, eq, outside]
      | some value' =>
        have inside : ¬ ¬ Trace.Defs rest address := fun outside => by
          have impossible := found.symm.trans (ih.mpr outside)
          cases impossible
        simp [Trace.lastWrite, found, Option.or, inside]

theorem lastWrite_append [DecidableEq Address] (first last : Trace Address Value) :
    Trace.lastWrite (first ++ last) address = (last.lastWrite address).or (first.lastWrite address) := by
  induction first with
  | nil => simp [Trace.lastWrite, Option.or_eq_left_of_none]
  | cons event rest ih =>
    cases event with
    | read => exact ih
    | write p value =>
      simp only [List.cons_append, Trace.lastWrite, ih, Option.or_assoc]

theorem lastWrite_eq_some_iff [DecidableEq Address] {value : Value} :
    trace.lastWrite address = some value ↔
      ∃ (pre post : Trace Address Value),
        trace = pre ++ .write address value :: post ∧ ¬ post.Defs address := by
  constructor
  · intro found
    induction trace with
    | nil => contradiction
    | cons event rest ih =>
      cases event with
      | read p observed =>
        obtain ⟨pre, post, rfl, outside⟩ := ih found
        exact ⟨.read p observed :: pre, post, rfl, outside⟩
      | write p written =>
        change (Trace.lastWrite rest address).or (if p = address then some written else none) =
          some value at found
        rcases Option.or_eq_some_iff.mp found with tail | ⟨noTail, head⟩
        · obtain ⟨pre, post, rfl, outside⟩ := ih tail
          exact ⟨.write p written :: pre, post, rfl, outside⟩
        · by_cases eq : p = address
          · subst p
            have writtenEq : written = value := by simpa using head
            subst written
            exact ⟨[], rest, rfl, lastWrite_eq_none_iff.mp noTail⟩
          · simp [eq] at head
  · rintro ⟨pre, post, rfl, outside⟩
    rw [lastWrite_append pre (.write address value :: post)]
    simp [Trace.lastWrite, lastWrite_eq_none_iff.mpr outside, Option.or]

/-- Isolate the next read of the address in a suffix known to read it. -/
private theorem split_first_read (reads : trace.Reads address) :
    ∃ (before : Trace Address Value) (value : Value) (after : Trace Address Value),
      trace = before ++ .read address value :: after ∧ ¬ before.Reads address := by
  induction trace with
  | nil => simp [Trace.Reads, Trace.reads] at reads
  | cons event rest ih =>
    cases event with
    | read p value =>
      by_cases eq : p = address
      · subst p
        exact ⟨[], value, rest, rfl, by simp [Trace.Reads, Trace.reads]⟩
      · have readsRest : Trace.Reads rest address := by
          change ∃ observed, (address, observed) ∈ (p, value) :: Trace.reads rest at reads
          simpa [Trace.Reads, Ne.symm eq] using reads
        obtain ⟨before, next, after, rfl, noRead⟩ := ih readsRest
        refine ⟨.read p value :: before, next, after, rfl, ?_⟩
        change ¬ ∃ observed, (address, observed) ∈ (p, value) :: before.reads
        simpa [Trace.Reads, Ne.symm eq] using noRead
    | write p value =>
      obtain ⟨before, next, after, rfl, noRead⟩ := ih reads
      exact ⟨.write p value :: before, next, after, rfl, noRead⟩

private theorem mem_reads_iff {value : Value} :
    (address, value) ∈ trace.reads ↔ ∃ pre post, trace = pre ++ .read address value :: post := by
  rw [Trace.reads, List.mem_filterMap, ← List.mem_iff_append]
  constructor
  · rintro ⟨event, member, observed⟩
    cases event with
    | read p v =>
      simp only [Option.some.injEq, Prod.mk.injEq] at observed
      obtain ⟨rfl, rfl⟩ := observed
      exact member
    | write p v => contradiction
  · intro member
    exact ⟨.read address value, member, rfl⟩

theorem consecutiveReads_members (pair : trace.ConsecutiveReads address earlier gap later) :
    (address, earlier) ∈ trace.reads ∧ (address, later) ∈ trace.reads := by
  obtain ⟨pre, post, rfl, _⟩ := pair
  exact ⟨mem_reads_iff.mpr ⟨pre, _, rfl⟩,
    mem_reads_iff.mpr ⟨pre ++ .read address earlier :: gap, post, by simp [List.append_assoc]⟩⟩

theorem repeatedReadAddresses_iff :
    trace.RepeatedReadAddresses address ↔
      ∃ pre earlier gap later post,
        trace = pre ++ .read address earlier :: (gap ++ .read address later :: post) := by
  constructor
  · rintro ⟨earlier, gap, later, pre, post, eq, _⟩
    exact ⟨pre, earlier, gap, later, post, eq⟩
  · rintro ⟨pre, earlier, gap, later, post, rfl⟩
    have reads : Trace.Reads (gap ++ .read address later :: post) address :=
      ⟨later, mem_reads_iff.mpr ⟨gap, post, rfl⟩⟩
    obtain ⟨before, next, after, eq, noRead⟩ := split_first_read reads
    exact ⟨earlier, before, next, pre, after, by rw [eq], noRead⟩

theorem stableWithoutWrites_iff_change_has_write :
    trace.ReadsStableWithoutWrites address ↔
      ∀ ⦃earlier gap later⦄, trace.ConsecutiveReads address earlier gap later →
        later ≠ earlier → gap.Defs address := by
  classical
  constructor
  · exact fun stable _ _ _ pair changed => by
      exact Classical.byContradiction (fun outside => changed (stable pair outside))
  · exact fun hasWrite _ _ _ pair outside => by
      exact Classical.byContradiction (fun different => outside (hasWrite pair different))

theorem repeated_partition :
    trace.RepeatedReadAddresses address ↔
      trace.StableReadAddresses address ∨ trace.ChangedReadAddresses address := by
  classical
  constructor
  · intro repeats
    by_cases stable : trace.ReadsStable address
    · exact .inl ⟨repeats, stable⟩
    · right
      unfold Trace.ReadsStable at stable
      simp only [Classical.not_forall] at stable
      obtain ⟨earlier, gap, later, pair, changed⟩ := stable
      exact ⟨earlier, gap, later, pair, changed⟩
  · rintro (⟨repeats, _⟩ | ⟨earlier, gap, later, pair, _⟩)
    · exact repeats
    · exact ⟨earlier, gap, later, pair⟩

theorem lastWrite_compatible_change_iff [DecidableEq Address]
    (expected : later = (gap.lastWrite address).getD earlier) :
    later ≠ earlier ↔ ∃ value, gap.lastWrite address = some value ∧ value ≠ earlier := by
  cases found : gap.lastWrite address <;> simp_all

theorem replays_read_eq [DecidableEq Address] (run : trace.Replays access initial final)
    (locality : access.Frames access.read) (readAfterWrite : access.ReadsAfterWrite)
    (read : access.read final address = some later) :
    (trace.lastWrite address).or (access.read initial address) = some later := by
  induction trace generalizing initial with
  | nil =>
    have eq : initial = final := run
    exact eq ▸ read
  | cons event rest ih =>
    cases event with
    | read p value => exact ih run.2
    | write p value =>
      obtain ⟨next, step, tail⟩ := run
      cases found : Trace.lastWrite rest address with
      | some written =>
        simpa [Trace.lastWrite, found, Option.or] using ih tail
      | none =>
        have nextRead := (tail.frame locality (lastWrite_eq_none_iff.mp found)).symm.trans read
        by_cases eq : p = address
        · subst p
          have valueEq := readAfterWrite step nextRead
          simp [Trace.lastWrite, found, Option.or, valueEq]
        · simpa [Trace.lastWrite, found, Option.or, eq] using (locality step (Ne.symm eq)).symm.trans nextRead

theorem replays_stableWithoutWrites (run : trace.Replays access initial final)
    (locality : access.Frames access.read) : trace.ReadsStableWithoutWrites address := by
  rintro earlier gap later ⟨pre, post, rfl, _⟩ outside
  obtain ⟨before, _, earlierRead, rest⟩ := (Trace.replays_append (first := pre)).mp run
  obtain ⟨after, gapRun, laterRead, _⟩ := (Trace.replays_append (first := gap)).mp rest
  exact Option.some.inj (laterRead.symm.trans ((gapRun.frame locality outside).trans earlierRead))

theorem replays_match_lastWrite [DecidableEq Address] (run : trace.Replays access initial final)
    (locality : access.Frames access.read) (readAfterWrite : access.ReadsAfterWrite) :
    trace.ReadsMatchLastWrite address := by
  rintro earlier gap later ⟨pre, post, rfl, _⟩
  obtain ⟨before, _, earlierRead, rest⟩ := (Trace.replays_append (first := pre)).mp run
  obtain ⟨after, gapRun, laterRead, _⟩ := (Trace.replays_append (first := gap)).mp rest
  have expected := replays_read_eq gapRun locality readAfterWrite laterRead
  rw [earlierRead] at expected
  cases found : gap.lastWrite address <;> simp_all [Option.or]

/-- When writes are erased, only reads preceded by a relevant write
need an additional check against the original snapshot. -/
theorem replays_reads_agree_iff [DecidableEq Address] (run : trace.Replays access initial final)
    (locality : access.Frames access.read) (readAfterWrite : access.ReadsAfterWrite) :
    trace.reads.Agrees access initial ↔
      ∀ ⦃pre post : Trace Address Value⦄ ⦃p observed written⦄,
        trace = pre ++ .read p observed :: post →
        pre.lastWrite p = some written → access.read initial p = some written := by
  constructor
  · intro agrees pre post p observed written eq found
    have observedInitially := agrees (p, observed) (mem_reads_iff.mpr ⟨pre, post, eq⟩)
    subst trace
    obtain ⟨middle, prefixRun, observedAtRead, _⟩ := (Trace.replays_append (first := pre)).mp run
    have expected := replays_read_eq prefixRun locality readAfterWrite observedAtRead
    simp only [found, Option.or, Option.some.injEq] at expected
    exact expected ▸ observedInitially
  · rintro agrees ⟨p, observed⟩ member
    obtain ⟨pre, post, eq⟩ := mem_reads_iff.mp member
    have validation := (Trace.replays_append (first := pre)).mp (eq ▸ run)
    obtain ⟨middle, prefixRun, observedAtRead, _⟩ := validation
    have expected := replays_read_eq prefixRun locality readAfterWrite observedAtRead
    cases found : Trace.lastWrite pre p with
    | none => simpa [found, Option.or] using expected
    | some written =>
      simp only [found, Option.or, Option.some.injEq] at expected
      exact expected ▸ agrees eq found

end Silmaril.Proofs.Semantics.ReadWrite.Observations
