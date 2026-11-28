module

public import Silmaril.Semantics.ReadWrite.Observations.Defs
public import Silmaril.Semantics.ReadWrite.Thms
import Silmaril.Proofs.Semantics.ReadWrite.Observations.Laws

public section
namespace Silmaril.Semantics.ReadWrite.Trace

universe u v w
variable {Address : Type u} {Value : Type v} {State : Type w}
variable {trace gap : Trace Address Value} {address : Address}
variable {earlier later : Value} {access : Access Address Value State} {initial final : State}

theorem lastWrite_eq_none_iff [DecidableEq Address] :
    trace.lastWrite address = none ↔ ¬ trace.Defs address :=
  Proofs.Semantics.ReadWrite.Observations.lastWrite_eq_none_iff

theorem lastWrite_append [DecidableEq Address] (first last : Trace Address Value) :
    Trace.lastWrite (first ++ last) address = (last.lastWrite address).or (first.lastWrite address) :=
  Proofs.Semantics.ReadWrite.Observations.lastWrite_append first last

theorem lastWrite_eq_some_iff [DecidableEq Address] {value : Value} :
    trace.lastWrite address = some value ↔
      ∃ (pre post : Trace Address Value),
        trace = pre ++ .write address value :: post ∧ ¬ post.Defs address :=
  Proofs.Semantics.ReadWrite.Observations.lastWrite_eq_some_iff

theorem ConsecutiveReads.members (pair : trace.ConsecutiveReads address earlier gap later) :
    (address, earlier) ∈ trace.reads ∧ (address, later) ∈ trace.reads :=
  Proofs.Semantics.ReadWrite.Observations.consecutiveReads_members pair

/-- Any two read occurrences at the address suffice, even if other reads intervene. -/
theorem repeatedReadAddresses_iff :
    trace.RepeatedReadAddresses address ↔
      ∃ pre earlier gap later post,
        trace = pre ++ .read address earlier :: (gap ++ .read address later :: post) :=
  Proofs.Semantics.ReadWrite.Observations.repeatedReadAddresses_iff

theorem ReadsStable.withoutWrites (stable : trace.ReadsStable address) :
    trace.ReadsStableWithoutWrites address :=
  fun _ _ _ pair _ => stable pair

theorem ReadsMatchLastWrite.withoutWrites [DecidableEq Address]
    (compatible : trace.ReadsMatchLastWrite address) :
    trace.ReadsStableWithoutWrites address := by
  intro earlier gap later pair outside
  simpa [lastWrite_eq_none_iff.mpr outside] using compatible pair

theorem stableReadAddresses_subset_stableWithoutWrites :
    trace.StableReadAddresses address → trace.StableWithoutWritesAddresses address :=
  fun ⟨repeats, stable⟩ => ⟨repeats, stable.withoutWrites⟩

theorem lastWriteCompatibleAddresses_subset_stableWithoutWrites [DecidableEq Address] :
    trace.LastWriteCompatibleAddresses address → trace.StableWithoutWritesAddresses address :=
  fun ⟨repeats, compatible⟩ => ⟨repeats, compatible.withoutWrites⟩

/-- The permissive change rule and equality across write-free gaps are equivalent. -/
theorem stableWithoutWrites_iff_change_has_write :
    trace.ReadsStableWithoutWrites address ↔
      ∀ ⦃earlier gap later⦄, trace.ConsecutiveReads address earlier gap later →
        later ≠ earlier → gap.Defs address :=
  Proofs.Semantics.ReadWrite.Observations.stableWithoutWrites_iff_change_has_write

theorem repeated_partition :
    trace.RepeatedReadAddresses address ↔
      trace.StableReadAddresses address ∨ trace.ChangedReadAddresses address :=
  Proofs.Semantics.ReadWrite.Observations.repeated_partition

theorem stable_disjoint_changed (stable : trace.StableReadAddresses address) :
    ¬ trace.ChangedReadAddresses address :=
  fun ⟨_, _, _, pair, different⟩ => different (stable.2 pair)

/-- With a compatible pair, a change occurs exactly when its last write
assigned a value different from the earlier read. -/
theorem lastWrite_compatible_change_iff [DecidableEq Address]
    (expected : later = (gap.lastWrite address).getD earlier) :
    later ≠ earlier ↔ ∃ value, gap.lastWrite address = some value ∧ value ≠ earlier :=
  Proofs.Semantics.ReadWrite.Observations.lastWrite_compatible_change_iff expected

/-- Given a successful final read, its value is supplied by the last relevant
write if present, and by the initial state otherwise. -/
theorem Replays.read_eq [DecidableEq Address] (run : trace.Replays access initial final)
    (locality : access.Frames access.read) (readAfterWrite : access.ReadsAfterWrite)
    (read : access.read final address = some later) :
    (trace.lastWrite address).or (access.read initial address) = some later :=
  Proofs.Semantics.ReadWrite.Observations.replays_read_eq run locality readAfterWrite read

theorem Replays.stableWithoutWrites (run : trace.Replays access initial final)
    (locality : access.Frames access.read) : trace.ReadsStableWithoutWrites address :=
  Proofs.Semantics.ReadWrite.Observations.replays_stableWithoutWrites run locality

theorem Replays.matchLastWrite [DecidableEq Address] (run : trace.Replays access initial final)
    (locality : access.Frames access.read) (readAfterWrite : access.ReadsAfterWrite) :
    trace.ReadsMatchLastWrite address :=
  Proofs.Semantics.ReadWrite.Observations.replays_match_lastWrite run locality readAfterWrite

theorem Replays.lastWriteCompatibleAddresses_iff [DecidableEq Address]
    (run : trace.Replays access initial final) (locality : access.Frames access.read)
    (readAfterWrite : access.ReadsAfterWrite) :
    trace.LastWriteCompatibleAddresses address ↔ trace.RepeatedReadAddresses address :=
  ⟨And.left, fun repeats => ⟨repeats, run.matchLastWrite locality readAfterWrite⟩⟩

/-- An exact criterion for replaying the read projection on the original state
after a successful mixed replay. Each checked prefix ends just before its read. -/
theorem Replays.reads_agree_iff [DecidableEq Address] (run : trace.Replays access initial final)
    (locality : access.Frames access.read) (readAfterWrite : access.ReadsAfterWrite) :
    trace.reads.Agrees access initial ↔
      ∀ ⦃pre post : Trace Address Value⦄ ⦃p observed written⦄,
        trace = pre ++ .read p observed :: post →
        pre.lastWrite p = some written → access.read initial p = some written :=
  Proofs.Semantics.ReadWrite.Observations.replays_reads_agree_iff run locality readAfterWrite

end Silmaril.Semantics.ReadWrite.Trace
