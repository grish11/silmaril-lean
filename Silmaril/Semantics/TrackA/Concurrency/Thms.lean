module

public import Silmaril.Semantics.TrackA.Concurrency.Race
import Silmaril.Proofs.Semantics.TrackA.Concurrency.Machine
import Silmaril.Proofs.Semantics.TrackA.Concurrency.Races

@[expose] public section

namespace Silmaril.Semantics.TrackA.Concurrency

variable {T L R : Type} [DecidableEq T] [DecidableEq L] [DecidableEq R]

theorem replay_iff {threads : List T} {s t : Config T L R} {xs : List (Event T L R)} :
    replay s threads = some (xs, t) ↔ sc.MTr s xs t ∧ xs.map Event.thread = threads :=
  Proofs.Semantics.TrackA.Concurrency.replay_iff

theorem single_run_iff {s t : Local Unit L R} {xs : List (Event Unit L R)} :
    sc.MTr (Config.single s) xs (Config.single t) ↔ (sequential ()).MTr s xs t :=
  Proofs.Semantics.TrackA.Concurrency.single_run_iff

omit [DecidableEq T] [DecidableEq L] [DecidableEq R] in
theorem held_exclusive {s : Config T L R} {t u : T} {l : L}
    (ht : s.Held t l) (hu : s.Held u l) : t = u :=
  Option.some.inj (ht.symm.trans hu)

theorem waiting_iff_disabled {s : Config T L R} {t : T} {l : L} {next : Program L R}
    (head : s.code t = .acquire l next) :
    s.Waiting t l ↔ s.stepFor t = none :=
  Proofs.Semantics.TrackA.Concurrency.waiting_iff_disabled head

theorem acquire_iff {t : T} {l : L} {next : Program L R} {shared : Shared T L R}
    {e : Event T L R} {s' : Local T L R} :
    (sequential t).Tr (.acquire l next, shared) e s' ↔
      shared.owner l = none ∧ e = ⟨t, .acquire l⟩ ∧
        s' = (next, { shared with owner := Function.update shared.owner l (some t) }) :=
  Proofs.Semantics.TrackA.Concurrency.acquire_iff

theorem release_iff {t : T} {l : L} {next : Program L R} {shared : Shared T L R}
    {e : Event T L R} {s' : Local T L R} :
    (sequential t).Tr (.release l next, shared) e s' ↔
      shared.owner l = some t ∧ e = ⟨t, .release l⟩ ∧
        s' = (next, { shared with owner := Function.update shared.owner l none }) :=
  Proofs.Semantics.TrackA.Concurrency.release_iff

theorem successors_correct (threads : List T) (covers : ∀ t, t ∈ threads)
    (s : Config T L R) (e : Event T L R) (t : Config T L R) :
    (e, t) ∈ successors threads s ↔ sc.Tr s e t :=
  Proofs.Semantics.TrackA.Concurrency.successors_correct threads covers s e t

def enumerator (threads : List T) (covers : ∀ t, t ∈ threads) :
    Operational.Enumerator (sc (T := T) (L := L) (R := R)) :=
  ⟨successors threads, successors_correct threads covers⟩

variable {profile : RaceProfile} {xs ys : List (Event T L R)} {i j : Nat}

theorem happensBefore_iff_transGen :
    happensBefore profile xs i j = true ↔
      Relation.TransGen (fun a b => direct profile xs a b = true) i j :=
  Proofs.Semantics.TrackA.Concurrency.happensBefore_iff_transGen

theorem happensBefore_lt (hb : happensBefore profile xs i j = true) : i < j :=
  Proofs.Semantics.TrackA.Concurrency.happensBefore_lt hb

/-- Future events do not alter happens-before between occurrences in a prefix. -/
theorem happensBefore_append (bound : j < xs.length) :
    happensBefore profile (xs ++ ys) i j = happensBefore profile xs i j :=
  Proofs.Semantics.TrackA.Concurrency.happensBefore_append bound

theorem hasRace_iff :
    hasRace profile xs = true ↔ ∃ i j, i < j ∧ j < xs.length ∧ racePair profile xs i j = true :=
  Proofs.Semantics.TrackA.Concurrency.hasRace_iff

theorem hasRace_append (race : hasRace profile xs = true) :
    hasRace profile (xs ++ ys) = true :=
  Proofs.Semantics.TrackA.Concurrency.hasRace_append race

theorem happensBefore_mixed (hb : happensBefore .mutexOnly xs i j = true) :
    happensBefore .mixed xs i j = true :=
  Proofs.Semantics.TrackA.Concurrency.happensBefore_mixed hb

theorem hasRace_mutexOnly_of_mixed (race : hasRace .mixed xs = true) :
    hasRace .mutexOnly xs = true :=
  Proofs.Semantics.TrackA.Concurrency.hasRace_mutexOnly_of_mixed race

variable {start finish : Config T L R}

theorem guarded_iff :
    GuardedRun profile start xs finish ↔ sc.MTr start xs finish ∧ RaceFree profile xs :=
  Proofs.Semantics.TrackA.Concurrency.guarded_iff

/-- Same ordinary executions, with identical event histories and endpoints. -/
theorem guarded_iff_filtered :
    GuardedRun profile start xs finish ↔ FilteredRun profile start xs finish :=
  Proofs.Semantics.TrackA.Concurrency.guarded_iff_filtered

theorem raceUB_has_raw_run (ub : RaceUB profile start xs) :
    ∃ finish, ClassifiedRun profile start xs finish .racy :=
  Proofs.Semantics.TrackA.Concurrency.raceUB_has_raw_run ub

theorem racy_run_has_ub_prefix (run : sc.MTr start xs finish) (race : hasRace profile xs = true) :
    ∃ prior tail, xs = prior ++ tail ∧ RaceUB profile start prior :=
  Proofs.Semantics.TrackA.Concurrency.racy_run_has_ub_prefix run race

/-- Program safety quantifies over every finite execution, including
unfinished prefixes and schedules dropped by the filter. -/
theorem raceSafe_iff :
    RaceSafe profile start ↔ ∀ xs finish, sc.MTr start xs finish → RaceFree profile xs :=
  Proofs.Semantics.TrackA.Concurrency.raceSafe_iff

theorem raceSafe_mixed_of_mutexOnly (safe : RaceSafe .mutexOnly start) : RaceSafe .mixed start :=
  raceSafe_iff.mpr fun events last run => Bool.eq_false_iff.mpr fun bad =>
    Bool.eq_false_iff.mp (raceSafe_iff.mp safe events last run) (hasRace_mutexOnly_of_mixed bad)

end Silmaril.Semantics.TrackA.Concurrency
