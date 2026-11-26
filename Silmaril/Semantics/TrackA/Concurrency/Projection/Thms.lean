module

public import Silmaril.Semantics.TrackA.Concurrency.Projection.Defs
import Silmaril.Proofs.Semantics.TrackA.Concurrency.Projection

public section

namespace Silmaril.Semantics.TrackA.Concurrency

variable {T L R : Type} {xs ys : List (Event T L R)}

namespace Interface

theorem observe_inter (outer inner : Interface L R) (xs : List (Event T L R)) :
    (outer.inter inner).observe xs = inner.observe (outer.observe xs) :=
  Proofs.Semantics.TrackA.Concurrency.Projection.observe_inter outer inner xs

theorem retains_iff (view : Interface L R) (k : Fin xs.length) :
    (view.projection xs).Retains k ↔ view.exposes xs[k.val].action = true :=
  Proofs.Semantics.TrackA.Concurrency.Projection.interface_retains_iff view k

variable [DecidableEq T] [DecidableEq L] [DecidableEq R] {profile : RaceProfile}

/-- Factoring the observation keeps the same source execution and endpoints. -/
theorem observedRun_inter (outer inner : Interface L R) {start finish : Config T L R} :
    (outer.inter inner).ObservedRun start ys finish ↔
      ∃ mid, outer.ObservedRun start mid finish ∧ inner.observe mid = ys :=
  Proofs.Semantics.TrackA.Concurrency.Projection.observedRun_inter outer inner

theorem keepsCrossThreadEdges (view : Interface L R)
    (sync : view.CoversSynchronization profile xs) :
    (view.projection xs).KeepsCrossThreadEdges profile :=
  Proofs.Semantics.TrackA.Concurrency.Projection.interface_keepsCrossThreadEdges view sync

omit [DecidableEq T] [DecidableEq L] in
theorem coversOverwrites (view : Interface L R)
    (sync : view.CoversSynchronization .mixed xs) :
    (view.projection xs).CoversOverwrites :=
  Proofs.Semantics.TrackA.Concurrency.Projection.interface_coversOverwrites view sync

end Interface

namespace Projection

variable [DecidableEq T] [DecidableEq L] [DecidableEq R]
variable (p : Projection xs ys) {profile : RaceProfile} {i j : Fin ys.length}

omit [DecidableEq L] in
theorem conflicts_eq (i j : Fin ys.length) :
    conflicts ys[i.val] ys[j.val] = conflicts xs[(p.index i).val] xs[(p.index j).val] :=
  Proofs.Semantics.TrackA.Concurrency.Projection.conflicts_eq p i j

omit [DecidableEq T] [DecidableEq L] in
/-- Compare the raw `atomicSync` Boolean on retained action labels under
overwrite coverage. Interpret `true` as reads-from only for a write and
read in index order (`i < j`) in a generated SC history. -/
theorem atomicSync_eq (covers : p.CoversOverwrites) (i j : Fin ys.length) :
    atomicSync ys i j ys[i.val].action ys[j.val].action =
      atomicSync xs (p.index i) (p.index j) xs[(p.index i).val].action xs[(p.index j).val].action :=
  Proofs.Semantics.TrackA.Concurrency.Projection.atomicSync_eq p covers i j

theorem direct_eq (covers : profile = .mixed → p.CoversOverwrites) (i j : Fin ys.length) :
    direct profile ys i j = direct profile xs (p.index i) (p.index j) :=
  Proofs.Semantics.TrackA.Concurrency.Projection.direct_eq p covers i j

/-- Every observed path lifts to the source if mixed-profile reads-from cannot
gain edges through hidden overwrites. -/
theorem happensBefore_to_source (covers : profile = .mixed → p.CoversOverwrites)
    (hb : happensBefore profile ys i j = true) :
    happensBefore profile xs (p.index i) (p.index j) = true :=
  Proofs.Semantics.TrackA.Concurrency.Projection.happensBefore_to_source p covers hb

/-- Retain cross-thread direct edges and compress the same-thread stretches
of a source path through hidden occurrences. -/
theorem happensBefore_to_observed (keeps : p.KeepsCrossThreadEdges profile)
    (hb : happensBefore profile xs (p.index i) (p.index j) = true) :
    happensBefore profile ys i j = true :=
  Proofs.Semantics.TrackA.Concurrency.Projection.happensBefore_to_observed p keeps hb

theorem happensBefore_eq (keeps : p.KeepsCrossThreadEdges profile)
    (covers : profile = .mixed → p.CoversOverwrites) :
    happensBefore profile ys i j = happensBefore profile xs (p.index i) (p.index j) :=
  Bool.eq_iff_iff.mpr ⟨p.happensBefore_to_source covers, p.happensBefore_to_observed keeps⟩

/-- Source races on a retained pair remain races if projection adds no
happens-before between those endpoints. -/
theorem racePair_to_observed (covers : profile = .mixed → p.CoversOverwrites)
    (race : racePair profile xs (p.index i) (p.index j) = true) :
    racePair profile ys i j = true :=
  Proofs.Semantics.TrackA.Concurrency.Projection.racePair_to_observed p covers race

/-- Observed races reflect source races when source happens-before survives. -/
theorem racePair_to_source (keeps : p.KeepsCrossThreadEdges profile)
    (race : racePair profile ys i j = true) :
    racePair profile xs (p.index i) (p.index j) = true :=
  Proofs.Semantics.TrackA.Concurrency.Projection.racePair_to_source p keeps race

theorem racePair_eq (keeps : p.KeepsCrossThreadEdges profile)
    (covers : profile = .mixed → p.CoversOverwrites) :
    racePair profile ys i j = racePair profile xs (p.index i) (p.index j) :=
  Bool.eq_iff_iff.mpr ⟨p.racePair_to_source keeps, p.racePair_to_observed covers⟩

theorem hasRace_to_source (keeps : p.KeepsCrossThreadEdges profile)
    (race : hasRace profile ys = true) : hasRace profile xs = true :=
  Proofs.Semantics.TrackA.Concurrency.Projection.hasRace_to_source p keeps race

theorem hasRace_to_observed (covers : profile = .mixed → p.CoversOverwrites)
    (conflictsCovered : p.CoversConflicts) (race : hasRace profile xs = true) :
    hasRace profile ys = true :=
  Proofs.Semantics.TrackA.Concurrency.Projection.hasRace_to_observed p covers conflictsCovered race

/-- Whole-trace classification agrees with additional coverage of conflict
endpoints, which can disappear even if all retained pairs agree. -/
theorem classify_eq (keeps : p.KeepsCrossThreadEdges profile)
    (covers : profile = .mixed → p.CoversOverwrites) (conflictsCovered : p.CoversConflicts) :
    classify profile ys = classify profile xs :=
  Proofs.Semantics.TrackA.Concurrency.Projection.classify_eq p keeps covers conflictsCovered

end Projection

/-- Exposing mutexes and the mixed profile's atomic resources suffices for
exact race classification of each retained pair, including across hidden
plain accesses. -/
theorem Interface.racePair_eq [DecidableEq T] [DecidableEq L] [DecidableEq R]
    (view : Interface L R) {profile : RaceProfile} (sync : view.CoversSynchronization profile xs)
    (i j : Fin (view.observe xs).length) :
    racePair profile (view.observe xs) i j =
      racePair profile xs ((view.projection xs).index i) ((view.projection xs).index j) :=
  (view.projection xs).racePair_eq (view.keepsCrossThreadEdges sync)
    (fun mixed => view.coversOverwrites (mixed ▸ sync))

end Silmaril.Semantics.TrackA.Concurrency
