module

public import Silmaril.Process.ITreeTrace.SharedStore.Defs
public import Silmaril.Semantics.Brookes.Parallel.Thms
public import Silmaril.Semantics.Brookes.TreeSC.Closed.Thms
public import Silmaril.Semantics.TrackA.Concurrency.Thms
import Silmaril.Proofs.Process.ITreeTrace.SharedStore.Parallel
import Silmaril.Proofs.Process.ITreeTrace.SharedStore.Replay

public section

namespace Silmaril.Process.ITreeTrace.SharedStore

open Silmaril.Semantics.Brookes.TreeSC (Code Store)
open Silmaril.Semantics.TrackA
open Concurrency (Config replay sc)

variable {T R : Type} [DecidableEq T] [DecidableEq R]

/-- A completed process schedule replays in SC using exactly its event thread
IDs. This drops skipped returned threads and the unused schedule suffix. -/
theorem replay_of_completes {schedule : List T} {code : T → Code R} {before after : Store R}
    {events : List (Concurrency.Event T Empty R)} (run : Completes schedule code before events after) :
    (events.map Concurrency.Event.thread).Sublist schedule ∧
      replay (Config.initial code before) (events.map Concurrency.Event.thread) =
        some (events, Config.initial (fun _ => .done) after) :=
  Proofs.Process.ITreeTrace.SharedStore.sound run

/-- Each successful SC schedule to done is itself a process schedule to return. -/
theorem completes_of_replay {schedule : List T} {code : T → Code R} {before after : Store R}
    {events : List (Concurrency.Event T Empty R)}
    (run : replay (Config.initial code before) schedule =
      some (events, Config.initial (fun _ => .done) after)) :
    Completes schedule code before events after :=
  Proofs.Process.ITreeTrace.SharedStore.complete run

/-- Closed completed interleavings agree at the level of full SC event words
and store endpoints. The reverse direction supplies the event-thread schedule. -/
theorem completes_iff_sc {code : T → Code R} {before after : Store R}
    {events : List (Concurrency.Event T Empty R)} :
    (∃ schedule, Completes schedule code before events after) ↔
      sc.MTr (Config.initial code before) events (Config.initial (fun _ => .done) after) :=
  Proofs.Process.ITreeTrace.SharedStore.sc_iff

/-- The singleton process and the saturated Brookes denotation have the same
closed endpoint observations, after hiding the event word and the schedule. -/
theorem singleton_completes_iff_denote {code : Code R} {before after : Store R} :
    (∃ schedule events, Completes (T := Unit) schedule (fun _ => code) before events after) ↔
      code.denote.completes before after () :=
  Proofs.Process.ITreeTrace.SharedStore.singleton_iff_denote

/-- A closed two-thread process run is a completion of the existing Brookes
parallel denotation after hiding the schedule and event word. -/
theorem parallel_completes_of_completes {schedule : List Bool} {code : Bool → Code R}
    {before after : Store R} {events : List (Concurrency.Event Bool Empty R)}
    (run : Completes schedule code before events after) :
    ((code false).denote.parallel (code true).denote).completes before after ((), ()) :=
  Proofs.Process.ITreeTrace.SharedStore.parallel_of_replay (replay_of_completes run).2

end Silmaril.Process.ITreeTrace.SharedStore
