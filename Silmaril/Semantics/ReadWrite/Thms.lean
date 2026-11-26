module

public import Silmaril.Semantics.ReadWrite.Defs
import Silmaril.Proofs.Semantics.ReadWrite.Laws

/-! Replay composition, projections and their laws. -/

public section
namespace Silmaril.Semantics.ReadWrite

universe u v w x
variable {Address : Type u} {Value : Type v} {State : Type w} {Other : Type x} {access : Access Address Value State}
variable {trace first last : Trace Address Value} {address : Address}
variable {initial middle final : State}

theorem Trace.reads_append :
    (first ++ last).reads = first.reads ++ last.reads :=
  Proofs.Semantics.ReadWrite.reads_append

theorem Trace.writes_append :
    (first ++ last).writes = first.writes ++ last.writes :=
  Proofs.Semantics.ReadWrite.writes_append

theorem ReadTrace.reads_toTrace (reads : ReadTrace Address Value) :
    reads.toTrace.reads = reads :=
  Proofs.Semantics.ReadWrite.reads_toTrace reads

theorem WriteTrace.writes_toTrace (writes : WriteTrace Address Value) :
    writes.toTrace.writes = writes :=
  Proofs.Semantics.ReadWrite.writes_toTrace writes

theorem Trace.readOnly_reads (trace : Trace Address Value) : trace.reads.toTrace.ReadOnly :=
  Proofs.Semantics.ReadWrite.readOnly_reads trace

theorem Trace.writeOnly_writes (trace : Trace Address Value) : trace.writes.toTrace.WriteOnly :=
  Proofs.Semantics.ReadWrite.writeOnly_writes trace

theorem Trace.defs_append :
    (first ++ last).Defs address ↔ first.Defs address ∨ last.Defs address :=
  Proofs.Semantics.ReadWrite.defs_append

theorem Trace.footprint_append :
    (first ++ last).Footprint address ↔ first.Footprint address ∨ last.Footprint address :=
  Proofs.Semantics.ReadWrite.footprint_append

theorem Trace.uses_append :
    (first ++ last).Uses address ↔ first.Uses address ∨ (¬ first.Defs address ∧ last.Uses address) :=
  Proofs.Semantics.ReadWrite.uses_append

theorem Trace.uses_or_defs : trace.Uses address ∨ trace.Defs address ↔ trace.Footprint address :=
  Proofs.Semantics.ReadWrite.uses_or_defs

theorem Trace.replays_append :
    (first ++ last).Replays access initial final ↔
      ∃ middle, first.Replays access initial middle ∧ last.Replays access middle final :=
  Proofs.Semantics.ReadWrite.replays_append

theorem Trace.run_eq_some_iff [DecidableEq Value] :
    trace.run access initial = some final ↔ trace.Replays access initial final :=
  Proofs.Semantics.ReadWrite.run_eq_some_iff

theorem Trace.run_eq_none_iff [DecidableEq Value] :
    trace.run access initial = none ↔ ¬ trace.Consistent access initial := by
  simp only [Trace.Consistent, ← Trace.run_eq_some_iff]
  cases trace.run access initial <;> simp

theorem Trace.Replays.unique (left : trace.Replays access initial middle)
    (right : trace.Replays access initial final) : middle = final :=
  Proofs.Semantics.ReadWrite.replays_unique left right

theorem Trace.replays_map {other : Access Address Value Other} (f : State → Other)
    (read : ∀ m p, other.read (f m) p = access.read m p)
    (write : ∀ m p v, other.write (f m) p v = (access.write m p v).map f)
    {target : Other} :
    trace.Replays other (f initial) target ↔
      ∃ final, trace.Replays access initial final ∧ f final = target :=
  Proofs.Semantics.ReadWrite.replays_map f read write

theorem Trace.run_map [DecidableEq Value] {other : Access Address Value Other} (f : State → Other)
    (read : ∀ m p, other.read (f m) p = access.read m p)
    (write : ∀ m p v, other.write (f m) p v = (access.write m p v).map f) :
    trace.run other (f initial) = (trace.run access initial).map f :=
  Proofs.Semantics.ReadWrite.run_map f read write

theorem ReadTrace.replays_iff (reads : ReadTrace Address Value) :
    reads.toTrace.Replays access initial final ↔ initial = final ∧ reads.Agrees access initial :=
  Proofs.Semantics.ReadWrite.replays_readTrace reads

theorem Trace.Replays.writes (run : trace.Replays access initial final) :
    trace.writes.toTrace.Replays access initial final :=
  Proofs.Semantics.ReadWrite.replays_writes run

/-- Replay preserves observations at addresses outside its write set,
provided each backend write obeys the same frame law. -/
theorem Trace.Replays.frame {Observation : Type _} {observe : State → Address → Observation}
    (run : trace.Replays access initial final) (locality : access.Frames observe)
    (outside : ¬ trace.Defs address) :
    observe final address = observe initial address :=
  Proofs.Semantics.ReadWrite.replays_frame run locality outside

theorem Trace.Replays.use_readable
    (run : trace.Replays access initial final) (locality : access.Frames access.read)
    (used : trace.Uses address) :
    ∃ value, access.read initial address = some value :=
  Proofs.Semantics.ReadWrite.replays_use_readable run locality used

theorem Trace.Replays.reads_agree_of_disjoint (run : trace.Replays access initial final)
    (locality : access.Frames access.read) (disjoint : ∀ p, trace.Reads p → ¬ trace.Defs p) :
    trace.reads.Agrees access initial :=
  Proofs.Semantics.ReadWrite.reads_agree_of_disjoint run locality disjoint

theorem Trace.Replays.reads_of_disjoint (run : trace.Replays access initial final)
    (locality : access.Frames access.read) (disjoint : ∀ p, trace.Reads p → ¬ trace.Defs p) :
    trace.reads.toTrace.Replays access initial initial :=
  (ReadTrace.replays_iff _).mpr ⟨rfl, run.reads_agree_of_disjoint locality disjoint⟩

theorem Trace.Replays.invariant {P : State → Prop}
    (run : trace.Replays access initial final) (holds : P initial)
    (preserve : ∀ before after address value, access.write before address value = some after →
      P before → P after) : P final :=
  Proofs.Semantics.ReadWrite.replays_invariant run holds preserve

end Silmaril.Semantics.ReadWrite
