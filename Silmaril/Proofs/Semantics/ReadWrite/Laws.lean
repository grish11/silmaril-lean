module

public import Silmaril.Semantics.ReadWrite.Defs

public section
namespace Silmaril.Proofs.Semantics.ReadWrite

open Silmaril.Semantics.ReadWrite

universe u v w x
variable {Address : Type u} {Value : Type v} {State : Type w} {Other : Type x} {access : Access Address Value State}
variable {trace first last : Trace Address Value} {address : Address}
variable {initial middle final : State}

theorem reads_append :
    (first ++ last).reads = first.reads ++ last.reads := by
  simp [Trace.reads]

theorem writes_append :
    (first ++ last).writes = first.writes ++ last.writes := by
  simp [Trace.writes]

theorem reads_toTrace (reads : ReadTrace Address Value) :
    reads.toTrace.reads = reads := by
  induction reads with
  | nil => rfl
  | cons entry rest ih => simpa [ReadTrace.toTrace, Trace.reads] using ih

theorem writes_toTrace (writes : WriteTrace Address Value) :
    writes.toTrace.writes = writes := by
  induction writes with
  | nil => rfl
  | cons entry rest ih => simpa [WriteTrace.toTrace, Trace.writes] using ih

theorem readOnly_reads (trace : Trace Address Value) : trace.reads.toTrace.ReadOnly := by
  simp [Trace.ReadOnly, reads_toTrace]

theorem writeOnly_writes (trace : Trace Address Value) : trace.writes.toTrace.WriteOnly := by
  simp [Trace.WriteOnly, writes_toTrace]

theorem defs_append :
    (first ++ last).Defs address ↔ first.Defs address ∨ last.Defs address := by
  simp only [Trace.Defs, writes_append, List.mem_append, exists_or]

theorem footprint_append :
    (first ++ last).Footprint address ↔ first.Footprint address ∨ last.Footprint address := by
  simp only [Trace.Footprint, Trace.Reads, reads_append, List.mem_append, exists_or, defs_append]
  grind

theorem uses_append :
    (first ++ last).Uses address ↔ first.Uses address ∨ (¬ first.Defs address ∧ last.Uses address) := by
  induction first with
  | nil => simp [Trace.Uses, Trace.Defs, Trace.writes]
  | cons event rest ih =>
    cases event <;> simp only [List.cons_append, Trace.Uses, ih, Trace.Defs,
      Trace.writes, List.filterMap_cons, List.mem_cons, Prod.mk.injEq] <;> grind

theorem uses_or_defs : trace.Uses address ∨ trace.Defs address ↔ trace.Footprint address := by
  induction trace with
  | nil => simp [Trace.Uses, Trace.Footprint, Trace.Reads, Trace.Defs, Trace.reads, Trace.writes]
  | cons event rest ih =>
    cases event <;>
      simp only [Trace.Uses, Trace.Footprint, Trace.Reads, Trace.Defs, Trace.reads, Trace.writes,
        List.filterMap_cons, List.mem_cons,
        Prod.mk.injEq] at ih ⊢ <;> grind

theorem replays_append :
    (first ++ last).Replays access initial final ↔
      ∃ middle, first.Replays access initial middle ∧ last.Replays access middle final := by
  induction first generalizing initial with
  | nil => simp [Trace.Replays]
  | cons event rest ih =>
    cases event <;> simp only [List.cons_append, Trace.Replays, ih] <;> grind

theorem run_eq_some_iff [DecidableEq Value] :
    trace.run access initial = some final ↔ trace.Replays access initial final := by
  induction trace generalizing initial with
  | nil => simp [Trace.run, Trace.Replays]
  | cons event rest ih =>
    cases event with
    | read address value =>
      by_cases h : access.read initial address = some value <;> simp [Trace.run, Trace.Replays, h, ih]
    | write address value =>
      cases h : access.write initial address value <;> simp [Trace.run, Trace.Replays, h, ih]

theorem replays_unique (left : trace.Replays access initial middle)
    (right : trace.Replays access initial final) : middle = final := by
  induction trace generalizing initial with
  | nil => exact left.symm.trans right
  | cons event rest ih =>
    cases event with
    | read => exact ih left.2 right.2
    | write =>
      obtain ⟨next, step, tail⟩ := left
      obtain ⟨next', step', tail'⟩ := right
      rw [step] at step'
      cases Option.some.inj step'
      exact ih tail tail'

theorem replays_map {other : Access Address Value Other} (f : State → Other)
    (read : ∀ m p, other.read (f m) p = access.read m p)
    (write : ∀ m p v, other.write (f m) p v = (access.write m p v).map f)
    {target : Other} :
    trace.Replays other (f initial) target ↔
      ∃ final, trace.Replays access initial final ∧ f final = target := by
  induction trace generalizing initial with
  | nil => simp [Trace.Replays]
  | cons event rest ih =>
    cases event with
    | read p v => simp only [Trace.Replays, read, ih]; grind
    | write p v =>
      cases h : access.write initial p v <;>
        simp [Trace.Replays, write, h, ih]

theorem run_map [DecidableEq Value] {other : Access Address Value Other} (f : State → Other)
    (read : ∀ m p, other.read (f m) p = access.read m p)
    (write : ∀ m p v, other.write (f m) p v = (access.write m p v).map f) :
    trace.run other (f initial) = (trace.run access initial).map f := by
  induction trace generalizing initial with
  | nil => rfl
  | cons event rest ih =>
    cases event with
    | read p v =>
      by_cases h : access.read initial p = some v <;> simp [Trace.run, read, h, ih]
    | write p v =>
      cases h : access.write initial p v <;> simp [Trace.run, write, h, ih]

theorem replays_readTrace (reads : ReadTrace Address Value) :
    reads.toTrace.Replays access initial final ↔ initial = final ∧ reads.Agrees access initial := by
  induction reads with
  | nil => simp [ReadTrace.toTrace, Trace.Replays, ReadTrace.Agrees]
  | cons entry rest ih =>
    rcases entry with ⟨p, v⟩
    change (access.read initial p = some v ∧ Trace.Replays access (ReadTrace.toTrace rest) initial final) ↔ _
    rw [ih]
    simp [ReadTrace.Agrees, and_left_comm]

theorem replays_writes (run : trace.Replays access initial final) :
    trace.writes.toTrace.Replays access initial final := by
  induction trace generalizing initial with
  | nil => exact run
  | cons event rest ih =>
    cases event with
    | read => exact ih run.2
    | write =>
      obtain ⟨m, h, tail⟩ := run
      exact ⟨m, h, ih tail⟩

theorem replays_frame {Observation : Type _} {observe : State → Address → Observation}
    (run : trace.Replays access initial final) (locality : access.Frames observe)
    (outside : ¬ trace.Defs address) :
    observe final address = observe initial address := by
  induction trace generalizing initial with
  | nil =>
    change initial = final at run
    rw [run]
  | cons event rest ih =>
    cases event with
    | read => exact ih run.2 outside
    | write p v =>
      obtain ⟨next, step, tail⟩ := run
      have notDef : address ≠ p ∧ ¬Trace.Defs rest address := by
        simpa [Trace.Defs, Trace.writes, Prod.mk.injEq, exists_or] using outside
      exact (ih tail notDef.2).trans (locality step notDef.1)

theorem replays_use_readable
    (run : trace.Replays access initial final) (locality : access.Frames access.read)
    (used : trace.Uses address) :
    ∃ value, access.read initial address = some value := by
  induction trace generalizing initial with
  | nil => exact False.elim used
  | cons event rest ih =>
    cases event with
    | read p v =>
      rcases used with eq | tailUse
      · subst p
        exact ⟨v, run.1⟩
      · exact ih run.2 tailUse
    | write p v =>
      obtain ⟨next, step, tail⟩ := run
      obtain ⟨value, defined⟩ := ih tail used.2
      exact ⟨value, (locality step used.1).symm.trans defined⟩

theorem reads_agree_of_disjoint
    (run : trace.Replays access initial final) (locality : access.Frames access.read)
    (disjoint : ∀ p, trace.Reads p → ¬ trace.Defs p) :
    trace.reads.Agrees access initial := by
  intro entry present
  rcases entry with ⟨address, value⟩
  induction trace generalizing initial with
  | nil => cases present
  | cons event rest ih =>
    cases event with
    | read p v =>
      change (address, value) ∈ (p, v) :: Trace.reads rest at present
      rcases List.mem_cons.mp present with eq | member
      · cases eq
        exact run.1
      · have tailDisjoint : ∀ q, Trace.Reads rest q → ¬Trace.Defs rest q := by
          rintro q ⟨v', hv⟩
          exact disjoint q ⟨v', List.mem_cons_of_mem _ hv⟩
        exact ih run.2 tailDisjoint member
    | write p v =>
      obtain ⟨next, step, tail⟩ := run
      have ne : address ≠ p := by
        intro eq
        subst p
        exact disjoint address ⟨value, present⟩ ⟨v, List.mem_cons_self⟩
      have tailDisjoint : ∀ q, Trace.Reads rest q → ¬Trace.Defs rest q := by
        rintro q h ⟨v', hv⟩
        exact disjoint q h ⟨v', List.mem_cons_of_mem _ hv⟩
      have agrees := ih tail tailDisjoint present
      exact (locality step ne).symm.trans agrees

theorem replays_invariant {P : State → Prop}
    (run : trace.Replays access initial final) (holds : P initial)
    (preserve : ∀ before after address value, access.write before address value = some after →
      P before → P after) : P final := by
  induction trace generalizing initial with
  | nil =>
    change initial = final at run
    exact run ▸ holds
  | cons event rest ih =>
    cases event with
    | read => exact ih run.2 holds
    | write address value =>
      obtain ⟨next, step, tail⟩ := run
      exact ih tail (preserve initial next address value step holds)

end Silmaril.Proofs.Semantics.ReadWrite
