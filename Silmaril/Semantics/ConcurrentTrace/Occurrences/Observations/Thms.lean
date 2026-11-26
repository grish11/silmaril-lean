module

public import Silmaril.Semantics.ConcurrentTrace.Occurrences.Thms
public import Silmaril.Semantics.ConcurrentTrace.Occurrences.Observations.Defs
import Silmaril.Proofs.Semantics.ConcurrentTrace.Occurrences.Observations

public section

namespace Silmaril.Semantics.ConcurrentTrace.OccurrencePoset

universe u v a

variable {T : Type u} {E : Type v} {Addr : Type a}

namespace Iso

variable {p q : OccurrencePoset T E} (f : Iso p q)

theorem concurrent_iff (i j : Fin p.size) :
    q.Concurrent (f.equiv i) (f.equiv j) ↔ p.Concurrent i j :=
  Proofs.Semantics.ConcurrentTrace.Occurrences.concurrent_iff f i j

theorem eventAntichain_iff (s : Finset (Fin p.size)) :
    q.EventAntichain (s.map f.equiv.toEmbedding) ↔ p.EventAntichain s :=
  Proofs.Semantics.ConcurrentTrace.Occurrences.eventAntichain_iff f s

theorem threadBlock_iff (t : T) (block : List (Fin p.size)) :
    q.ThreadBlock t (block.map f.equiv) ↔ p.ThreadBlock t block :=
  Proofs.Semantics.ConcurrentTrace.Occurrences.threadBlock_iff f t block

theorem threadBlockFamily_iff {n : Nat} (threads : Fin n → T)
    (blocks : Fin n → List (Fin p.size)) :
    q.ThreadBlockFamily threads (fun k => (blocks k).map f.equiv) ↔
      p.ThreadBlockFamily threads blocks :=
  Proofs.Semantics.ConcurrentTrace.Occurrences.threadBlockFamily_iff f threads blocks

theorem fragmentBefore_iff {s : Finset (Fin p.size)} (i j : {x // x ∈ s}) :
    q.fragmentBefore (s := s.map f.equiv.toEmbedding)
        ⟨f.equiv i.val, Finset.mem_map_of_mem _ i.property⟩
        ⟨f.equiv j.val, Finset.mem_map_of_mem _ j.property⟩ ↔
      p.fragmentBefore i j :=
  f.before_iff i.val j.val

theorem fragmentFamily_iff {n : Nat} (fragments : Fin n → Finset (Fin p.size)) :
    q.FragmentFamily (fun k => (fragments k).map f.equiv.toEmbedding) ↔
      p.FragmentFamily fragments :=
  Proofs.Semantics.ConcurrentTrace.Occurrences.fragmentFamily_iff f fragments

theorem conflictAt_eq (policy : ConflictPolicy T E Addr) (i j : Fin p.size) :
    q.conflictAt policy (f.equiv i) (f.equiv j) = p.conflictAt policy i j :=
  Proofs.Semantics.ConcurrentTrace.Occurrences.conflictAt_eq f policy i j

include f in
theorem conflictAddresses_eq (policy : ConflictPolicy T E Addr) :
    q.conflictAddresses policy = p.conflictAddresses policy :=
  Proofs.Semantics.ConcurrentTrace.Occurrences.conflictAddresses_eq f policy

theorem raceAt_eq (touches : T → E → Set Addr) (i j : Fin p.size) :
    q.raceAt touches (f.equiv i) (f.equiv j) = p.raceAt touches i j :=
  f.conflictAt_eq (anyTouchPolicy touches) i j

include f in
theorem raceAddresses_eq (touches : T → E → Set Addr) :
    q.raceAddresses touches = p.raceAddresses touches :=
  f.conflictAddresses_eq (anyTouchPolicy touches)

end Iso

/-- Observe the addresses reported by a conflict policy on a trace class. -/
@[expose] def traceConflictAddresses (policy : ConflictPolicy T E Addr)
    (t : Trace T E) : Set Addr :=
  Quotient.liftOn (ofTrace t) (fun p => p.conflictAddresses policy) (fun _ _ ⟨f⟩ =>
    (f.conflictAddresses_eq policy).symm)

@[simp] theorem traceConflictAddresses_ofWord (policy : ConflictPolicy T E Addr) (w : Word T E) :
    traceConflictAddresses policy (ConcurrentTrace.ofWord w) =
      (ofWord w).conflictAddresses policy := rfl

/-- The set of addresses with concurrent overlaps, for a trace class. -/
@[expose] def traceRaceAddresses (touches : T → E → Set Addr) (t : Trace T E) : Set Addr :=
  traceConflictAddresses (anyTouchPolicy touches) t

@[simp] theorem traceRaceAddresses_ofWord (touches : T → E → Set Addr) (w : Word T E) :
    traceRaceAddresses touches (ConcurrentTrace.ofWord w) = (ofWord w).raceAddresses touches := rfl

end Silmaril.Semantics.ConcurrentTrace.OccurrencePoset
