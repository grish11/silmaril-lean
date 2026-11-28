module

public import Silmaril.Semantics.ConcurrentTrace.Occurrences.Observations.Defs

public section

namespace Silmaril.Proofs.Semantics.ConcurrentTrace.Occurrences

open Silmaril.Semantics.ConcurrentTrace
open OccurrencePoset

universe u v a

variable {T : Type u} {E : Type v} {Addr : Type a}
variable {p q : OccurrencePoset T E} (f : Iso p q)

theorem concurrent_iff (i j : Fin p.size) :
    q.Concurrent (f.equiv i) (f.equiv j) ↔ p.Concurrent i j := by
  simp [Concurrent, f.equiv.injective.eq_iff, f.before_iff]

theorem eventAntichain_iff (s : Finset (Fin p.size)) :
    q.EventAntichain (s.map f.equiv.toEmbedding) ↔ p.EventAntichain s := by
  simp only [EventAntichain, Set.Pairwise, Finset.mem_coe, Finset.forall_mem_map,
    Equiv.coe_toEmbedding, f.label_eq, ne_eq, f.equiv.injective.eq_iff, concurrent_iff f]

theorem threadBlock_iff (t : T) (block : List (Fin p.size)) :
    q.ThreadBlock t (block.map f.equiv) ↔ p.ThreadBlock t block := by
  simp only [ThreadBlock, ne_eq, List.map_eq_nil_iff, List.forall_mem_map, f.label_eq,
    List.pairwise_map]
  exact and_congr_right fun _ => and_congr_right fun _ => List.Pairwise.iff f.before_iff

theorem threadBlockFamily_iff {n : Nat} (threads : Fin n → T)
    (blocks : Fin n → List (Fin p.size)) :
    q.ThreadBlockFamily threads (fun k => (blocks k).map f.equiv) ↔
      p.ThreadBlockFamily threads blocks := by
  simp only [ThreadBlockFamily, threadBlock_iff f, List.forall_mem_map, concurrent_iff f]

theorem fragmentFamily_iff {n : Nat} (fragments : Fin n → Finset (Fin p.size)) :
    q.FragmentFamily (fun k => (fragments k).map f.equiv.toEmbedding) ↔
      p.FragmentFamily fragments := by
  simp only [FragmentFamily, Fragment, Finset.map_nonempty, Finset.forall_mem_map,
    Equiv.coe_toEmbedding, concurrent_iff f]

theorem conflictAt_eq (policy : ConflictPolicy T E Addr) (i j : Fin p.size) :
    q.conflictAt policy (f.equiv i) (f.equiv j) = p.conflictAt policy i j := by
  simp [conflictAt, f.label_eq, concurrent_iff f]

include f in
theorem conflictAddresses_eq (policy : ConflictPolicy T E Addr) :
    q.conflictAddresses policy = p.conflictAddresses policy := by
  ext a
  change (∃ i j, a ∈ q.conflictAt policy i j) ↔ (∃ i j, a ∈ p.conflictAt policy i j)
  constructor
  · rintro ⟨i, j, ha⟩
    obtain ⟨i, rfl⟩ := f.equiv.surjective i
    obtain ⟨j, rfl⟩ := f.equiv.surjective j
    exact ⟨i, j, conflictAt_eq f policy i j ▸ ha⟩
  · rintro ⟨i, j, ha⟩
    exact ⟨f.equiv i, f.equiv j, (conflictAt_eq f policy i j).symm ▸ ha⟩

end Silmaril.Proofs.Semantics.ConcurrentTrace.Occurrences
