module

import Silmaril.Formats.SExp.Arena.Thms

namespace Silmaril.Formats.SExpArena

private def cells : List (Cell Nat String) := [.cons ⟨1, 1⟩, .atom "leaf", .nil]
private def sumCell : Cons Nat ⊕ String := .inl ⟨1, 1⟩

example : (Arena.ofList cells).Unfolds 0 (.cons (.atom "leaf") (.atom "leaf")) :=
  .cons rfl (.atom rfl) (.atom rfl)

example : (Arena.ofMap (fun _ : Nat => sumCell)) 0 = some (.cons ⟨1, 1⟩) := rfl
example : (Arena.ofList [sumCell, .inr "leaf"]) 1 = some (.atom "leaf") := rfl
example : (Arena.ofMap (fun _ : Nat => some sumCell)) 0 = some (.cons ⟨1, 1⟩) := rfl
example : (Arena.ofMap (fun _ : Nat => Undef.defined (Cell.nil : Cell Nat String))) 0 =
    some .nil := rfl
example : (Arena.ofList [Undef.defined sumCell, .undef]) 1 = none := rfl

private def holes : Arena Nat String := Arena.ofList [some (Cell.nil : Cell Nat String), none]

example : holes.Unfolds 0 .nil := .nil rfl
example : (Arena.ofOption (none : Option (Arena Nat String))) 0 = none := rfl
example : (Arena.ofUndef (.defined holes)) 0 = some .nil := rfl

-- An explicit hole and an out-of-bounds root have the same empty observation.
example : (⟨1, holes⟩ : Pointed Nat String) ≈ ⟨2, holes⟩ := by
  have emptyAt (i : Nat) (missing : holes i = none) :
      (⟨i, holes⟩ : Pointed Nat String).denotation = ∅ :=
    Pointed.denotation_eq_empty_iff.mpr fun ⟨_, unfolded⟩ =>
      Arena.not_unfolds_of_lookup_none missing unfolded
  exact (emptyAt 1 rfl).trans (emptyAt 2 rfl).symm

private structure EntryPoints where
  main : Nat
  others : List Nat

private instance : Root EntryPoints Nat where
  indices roots := roots.main :: roots.others

example (roots : EntryPoints) : (↑roots : List Nat) = roots.main :: roots.others := rfl
example : Root.indices (⟨0, []⟩ : EntryPoints) = [0] := rfl

private def rooted : Rooted Nat String EntryPoints := ⟨⟨0, [2]⟩, Arena.ofList cells⟩

example : rooted.markSweep ≈ rooted := rooted.markSweep_equiv

example : (⟨⟨0, [2]⟩, Arena.ofList cells⟩ : Rooted Nat String EntryPoints) ≈
    ⟨⟨2, [0]⟩, Arena.ofList cells⟩ :=
  Rooted.equiv_of_perm (List.Perm.swap 2 0 [])

-- Sweeping above the nil export drops an unexported atom from the whole-arena observation.
example :
    ((Arena.ofList cells).markSweep [2]).denotation ≠ (Arena.ofList cells).denotation := by
  let arena := Arena.ofList cells
  have reachableOnly : ∀ i, arena.ReachableFrom [2] i → i = 2 := by
    rintro i ⟨root, member, reached⟩
    have rootEq : root = 2 := List.mem_singleton.mp member
    subst root
    rcases Relation.ReflTransGen.cases_head reached with equal | ⟨_, ⟨_, read, _⟩, _⟩
    · exact equal.symm
    · cases read
  intro eq
  have before : (.atom "leaf" : SExp2 String) ∈ arena.denotation := ⟨1, .atom rfl⟩
  obtain ⟨i, after⟩ : (.atom "leaf" : SExp2 String) ∈ (arena.markSweep [2]).denotation := eq ▸ before
  have read := Arena.unfolds_atom_iff.mp after
  by_cases reached : arena.ReachableFrom [2] i
  · rw [Arena.markSweep_preservesReachable i reached, reachableOnly i reached] at read
    cases read
  · rw [Arena.markSweep_lookup_unreachable reached] at read
    cases read

private def ring : FiniteLookup Nat (Cell Nat String) :=
  FiniteLookup.ofList [.cons ⟨0, 0⟩]

example : ring.withRefCounts.count? 0 = some 2 := by decide

example : ring.withRefCounts.CountsCorrect := RefCounted.withRefCounts_correct ring

private theorem ringCycle : Arena.CyclicBelow ring.lookup 0 :=
  ⟨0, .refl, .single ⟨⟨0, 0⟩, rfl, Or.inl rfl⟩⟩

example : Arena.Cyclic ring.withRefCounts.erase.lookup := by
  rw [RefCounted.erase_withRefCounts]
  exact ⟨0, .single ⟨⟨0, 0⟩, rfl, Or.inl rfl⟩⟩

example : ¬ ∃ expr, Arena.Unfolds ring.lookup 0 expr :=
  fun ⟨_, unfolded⟩ => Arena.unfolds_acyclicBelow unfolded ringCycle

private def sparseEntries : FiniteLookup Nat (Option (Cell Nat String)) :=
  FiniteLookup.ofList [some (.cons ⟨1, 3⟩), some (.atom "leaf"), some (.cons ⟨1, 1⟩), none]

private def sparse : FiniteLookup Nat (Cell Nat String) := sparseEntries.normalize

private theorem holeReached : Arena.Reachable sparse.lookup 0 3 :=
  .single ⟨⟨1, 3⟩, rfl, Or.inr rfl⟩

example : ¬ ∃ expr, Arena.Unfolds sparse.lookup 0 expr := by
  intro unfolded
  obtain ⟨_, read⟩ := ((sparse.exists_unfolds_iff 0).mp unfolded).2 3 holeReached
  cases read

example : (sparseEntries.markSweep [0]).normalize.lookup 3 = none := by
  rw [FiniteLookup.markSweep_normalize_lookup]
  exact (Arena.markSweep_preservesReachable 3 ⟨0, List.mem_singleton.mpr rfl, holeReached⟩).trans rfl

-- The dead cons contributes two references to the surviving leaf before deletion.
example : sparse.withRefCounts.count? 1 = some 3 := by decide
example : (sparse.restrict (· ≠ 2)).withRefCounts.count? 1 = some 1 := by decide
example : sparse.incomingCount 3 = 1 ∧ sparse.withRefCounts.count? 3 = none := by decide

end Silmaril.Formats.SExpArena
