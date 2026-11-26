module

import Silmaril.Semantics.ConcurrentTrace.Occurrences.Observations.Thms

namespace Silmaril.Proofs.Semantics.ConcurrentTrace.Occurrences.Conflict.Regression

open Silmaril.Semantics.ConcurrentTrace
open OccurrencePoset (Causal causal_lt readWritePolicy traceConflictAddresses)

private inductive Access
  | read
  | write

private def reads (_ : Nat) : Access → Set Nat
  | .read => {7}
  | .write => ∅

private def writes (_ : Nat) : Access → Set Nat
  | .read => ∅
  | .write => {7}

private abbrev pair (t : Nat) (x y : Access) : Word Nat Access :=
  [.event 0 x, .event t y]

private abbrev first : Fin 2 := 0
private abbrev second : Fin 2 := 1

private theorem concurrentPair (x y : Access) :
    (OccurrencePoset.ofWord (pair 1 x y)).Concurrent first second := by
  refine ⟨(show first ≠ second by decide), ?_, ?_⟩
  · intro h
    cases h with
    | single edge => exact edge.2 (.events (by decide))
    | @tail k _ path edge =>
      have h₁ := causal_lt path
      have h₂ := edge.1
      change 0 < k.val at h₁
      change k.val < 1 at h₂
      omega
  · intro h
    have hlt : (1 : Nat) < 0 := causal_lt h
    omega

private abbrev rwPolicy := readWritePolicy reads writes

-- Both reads touch the address. Only the any-touch policy reports the overlap.
example :
    let p := OccurrencePoset.ofWord (pair 1 .read .read)
    7 ∈ p.raceAt reads first second ∧ 7 ∉ p.conflictAt rwPolicy first second :=
  ⟨⟨concurrentPair _ _, rfl, rfl⟩, fun h => h.2.elim And.left And.left⟩

example : 7 ∈ (OccurrencePoset.ofWord (pair 1 .read .write)).conflictAt rwPolicy first second :=
  ⟨concurrentPair _ _, Or.inr ⟨rfl, rfl⟩⟩

example : 7 ∈ (OccurrencePoset.ofWord (pair 1 .write .read)).conflictAt rwPolicy first second :=
  ⟨concurrentPair _ _, Or.inl ⟨rfl, Or.inl rfl⟩⟩

example : 7 ∈ traceConflictAddresses rwPolicy (ofWord (pair 1 .write .write)) :=
  ⟨first, second, concurrentPair _ _, Or.inl ⟨rfl, Or.inr rfl⟩⟩

-- The same footprints conflict under the policy, but same-thread order excludes the pair.
example :
    let w := pair 0 .read .write
    7 ∈ rwPolicy w[0] w[1] ∧
      7 ∉ (OccurrencePoset.ofWord w).conflictAt rwPolicy first second := by
  have h : Causal (pair 0 .read .write) first second :=
    .single ⟨by decide, fun h => by cases h with | events h => exact h rfl⟩
  exact ⟨Or.inr ⟨rfl, rfl⟩, fun hc => hc.1.2.1 h⟩

end Silmaril.Proofs.Semantics.ConcurrentTrace.Occurrences.Conflict.Regression
