module

import Silmaril.Semantics.ConcurrentTrace.Occurrences.Observations.Thms

namespace Silmaril.Proofs.Semantics.ConcurrentTrace.Occurrences.Regression

open Silmaril.Semantics.ConcurrentTrace
open OccurrencePoset (Causal Edge)

private abbrev interleaved : Word Nat Unit :=
  [.event 0 (), .event 1 (), .event 0 ()]

private abbrev p := OccurrencePoset.ofWord interleaved
private abbrev firstA : Fin 3 := 0
private abbrev b : Fin 3 := 1
private abbrev lastA : Fin 3 := 2

private theorem sameThreadOrder : p.before firstA lastA :=
  .single ⟨by decide, fun h => by cases h with | events h => exact h rfl⟩

-- Equal payloads at distinct positions are ordered occurrences.
example : p.label firstA = p.label lastA ∧ firstA ≠ lastA ∧ p.before firstA lastA :=
  ⟨rfl, by decide, sameThreadOrder⟩

-- The latter copy moves across B and the earlier copy keeps its own identity.
example :
    let f := OccurrencePoset.swapIso ([.event 0 ()] : Word Nat Unit) []
      (.events (t := 1) (u := 0) (e := ()) (f := ()) (by decide))
    (f.equiv firstA).val = 0 ∧ (f.equiv b).val = 2 ∧ (f.equiv lastA).val = 1 := by
  have hab : (Letter.event 1 ()).Independent (Letter.event 0 ()) := .events (by decide)
  exact ⟨OccurrencePoset.swapIso_apply_val [.event 0 ()] [] hab firstA,
    OccurrencePoset.swapIso_apply_val [.event 0 ()] [] hab b,
    OccurrencePoset.swapIso_apply_val [.event 0 ()] [] hab lastA⟩

private theorem noEdgeToB (i : Fin interleaved.length) : ¬ Edge interleaved i 1 := by
  rintro ⟨hlt, hdep⟩
  have hi : i = 0 := Fin.ext (by
    change i.val < 1 at hlt
    change i.val = 0
    omega)
  subst i
  exact hdep (.events (by decide))

private theorem noEdgeFromB (i : Fin interleaved.length) : ¬ Edge interleaved 1 i := by
  rintro ⟨hlt, hdep⟩
  have hi : i = 2 := Fin.ext (by
    have hbound : i.val < 3 := i.isLt
    change 1 < i.val at hlt
    change i.val = 2
    omega)
  subst i
  exact hdep (.events (by decide))

private theorem noCauseToB (i : Fin interleaved.length) : ¬ Causal interleaved i 1 := by
  intro h
  cases h with
  | single edge => exact noEdgeToB _ edge
  | tail _ edge => exact noEdgeToB _ edge

private theorem noCauseFromB (i : Fin interleaved.length) : ¬ Causal interleaved 1 i := by
  intro h
  obtain ⟨j, edge, _⟩ := Relation.TransGen.head'_iff.mp h
  exact noEdgeFromB j edge

private theorem concurrentAB : p.Concurrent firstA b :=
  ⟨(show firstA ≠ b by decide), noCauseToB 0, noCauseFromB 0⟩

example : p.Concurrent firstA b ∧ p.Concurrent b lastA ∧ ¬ p.Concurrent firstA lastA :=
  ⟨concurrentAB, ⟨(show b ≠ lastA by decide), noCauseFromB 2, noCauseToB 2⟩, fun h => h.2.1 sameThreadOrder⟩

private abbrev chained : Word Nat Unit :=
  [.event 0 (), .sync [0], .sync [2], .event 2 ()]

-- No individual sync sees both events. The disjoint syncs still form the middle edge.
example :
    (chained[0]).Independent (chained[3]) ∧
    (chained[0]).Independent (chained[2]) ∧
    (chained[1]).Independent (chained[3]) ∧
    Causal chained 0 3 := by
  refine ⟨.events (by decide), .eventSync (by decide), .syncEvent (by decide), ?_⟩
  have ha : Edge chained 0 1 := ⟨by decide, fun h => by
    cases h with | eventSync h => exact h (by decide)⟩
  have hs : Edge chained 1 2 := ⟨by decide, fun h => by cases h⟩
  have hb : Edge chained 2 3 := ⟨by decide, fun h => by
    cases h with | syncEvent h => exact h (by decide)⟩
  exact (Relation.TransGen.single ha).tail hs |>.tail hb

-- Empty syncs also occur separately and are ordered.
example : Causal ([.sync [], .sync []] : Word Nat Unit) 0 1 :=
  .single ⟨by decide, fun h => by cases h⟩

private def touches (_ : Nat) (_ : Unit) : Set Nat := {7}

-- Different threads can overlap even when their occurrences commute.
example : 7 ∈ p.raceAt touches firstA b ∧ 7 ∉ p.raceAt touches firstA lastA :=
  ⟨⟨concurrentAB, rfl, rfl⟩, fun h => h.1.2.1 sameThreadOrder⟩

example : 7 ∈ OccurrencePoset.traceRaceAddresses touches (ofWord interleaved) :=
  ⟨firstA, b, concurrentAB, rfl, rfl⟩

end Silmaril.Proofs.Semantics.ConcurrentTrace.Occurrences.Regression
