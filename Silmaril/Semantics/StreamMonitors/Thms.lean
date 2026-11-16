module

public import Silmaril.Semantics.StreamMonitors.Defs
public import Cslib.Computability.Languages.SafetyLiveness
import Silmaril.Proofs.Semantics.StreamMonitors.Verdicts

/-!
# Monitoring chunk streams: theorems

Statements about `Silmaril.Semantics.StreamMonitors.Defs`; proofs are in
`Silmaril.Proofs.Semantics.StreamMonitors.Verdicts`.

* `safetyω L` is a safety property in CSLib's topological sense (`isSafety_safetyω`).
  If every word extends by a nonempty word into `L`, then `L↗ω` is a liveness property
  (`isLiveness_omegaLim`).
* For one letter per chunk, chunk-boundary verdicts agree exactly with the limit word:
  `alwaysAt_ofω_iff` and `infOftenAt_ofω_iff`.
* For any chunking with an infinite limit, safety of the limit implies the
  boundary verdict (`alwaysAt_of_mem_safetyω`), but not conversely
  (`alwaysAt_coarse_counterexample`). For liveness the boundary verdict implies
  `L↗ω` of the limit (`mem_omegaLim_of_infOftenAt`).
* A stream with a finite limit `w` (one that is not progressive, for instance a
  terminating stream or one stalled on empty chunks) has "infinitely often yes" and
  "eventually always yes" verdicts that both just say `w ∈ L`
  (`verdicts_of_limit_fin`). Liveness verdicts therefore need progress as a hypothesis.
-/

public section

namespace Silmaril.Streams

open Cslib

universe u

variable {α : Type u}

theorem mem_safetyω {L : Language α} {s : ωSequence α} :
    s ∈ safetyω L ↔ ∀ n, s.take n ∈ L := Iff.rfl

theorem mem_omegaLim_iff {L : Language α} {s : ωSequence α} :
    s ∈ L↗ω ↔ ∀ M, ∃ m, M ≤ m ∧ s.take m ∈ L :=
  Silmaril.Proofs.Semantics.StreamMonitors.mem_omegaLim_iff

/-- Prefix safety is a safety property (a closed set of infinite words). -/
theorem isSafety_safetyω (L : Language α) : (safetyω L).IsSafety :=
  Silmaril.Proofs.Semantics.StreamMonitors.isSafety_safetyω L

/-- "Infinitely many prefixes in `L`" is a liveness property (a dense set) when every
finite word can be extended by a nonempty word into `L`. -/
theorem isLiveness_omegaLim {L : Language α} (hL : ∀ u, ∃ v, v ≠ [] ∧ u ++ v ∈ L) :
    (L↗ω).IsLiveness :=
  Silmaril.Proofs.Semantics.StreamMonitors.isLiveness_omegaLim hL

namespace Chunks

/-- On an infinite limit, every delivered prefix is a prefix of the limit word. -/
theorem prefixAt_eq_take {cs : Chunks α} {s : ωSequence α} (h : cs.limit = .inf s) (n : ℕ) :
    cs.prefixAt n = s.take (cs.prefixAt n).length :=
  Silmaril.Proofs.Semantics.StreamMonitors.prefixAt_eq_take h n

theorem alwaysAt_of_mem_safetyω {L : Language α} {cs : Chunks α} {s : ωSequence α}
    (h : cs.limit = .inf s) (hs : s ∈ safetyω L) : cs.AlwaysAt L :=
  Silmaril.Proofs.Semantics.StreamMonitors.alwaysAt_of_mem_safetyω h hs

theorem alwaysAt_ofω_iff {L : Language α} {s : ωSequence α} :
    (ofω s).AlwaysAt L ↔ s ∈ safetyω L :=
  Silmaril.Proofs.Semantics.StreamMonitors.alwaysAt_ofω_iff

/-- Coarse chunks can hide a violation from a chunk-boundary monitor. -/
theorem alwaysAt_coarse_counterexample :
    ∃ (L : Language Bool) (cs : Chunks Bool) (s : ωSequence Bool),
      cs.limit = .inf s ∧ cs.AlwaysAt L ∧ s ∉ safetyω L :=
  Silmaril.Proofs.Semantics.StreamMonitors.alwaysAt_coarse_counterexample

/-- Infinitely many yes answers on an infinite limit witness `L↗ω`. -/
theorem mem_omegaLim_of_infOftenAt {L : Language α} {cs : Chunks α} {s : ωSequence α}
    (h : cs.limit = .inf s) (hL : cs.InfOftenAt L) : s ∈ L↗ω :=
  Silmaril.Proofs.Semantics.StreamMonitors.mem_omegaLim_of_infOftenAt h hL

theorem infOftenAt_ofω_iff {L : Language α} {s : ωSequence α} :
    (ofω s).InfOftenAt L ↔ s ∈ L↗ω :=
  Silmaril.Proofs.Semantics.StreamMonitors.infOftenAt_ofω_iff

/-- On a finite limit `w`, the liveness-style verdicts only decide `w ∈ L`. -/
theorem verdicts_of_limit_fin {L : Language α} {cs : Chunks α} {w : List α}
    (h : cs.limit = .fin w) :
    (cs.InfOftenAt L ↔ w ∈ L) ∧ (cs.EventuallyAlwaysAt L ↔ w ∈ L) :=
  Silmaril.Proofs.Semantics.StreamMonitors.verdicts_of_limit_fin h

/-- A terminating stream: the answer after the end of input decides its concatenation. -/
theorem eventuallyAlwaysAt_ofList_iff {L : Language α} (cs : List (List α)) :
    (ofList cs).EventuallyAlwaysAt L ↔ cs.flatten ∈ L :=
  (verdicts_of_limit_fin (limit_ofList cs)).2

/-- A stalled stream that has delivered `w ∈ L` answers yes infinitely often, although it
delivers no infinite word. -/
theorem infOftenAt_stall {L : Language α} {w : List α} (hw : w ∈ L) :
    (ofList [w]).InfOftenAt L ∧ ¬ (ofList [w]).Progressive := by
  have h := limit_ofList [w]
  refine ⟨(verdicts_of_limit_fin h).1.mpr (by simpa using hw), ?_⟩
  rw [← isFinite_limit_iff, h]; trivial

end Chunks

end Silmaril.Streams
