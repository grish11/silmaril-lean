module

public import Silmaril.Semantics.StreamAcceptors.Defs
public import Silmaril.Semantics.Acceptors.Thms
public import Silmaril.Semantics.StreamMonitors.Thms
import Silmaril.Proofs.Semantics.StreamAcceptors.Answers

/-!
# Incremental acceptors on unbounded chunk streams: theorems

* `boundaryAnswer_eq`: a `CorrectFold` acceptor answers, after `n` chunks, whether the
  delivered input `(view cs).prefixAt n` is in `L`.
* `run_boundaryTrace` and `run_boundaryTrace_eq`: for a `Pure` acceptor, the finite
  client trace of `n` process/query rounds returns exactly these answers. With
  `CorrectInterleaved`, they are the specified answers.
* `alwaysAt_iff`, `infOftenAt_iff` and `eventuallyAlwaysAt_iff`: the safety, Büchi and
  co-Büchi verdicts on an acceptor's answers are the monitor verdicts of
  `StreamMonitors` on the chunk stream.
* `mem_omegaLim_of_answers`: infinitely many yes answers on a stream with an infinite
  limit `s` give `s ∈ L↗ω`.
* `answers_of_limit_fin`: on a stream without progress, with finite limit `w` (for
  example a session that only sends empty chunks from some point on), infinitely many
  yes answers mean only `w ∈ L`.
-/

public section

namespace Silmaril.Acceptor

open Cslib Silmaril.Streams

universe u v w

variable {σ : Type u} {χ : Type v} {α : Type w}

theorem prefixAt_view [ChunkView χ α] (cs : ωSequence χ) (n : ℕ) :
    (view cs).prefixAt n = (cs.take n).flatMap ChunkView.toList :=
  Silmaril.Proofs.Semantics.StreamAcceptors.prefixAt_view cs n

/-- For a pure acceptor, the trace of `n` process/query rounds returns the boundary answers. -/
theorem run_boundaryTrace {A : Acceptor σ χ} (hp : A.Pure) (cs : ωSequence χ) (n : ℕ) :
    A.run A.init (boundaryTrace cs n) =
      ((List.range n).map fun k => A.boundaryAnswer cs (k + 1),
        (cs.take n).foldl A.process A.init) :=
  Silmaril.Proofs.Semantics.StreamAcceptors.run_boundaryTrace hp cs n

variable [ChunkView χ α] {L : Language α} [DecidablePred (· ∈ L)]

/-- A correct acceptor answers membership of the input delivered so far. -/
theorem boundaryAnswer_eq {A : Acceptor σ χ} (h : A.CorrectFold L) (cs : ωSequence χ) (n : ℕ) :
    A.boundaryAnswer cs n = member L ((view cs).prefixAt n) :=
  Silmaril.Proofs.Semantics.StreamAcceptors.boundaryAnswer_eq h cs n

/-- The answers of the first `n` rounds of an unbounded session, for a pure acceptor that
is correct on all interleavings. -/
theorem run_boundaryTrace_eq {A : Acceptor σ χ} (hp : A.Pure) (h : A.CorrectInterleaved L)
    (cs : ωSequence χ) (n : ℕ) :
    (A.run A.init (boundaryTrace cs n)).1 =
      (List.range n).map fun k => member L ((view cs).prefixAt (k + 1)) := by
  rw [run_boundaryTrace hp]; simp only [boundaryAnswer_eq h.correctFold]

theorem alwaysAt_iff {A : Acceptor σ χ} (h : A.CorrectFold L) (cs : ωSequence χ) :
    (∀ n, A.boundaryAnswer cs n = true) ↔ (view cs).AlwaysAt L := by
  simp only [boundaryAnswer_eq h, member_eq_true]; rfl

theorem infOftenAt_iff {A : Acceptor σ χ} (h : A.CorrectFold L) (cs : ωSequence χ) :
    (∀ N, ∃ n, N ≤ n ∧ A.boundaryAnswer cs n = true) ↔ (view cs).InfOftenAt L := by
  simp only [boundaryAnswer_eq h, member_eq_true]; rfl

theorem eventuallyAlwaysAt_iff {A : Acceptor σ χ} (h : A.CorrectFold L) (cs : ωSequence χ) :
    (∃ N, ∀ n, N ≤ n → A.boundaryAnswer cs n = true) ↔ (view cs).EventuallyAlwaysAt L := by
  simp only [boundaryAnswer_eq h, member_eq_true]; rfl

/-- Infinitely many yes answers on an infinite limit witness the liveness property `L↗ω`. -/
theorem mem_omegaLim_of_answers {A : Acceptor σ χ} (h : A.CorrectFold L) {cs : ωSequence χ}
    {s : ωSequence α} (hlim : (view cs).limit = .inf s)
    (hinf : ∀ N, ∃ n, N ≤ n ∧ A.boundaryAnswer cs n = true) : s ∈ L↗ω :=
  Chunks.mem_omegaLim_of_infOftenAt hlim ((infOftenAt_iff h cs).mp hinf)

/-- Without progress, infinitely many yes answers only say that the finite limit is in `L`. -/
theorem answers_of_limit_fin {A : Acceptor σ χ} (h : A.CorrectFold L) {cs : ωSequence χ}
    {w : List α} (hlim : (view cs).limit = .fin w) :
    (∀ N, ∃ n, N ≤ n ∧ A.boundaryAnswer cs n = true) ↔ w ∈ L :=
  (infOftenAt_iff h cs).trans (Chunks.verdicts_of_limit_fin hlim).1

end Silmaril.Acceptor
