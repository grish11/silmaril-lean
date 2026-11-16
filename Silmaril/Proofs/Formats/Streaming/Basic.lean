module

public import Silmaril.Formats.Streaming.Defs
public import Silmaril.Semantics.Acceptors.Thms

/-! # Proofs: incremental acceptors for the format languages
(`Silmaril.Formats.Streaming.Thms`) -/

@[expose] public section

namespace Silmaril.Proofs.Formats.Streaming

open RegularExpression Silmaril Silmaril.Formats.Streaming

theorem matchEpsilon_foldl_deriv (r : RegularExpression UInt8) (w : List UInt8) :
    (w.foldl deriv r).matchEpsilon = r.rmatch w := by
  induction w generalizing r with
  | nil => rfl
  | cons a w ih => exact ih (deriv r a)

theorem foldl_process {χ : Type} [ChunkView χ UInt8] (r s : RegularExpression UInt8)
    (cs : List χ) :
    cs.foldl (derivAcceptor (χ := χ) r).process s =
      (cs.flatMap ChunkView.toList).foldl deriv s := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
    rw [List.foldl_cons, ih, List.flatMap_cons, List.foldl_append]
    rfl

theorem derivAcceptor_correctFold {χ : Type} [ChunkView χ UInt8] (r : RegularExpression UInt8)
    [DecidablePred (· ∈ r.matches')] : (derivAcceptor (χ := χ) r).CorrectFold r.matches' := by
  intro cs
  show ((cs.foldl (derivAcceptor (χ := χ) r).process r).matchEpsilon) = _
  rw [foldl_process, matchEpsilon_foldl_deriv, Acceptor.member]
  exact Bool.eq_iff_iff.mpr ((rmatch_iff_matches' _ _).trans decide_eq_true_iff.symm)

theorem derivAcceptor_correctInterleaved {χ : Type} [ChunkView χ UInt8]
    (r : RegularExpression UInt8) [DecidablePred (· ∈ r.matches')] :
    (derivAcceptor (χ := χ) r).CorrectInterleaved r.matches' :=
  Acceptor.correctInterleaved_of_correctFold (fun _ => rfl)
    (Acceptor.ResetSound.of_eq fun _ => rfl) (derivAcceptor_correctFold r)

end Silmaril.Proofs.Formats.Streaming

end
