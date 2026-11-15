module

public import Silmaril.Semantics.Streams.Defs
import Mathlib.Data.Seq.Basic

/-! # Proofs: words and Mathlib's `Stream'.Seq` -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.Streams

open Cslib Silmaril.Streams

universe u

variable {α : Type u}

theorem not_terminates_ofStream (s : Stream' α) : ¬ (Stream'.Seq.ofStream s).Terminates := by
  rintro ⟨n, hn⟩
  simp [Stream'.Seq.TerminatedAt, Stream'.Seq.ofStream, Stream'.Seq.get?, Stream'.map] at hn

theorem toSeq_ofSeq (s : Stream'.Seq α) : (Word.ofSeq s).toSeq = s := by
  unfold Word.ofSeq
  split
  · exact Stream'.Seq.ofList_toList s _
  · rename_i h
    apply Stream'.Seq.ext
    intro n
    show Stream'.Seq.get? (Stream'.Seq.ofStream (s.toStream h)) n = s.get? n
    have hs := Stream'.Seq.not_terminates_iff.mp h n
    simp only [Stream'.Seq.ofStream, Stream'.Seq.get?, Stream'.map, Stream'.get,
      Stream'.Seq.toStream]
    exact Option.some_get hs

theorem ofSeq_toSeq (t : Word α) : Word.ofSeq t.toSeq = t := by
  cases t with
  | fin w =>
    show Word.ofSeq (Stream'.Seq.ofList w) = _
    unfold Word.ofSeq
    split
    · exact congrArg Word.fin (Stream'.Seq.toList_ofList w)
    · rename_i h; exact absurd (Stream'.Seq.terminates_ofList w) h
  | inf s =>
    show Word.ofSeq (Stream'.Seq.ofStream s.get) = _
    unfold Word.ofSeq
    split
    · rename_i h; exact absurd h (not_terminates_ofStream s.get)
    · rfl

theorem terminates_toSeq_iff (t : Word α) : t.toSeq.Terminates ↔ t.IsFinite := by
  cases t with
  | fin w => exact iff_of_true (Stream'.Seq.terminates_ofList w) trivial
  | inf s => exact iff_of_false (not_terminates_ofStream _) id

end Silmaril.Proofs.Semantics.Streams
