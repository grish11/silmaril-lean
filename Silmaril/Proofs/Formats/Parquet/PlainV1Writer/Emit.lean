module

public import Silmaril.Formats.Parquet.PlainV1Writer.Defs
import Silmaril.Proofs.Formats.Parquet.PlainV1Writer.Body

public section

namespace Silmaril.Proofs.Formats.Parquet.PlainV1Writer

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.PlainV1Writer

theorem emit_exact {limits : Limits} {input : Input} {page : Encoded}
    (written : emit limits input = .ok page) :
    input.Fits limits ∧ page.headerBytes.length ≤ limits.headerBytes ∧
      page.header = input.header ∧ page.body = input.body ∧
      Page.readHeaderPrefix limits.header page.wire = .ok (page.header, page.headerBytes.length) ∧
      page.header.compressedSize = page.body.length ∧ page.header.uncompressedSize = page.body.length ∧
      page.wire.length = page.headerBytes.length + page.body.length := by
  by_cases fits : input.Fits limits
  · cases encoded : encodeHeader input.numValues input.bodySize with
    | none => simp [emit, fits, encoded] at written
    | some headerBytes =>
      by_cases bounded : headerBytes.length ≤ limits.headerBytes
      · let candidate : Encoded := ⟨input.header, headerBytes, input.body⟩
        cases checked : Page.readHeaderPrefix limits.header candidate.wire with
        | error error => simp [emit, fits, encoded, Nat.not_lt.mpr bounded, candidate, checked] at written
        | ok parsed =>
          simp only [emit, fits, ite_true, encoded, Nat.not_lt.mpr bounded, ite_false] at written
          change (match Page.readHeaderPrefix limits.header candidate.wire with
            | .error error => Except.error (Error.header error)
            | .ok result => if result = (candidate.header, headerBytes.length) then Except.ok candidate
                else Except.error Error.headerMismatch) = Except.ok page at written
          rw [checked] at written
          change (if parsed = (candidate.header, headerBytes.length) then Except.ok candidate
            else Except.error Error.headerMismatch) = Except.ok page at written
          by_cases equal : parsed = (candidate.header, headerBytes.length)
          · simp only [equal, ite_true] at written
            have same := Except.ok.inj written
            subst page
            exact ⟨fits, bounded, rfl, rfl, checked.trans (congrArg Except.ok equal),
              (body_length input).symm, (body_length input).symm, Bytes.length_append _ _⟩
          · simp [equal] at written
      · simp [emit, fits, encoded, Nat.lt_of_not_ge bounded] at written
  · simp [emit, fits] at written

end Silmaril.Proofs.Formats.Parquet.PlainV1Writer
