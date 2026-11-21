module

public import Silmaril.Formats.Iroh.Defs
public import Silmaril.Formats.Bao.Thms

public section

namespace Silmaril.Proofs.Formats.Iroh

open Silmaril.Formats.Iroh
open Silmaril.Formats.Bao (Bytes Tape readHeader readSlots readSlots_spec readFrame_spec Span)

theorem readResponse_spec {query : Boundaries} {input rest : Bytes} {size : Nat}
    {fields : List Bytes} :
    readResponse query input = some (size, fields, rest) ↔
      readHeader input = some (size, fields.flatten ++ rest) ∧
      coverageBytes size query ≤ (fields.flatten ++ rest).length ∧
      Tape (responsePlan size query).preorder fields := by
  constructor
  · intro parsed
    cases header : readHeader input with
    | none => simp [readResponse, header] at parsed
    | some pair =>
      obtain ⟨claim, body⟩ := pair
      by_cases enough : coverageBytes claim query ≤ body.length
      · have enough' : ¬ coverageBytes claim query > body.length := by omega
        cases framed : readSlots (responsePlan claim query).preorder body with
        | none => simp [readResponse, header, enough', framed] at parsed
        | some pair =>
          obtain ⟨cells, tail⟩ := pair
          simp [readResponse, header, enough', framed] at parsed
          obtain ⟨rfl, rfl, rfl⟩ := parsed
          obtain ⟨tape, rfl⟩ := readSlots_spec.mp framed
          exact ⟨rfl, enough, tape⟩
      · have short : coverageBytes claim query > body.length := by omega
        simp [readResponse, header, short] at parsed
  · rintro ⟨header, enough, tape⟩
    have framed : readSlots (responsePlan size query).preorder (fields.flatten ++ rest) =
        some (fields, rest) := readSlots_spec.mpr ⟨tape, rfl⟩
    have enough' : coverageBytes size query ≤ (fields.map List.length).sum + rest.length :=
      by simpa using enough
    simp [readResponse, header, framed, enough']

theorem readMemory_spec {root : Hash} {size : Nat} {order : Order} {body : Bytes}
    {fields : List Bytes} :
    readMemory root size order body = some ⟨root, size, order, fields⟩ ↔
      size < Silmaril.Formats.Bao.u64Limit ∧ body.length = outboardSize size ∧
      Tape (outboardLayout order size) fields ∧ body = fields.flatten := by
  by_cases inRange : size < Silmaril.Formats.Bao.u64Limit
  · have notLarge : ¬size ≥ Silmaril.Formats.Bao.u64Limit := by omega
    by_cases lengthEq : body.length = outboardSize size
    · simp [readMemory, notLarge, inRange, lengthEq, Option.bind_eq_some_iff, readFrame_spec]
    · simp [readMemory, lengthEq]
  · have large : size ≥ Silmaril.Formats.Bao.u64Limit := by omega
    simp [readMemory, large, inRange]

theorem readTrailer_spec {input body : Bytes} {size : Nat} :
    readTrailer input = some (size, body) ↔
      ∃ header : Bytes, header.length = 8 ∧ Silmaril.Formats.Bao.getLE header = size ∧
        input = body ++ header := by
  constructor
  · intro parsed
    cases trailer : Silmaril.Formats.Bao.takeExact 8 input.reverse with
    | none => simp [readTrailer, trailer] at parsed
    | some pair =>
      obtain ⟨head, tail⟩ := pair
      simp [readTrailer, trailer] at parsed
      obtain ⟨width, whole⟩ := Silmaril.Formats.Bao.takeExact_spec.mp trailer
      exact ⟨head.reverse, by simpa using width, parsed.1,
        by simpa [parsed.2] using congrArg List.reverse whole⟩
  · rintro ⟨header, width, sizeEq, rfl⟩
    have trailer : Silmaril.Formats.Bao.takeExact 8 (body ++ header).reverse =
        some (header.reverse, body.reverse) :=
      Silmaril.Formats.Bao.takeExact_spec.mpr ⟨by simpa using width, List.reverse_append⟩
    rw [readTrailer, trailer]
    simp [sizeEq]

end Silmaril.Proofs.Formats.Iroh
