module

public import Silmaril.Logic.SAT.Carrier.Thms

/-!
# Examples: the word carriers, their malformed inputs, and the acceptors

All by kernel evaluation (`decide`).

* **Empty versus malformed.** The empty nested input `[]` and the empty stream `[]` are the
  empty formula (satisfiable, accepted by the SAT acceptors with the empty model:
  `empty_nested_sat`, `empty_stream_sat`); `[[]]` and the stream `[0]` are the formula with one
  empty clause (unsatisfiable: `emptyClause_nested_unsat`, `emptyClause_stream_unsat`). A nested
  `0` (`[[0]]`, `[[1, 0, 2]]`), `Int32.MIN`, and an unterminated stream (`[1]`, `[1, 0, 2]`) are
  malformed (`none`), not empty (`malformed_*`).
* **Nested zero versus stream zero.** `[[1, 0, 2]]` is malformed nested input, while its
  flattening `[1, 0, 2, 0]` is the stream of `[[1], [2]]` (`flatten_split`).
* **LRAT.** The existing refutations of the four clauses over two variables
  (`LRAT.fourClausesProof`, RUP; `LRAT.fourClausesRatProof`, with RAT steps) as certificate
  streams (`fourCert`, `fourRatCert`) are decoded back exactly (`fourCert_decode`,
  `fourRatCert_decode`) and accepted with both problem carriers (`four_nested_accepted`,
  `four_stream_accepted`, `fourRat_nested_accepted`), so both problems are in the UNSAT
  languages. A bogus certificate and a malformed one are rejected.
* **SAT.** `satTwo = [[1, 2], [-1, 2]]` is accepted with the model `[2]` and rejected with the
  inconsistent `[2, -2]`, the incomplete `[1]`, and a model containing `0`.
-/

@[expose] public section

namespace Silmaril.Logic.SAT.Carrier.Examples

open Silmaril.Logic.SAT

/-! ## Empty, empty clause, malformed -/

theorem decode_empty_nested : decodeNested [] = some [] := by decide
theorem decode_empty_stream : decodeStream [] = some [] := by decide
theorem decode_emptyClause_nested : decodeNested [[]] = some [[]] := by decide
theorem decode_emptyClause_stream : decodeStream [0] = some [[]] := by decide

theorem malformed_nested_zero : decodeNested [[0]] = none := by decide
theorem malformed_nested_inner_zero : decodeNested [[1, 0, 2]] = none := by decide
theorem malformed_nested_intMin : decodeNested [[BitVec.intMin 32]] = none := by decide
theorem malformed_stream_unterminated : decodeStream [1] = none := by decide
theorem malformed_stream_tail : decodeStream [1, 0, 2] = none := by decide
theorem malformed_stream_intMin : decodeStream [BitVec.intMin 32, 0] = none := by decide

/-- The largest literals are accepted: `±(2³¹ - 1)`. -/
theorem decode_extremes :
    decodeNested [[0x7fffffff, 0x80000001]] = some [[2147483647, -2147483647]] := by decide

theorem flatten_split : flatten [[1, 0, 2]] = [1, 0, 2, 0] ∧
    decodeStream [1, 0, 2, 0] = some [[1], [2]] := by decide

theorem empty_nested_sat : satNested [] [] = true := by decide
theorem empty_stream_sat : satStream [] [] = true := by decide

theorem emptyClause_nested_unsat : [[]] ∈ UnsatNested :=
  ⟨[[]], decode_emptyClause_nested, fun _ => rfl⟩
theorem emptyClause_stream_unsat : [0] ∈ UnsatStream :=
  ⟨[[]], decode_emptyClause_stream, fun _ => rfl⟩

theorem empty_nested_not_unsat : [] ∉ UnsatNested :=
  fun h => not_satNested_of_unsat h (satNested_sound ⟨[], empty_nested_sat⟩)

/-! ## LRAT certificates -/

/-- The four clauses over two variables, nested. -/
def four : Nested := encodeNested LRAT.fourClauses

/-- Its RUP refutation as a certificate stream. -/
def fourCert : List S32 := LratStream.encode LRAT.fourClausesProof

/-- Its refutation through RAT steps as a certificate stream. -/
def fourRatCert : List S32 := LratStream.encode LRAT.fourClausesRatProof

theorem fourCert_eq : fourCert = [1, 5, 2, 0, 1, 2, 0, 1, 6, 0, 5, 3, 4, 0] := by decide

theorem fourCert_decode : LratStream.decode fourCert = some LRAT.fourClausesProof := by decide
theorem fourRatCert_decode : LratStream.decode fourRatCert = some LRAT.fourClausesRatProof := by
  decide

theorem four_nested_accepted : lratNested four fourCert = true := by decide
theorem four_stream_accepted : lratStream (flatten four) fourCert = true := by decide
theorem fourRat_nested_accepted : lratNested four fourRatCert = true := by decide

theorem four_unsatNested : four ∈ UnsatNested := lratNested_sound ⟨_, four_nested_accepted⟩
theorem four_unsatStream : flatten four ∈ UnsatStream :=
  lratStream_sound ⟨_, four_stream_accepted⟩

theorem bogus_rejected : lratNested four [1, 5, 0, 1, 0] = false := by decide
/-- A certificate ending inside a step is malformed. -/
theorem truncated_rejected : LratStream.decode [1, 5, 2] = none := by decide
/-- An unknown tag is malformed. -/
theorem badTag_rejected : LratStream.decode [4, 5, 0] = none := by decide

/-! ## Models -/

theorem satTwo_accepted : satNested (encodeNested LRAT.satTwo) [2] = true := by decide
theorem satTwo_inconsistent : satNested (encodeNested LRAT.satTwo) [2, -2] = false := by decide
theorem satTwo_incomplete : satNested (encodeNested LRAT.satTwo) [1] = false := by decide
theorem satTwo_zero : satNested (encodeNested LRAT.satTwo) [2, 0] = false := by decide
theorem satTwo_stream_accepted : satStream (flatten (encodeNested LRAT.satTwo)) [2] = true := by
  decide

end Silmaril.Logic.SAT.Carrier.Examples
