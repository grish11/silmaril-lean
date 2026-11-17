module

public import Silmaril.Logic.SAT.Carrier.Defs
public import Silmaril.Logic.SAT.CNF.Thms
public import Silmaril.Logic.SAT.LRAT.Thms
public import Silmaril.Logic.Consequence.Gentzen.Clausal.Dimacs.Thms
import Silmaril.Proofs.Logic.SAT.Carrier.Basic
import Silmaril.Proofs.Logic.SAT.Carrier.LratStream

@[expose] public section

/-!
# CNF carriers of 32-bit words: results

Proofs in `Silmaril.Proofs.Logic.SAT.Carrier.{Basic,LratStream}`.

**Words.** `litWord_iff`: a word is a literal word exactly when its signed reading is a literal
in range (`x ≠ 0`, `x ≠ Int32.MIN`); `toInt_encodeLit`, `encodeLit_toInt`: words and
in-range integers are in bijection.

**Lossless readings.** With `CnfRange F` (every literal nonzero with `|l| < 2³¹`):

* `decodeNested_encode`, `decodeStream_encode`: a formula is read back from its words;
* `encodeNested_of_decode`, `encodeStream_of_decode`: a well-formed input is the encoding of
  the formula it reads as (decoding is injective, no information is lost);
* `cnfRange_of_decodeNested`, `cnfRange_of_decodeStream`: every formula read is in range.

**Malformed input.** `decodeNested_none_of_zero`: a `0` inside a clause makes the nested input
malformed; `decodeStream_eq_some` and `streamOk_iff` state the stream policy (`Int32.MIN`
anywhere, or a last clause without its `0`, is malformed). Malformed input is `none`, not the
empty formula (`…Carrier.Examples`).

**The two carriers.** `decodeStream_flatten`: a well-formed nested input reads as its flattened
stream; `decodeNested_of_decodeStream`: a well-formed stream has a well-formed nested form.
Hence `unsatNested_iff_stream`, `satNested_iff_stream`, `unsatStream_iff_nested`,
`satStream_iff_nested`. The converse of `decodeStream_flatten` fails: `[[1, 0, 2]]` is malformed
nested input, while its flattening `[1, 0, 2, 0]` is the stream of `[[1], [2]]`.

**The existing clausal lore** (`Silmaril.Consequence.Gentzen.Clausal`): `unsatNested_iff_cnfUnsat`,
`unsatStream_iff_cnfUnsat` (the languages through `CnfUnsat litSat`), `lratNested_lratAccepts`,
`lratStream_lratAccepts` (an accepted problem's formula is accepted by the existing CNF acceptor
`lratAccepts`), `modelOk_hits` (a checked model is a consistent hitting set, `Hits`).

**Acceptors.** Sound, as existential projections:

* **`lratNested_sound`**, **`lratStream_sound`**: `Accepts lratNested ⊆ UnsatNested`,
  `Accepts lratStream ⊆ UnsatStream` (`LRAT.check_sound`);
* **`satNested_sound`**, **`satStream_sound`**: `Accepts satNested ⊆ SatNested`,
  `Accepts satStream ⊆ SatStream`, from **`eval_of_modelOk`** (a checked model witness
  satisfies the formula under `modelAsg`);
* `not_satNested_of_unsat`, `not_satStream_of_unsat`: the UNSAT and SAT languages are disjoint.

No completeness is claimed for the acceptors. What is shown is that the certificate format
loses no representable LRAT proof: `LratStream.decode_encode` and `LratStream.encode_decode`
(lossless on `StepRange` steps, RUP, deletion and RAT), so `mem_accepts_lratNested` and
`mem_accepts_lratStream`: an in-range formula with an accepted, representable LRAT proof is
accepted.
-/

namespace Silmaril.Logic.SAT.Carrier

/-! ## Words -/

theorem litWord_iff (x : S32) : LitWord x = true ↔ LitRange x.toInt :=
  Proofs.Logic.SAT.Carrier.litWord_iff x

theorem toInt_encodeLit {l : Int} (h : InRange l) : (encodeLit l).toInt = l :=
  Proofs.Logic.SAT.Carrier.toInt_encodeLit h

theorem encodeLit_toInt (x : S32) : encodeLit x.toInt = x := BitVec.ofInt_toInt

/-! ## Readings -/

theorem decodeNested_eq_some {p : Nested} {F : CNF} :
    decodeNested p = some F ↔ p.all (·.all LitWord) = true ∧ F = p.map (·.map BitVec.toInt) :=
  Proofs.Logic.SAT.Carrier.decodeNested_eq_some

theorem decodeStream_eq_some {xs : Stream} {F : CNF} :
    decodeStream xs = some F ↔ StreamOk xs = true ∧ F = Dimacs.cnf (xs.map BitVec.toInt) :=
  Proofs.Logic.SAT.Carrier.decodeStream_eq_some

theorem streamOk_iff (xs : Stream) :
    StreamOk xs = true ↔ (∀ x ∈ xs, x ≠ BitVec.intMin 32) ∧
      Dimacs.pending (xs.map BitVec.toInt) = [] :=
  Proofs.Logic.SAT.Carrier.streamOk_iff xs

theorem decodeNested_none_of_zero {p : Nested} {c : List S32} (hc : c ∈ p) (h0 : (0 : S32) ∈ c) :
    decodeNested p = none :=
  Proofs.Logic.SAT.Carrier.decodeNested_none_of_zero hc h0

theorem cnfRange_of_decodeNested {p : Nested} {F : CNF} (h : decodeNested p = some F) :
    CnfRange F :=
  Proofs.Logic.SAT.Carrier.cnfRange_of_decodeNested h

theorem cnfRange_of_decodeStream {xs : Stream} {F : CNF} (h : decodeStream xs = some F) :
    CnfRange F :=
  Proofs.Logic.SAT.Carrier.cnfRange_of_decodeStream h

theorem decodeNested_encode {F : CNF} (h : CnfRange F) : decodeNested (encodeNested F) = some F :=
  Proofs.Logic.SAT.Carrier.decodeNested_encode h

theorem encodeNested_of_decode {p : Nested} {F : CNF} (h : decodeNested p = some F) :
    encodeNested F = p :=
  Proofs.Logic.SAT.Carrier.encodeNested_of_decode h

theorem decodeStream_encode {F : CNF} (h : CnfRange F) : decodeStream (encodeStream F) = some F :=
  Proofs.Logic.SAT.Carrier.decodeStream_encode h

theorem encodeStream_of_decode {xs : Stream} {F : CNF} (h : decodeStream xs = some F) :
    encodeStream F = xs :=
  Proofs.Logic.SAT.Carrier.encodeStream_of_decode h

/-- The DIMACS reader leaves the stream split into written clauses and pending literals. -/
theorem write_cnf_append_pending (ys : List Int) :
    Dimacs.write (Dimacs.cnf ys) ++ Dimacs.pending ys = ys :=
  Proofs.Logic.SAT.Carrier.write_cnf_append_pending ys

/-! ## The two carriers -/

theorem decodeStream_flatten {p : Nested} {F : CNF} (h : decodeNested p = some F) :
    decodeStream (flatten p) = some F :=
  Proofs.Logic.SAT.Carrier.decodeStream_flatten h

theorem decodeNested_of_decodeStream {xs : Stream} {F : CNF} (h : decodeStream xs = some F) :
    decodeNested (encodeNested F) = some F :=
  Proofs.Logic.SAT.Carrier.decodeNested_of_decodeStream h

theorem unsatNested_iff_stream (p : Nested) :
    p ∈ UnsatNested ↔ (decodeNested p).isSome ∧ flatten p ∈ UnsatStream :=
  Proofs.Logic.SAT.Carrier.unsatNested_iff_stream p

theorem satNested_iff_stream (p : Nested) :
    p ∈ SatNested ↔ (decodeNested p).isSome ∧ flatten p ∈ SatStream :=
  Proofs.Logic.SAT.Carrier.satNested_iff_stream p

theorem unsatStream_iff_nested (xs : Stream) :
    xs ∈ UnsatStream ↔ ∃ F, decodeStream xs = some F ∧ encodeNested F ∈ UnsatNested :=
  Proofs.Logic.SAT.Carrier.unsatStream_iff_nested xs

theorem satStream_iff_nested (xs : Stream) :
    xs ∈ SatStream ↔ ∃ F, decodeStream xs = some F ∧ encodeNested F ∈ SatNested :=
  Proofs.Logic.SAT.Carrier.satStream_iff_nested xs

theorem not_satNested_of_unsat {p : Nested} (h : p ∈ UnsatNested) : p ∉ SatNested :=
  Proofs.Logic.SAT.Carrier.not_satNested_of_unsat h

theorem not_satStream_of_unsat {xs : Stream} (h : xs ∈ UnsatStream) : xs ∉ SatStream :=
  Proofs.Logic.SAT.Carrier.not_satStream_of_unsat h

/-! ## Acceptors -/

theorem lratNested_iff (p : Nested) (c : List S32) :
    lratNested p c = true ↔
      ∃ F ss, decodeNested p = some F ∧ LratStream.decode c = some ss ∧ LRAT.check F ss = true :=
  Proofs.Logic.SAT.Carrier.lratNested_iff p c

theorem lratStream_iff (xs : Stream) (c : List S32) :
    lratStream xs c = true ↔
      ∃ F ss, decodeStream xs = some F ∧ LratStream.decode c = some ss ∧ LRAT.check F ss = true :=
  Proofs.Logic.SAT.Carrier.lratStream_iff xs c

/-- **The nested LRAT acceptor is sound** for the nested UNSAT language. -/
theorem lratNested_sound : Accepts lratNested ⊆ UnsatNested :=
  Proofs.Logic.SAT.Carrier.lratNested_sound

/-- **The stream LRAT acceptor is sound** for the stream UNSAT language. -/
theorem lratStream_sound : Accepts lratStream ⊆ UnsatStream :=
  Proofs.Logic.SAT.Carrier.lratStream_sound

theorem modelOk_iff (F : CNF) (m : List S32) :
    modelOk F m = true ↔ (∀ x ∈ m, LitWord x = true) ∧
      (∀ l ∈ m.map BitVec.toInt, -l ∉ m.map BitVec.toInt) ∧
      ∀ C ∈ F, ∃ l ∈ C, l ∈ m.map BitVec.toInt :=
  Proofs.Logic.SAT.Carrier.modelOk_iff F m

/-- **A checked model witness satisfies the formula.** -/
theorem eval_of_modelOk {F : CNF} {m : List S32} (h : modelOk F m = true) :
    F.eval (modelAsg m) = true :=
  Proofs.Logic.SAT.Carrier.eval_of_modelOk h

/-- **The nested SAT acceptor is sound** for the nested SAT language. -/
theorem satNested_sound : Accepts satNested ⊆ SatNested :=
  Proofs.Logic.SAT.Carrier.satNested_sound

/-- **The stream SAT acceptor is sound** for the stream SAT language. -/
theorem satStream_sound : Accepts satStream ⊆ SatStream :=
  Proofs.Logic.SAT.Carrier.satStream_sound

/-! ## The certificate stream -/

theorem LratStream.decode_encode {ss : List LRAT.Step} (h : ∀ s ∈ ss, LratStream.StepRange s) :
    LratStream.decode (LratStream.encode ss) = some ss :=
  Proofs.Logic.SAT.Carrier.LratStream.decode_encode h

theorem LratStream.encode_decode {xs : List S32} {ss : List LRAT.Step}
    (h : LratStream.decode xs = some ss) : LratStream.encode ss = xs :=
  Proofs.Logic.SAT.Carrier.LratStream.encode_decode h

theorem LratStream.stepRange_of_decode {xs : List S32} {ss : List LRAT.Step}
    (h : LratStream.decode xs = some ss) : ∀ s ∈ ss, LratStream.StepRange s :=
  Proofs.Logic.SAT.Carrier.LratStream.stepRange_of_decode h

/-- An in-range formula with an accepted representable LRAT proof is accepted (nested). -/
theorem mem_accepts_lratNested {F : CNF} {ss : List LRAT.Step} (hF : CnfRange F)
    (hs : ∀ s ∈ ss, LratStream.StepRange s) (h : LRAT.check F ss = true) :
    encodeNested F ∈ Accepts lratNested :=
  ⟨LratStream.encode ss, (lratNested_iff _ _).2 ⟨F, ss, decodeNested_encode hF,
    LratStream.decode_encode hs, h⟩⟩

/-- An in-range formula with an accepted representable LRAT proof is accepted (stream). -/
theorem mem_accepts_lratStream {F : CNF} {ss : List LRAT.Step} (hF : CnfRange F)
    (hs : ∀ s ∈ ss, LratStream.StepRange s) (h : LRAT.check F ss = true) :
    encodeStream F ∈ Accepts lratStream :=
  ⟨LratStream.encode ss, (lratStream_iff _ _).2 ⟨F, ss, decodeStream_encode hF,
    LratStream.decode_encode hs, h⟩⟩

/-! ## The existing clausal lore -/

open Silmaril.Consequence.Gentzen.Clausal (CnfUnsat litSat lratAccepts Hits cnfUnsat_litSat_iff)

theorem unsatNested_iff_cnfUnsat (p : Nested) :
    p ∈ UnsatNested ↔ ∃ F, decodeNested p = some F ∧ CnfUnsat litSat F :=
  exists_congr fun _ => and_congr_right fun _ => cnfUnsat_litSat_iff.symm

theorem unsatStream_iff_cnfUnsat (xs : Stream) :
    xs ∈ UnsatStream ↔ ∃ F, decodeStream xs = some F ∧ CnfUnsat litSat F :=
  exists_congr fun _ => and_congr_right fun _ => cnfUnsat_litSat_iff.symm

/-- An accepted nested problem reads as a formula that the existing CNF acceptor
`lratAccepts` accepts. -/
theorem lratNested_lratAccepts {p : Nested} (h : p ∈ Accepts lratNested) :
    ∃ F, decodeNested p = some F ∧ lratAccepts F := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨F, ss, hF, _, hck⟩ := (lratNested_iff p c).1 hc
  exact ⟨F, hF, ss, hck⟩

/-- An accepted stream reads as a formula that `lratAccepts` accepts. -/
theorem lratStream_lratAccepts {xs : Stream} (h : xs ∈ Accepts lratStream) :
    ∃ F, decodeStream xs = some F ∧ lratAccepts F := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨F, ss, hF, _, hck⟩ := (lratStream_iff xs c).1 hc
  exact ⟨F, hF, ss, hck⟩

/-- A checked model is a consistent hitting set of the formula (`Clausal.Hits`). -/
theorem modelOk_hits {F : CNF} {m : List S32} (h : modelOk F m = true) :
    Hits (m.map BitVec.toInt) F :=
  ((modelOk_iff F m).1 h).2.2

end Silmaril.Logic.SAT.Carrier
