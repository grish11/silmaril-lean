module

public import Silmaril.Project.Shapes.Language.Thms
public import ProjectSelfTest.Languages
public import ProjectSelfTest.FormatExamples

/-!
# Relations between catalogue languages (inclusions, with counterexamples)

The format languages and their membership examples are registered in
`ProjectSelfTest.FormatExamples` (generated) and the baseline JSON, UTF-8 and well-formed CBOR
languages in `ProjectSelfTest.Languages`. This module adds the two languages those leave out
(the RFC 8259 number-token language and DRISL without floats), a few membership examples for
them, and the **relations** between the languages, as `silmaril.shapes.language.subset_at`
problems over the registered definitions:

* `THM` answers: inclusions, each the merged library theorem (named in the doc);
* `CSA` answers: non-inclusions, each with the witness the answer records.

Every claim is a theorem: there is no row without a proof. Scope notes kept in the titles:
`safeInteger` is only I-JSON's integer range (not I-JSON); the Python spellings are not JSON;
`atprotoCoreExactCid` is the CBOR-level core of the atproto data model (no floats, signed
64-bit integers, DASL CIDs), not atproto record validation; the DRISL CID rules pair codecs
`55, 71` with the (multihash, length) pairs `(12, 32)` for DASL and `(12, 32), (1E, 32)` for
BDASL (`Silmaril.Formats.Cbor.Drisl.LinkRule`).
-/

namespace Silmaril.Project.Languages.Catalogue

@[expose] public section

/-- RFC 8259 §6 number tokens (`Silmaril.Formats.JsonNumbers.rfc`). -/
def jsonNumberRfc : Set (List UInt8) := Silmaril.Formats.JsonNumbers.rfc
/-- DRISL without floats, DASL CIDs, exact CID boundary
(`Silmaril.Formats.Cbor.Drisl.language .drislNoFloatsExactCid`). -/
def drislNoFloatsExactCid : Set (List UInt8) :=
  Silmaril.Formats.Cbor.Drisl.language .drislNoFloatsExactCid

end

end Silmaril.Project.Languages.Catalogue

silmaril language formats.json.numbers.rfc := Silmaril.Project.Languages.Catalogue.jsonNumberRfc
  (domain := bytes) (op := decl) (title := "RFC 8259 number tokens") (source := rfc8259)
  (doc := "The number rule of RFC 8259 §6: [ minus ] int [ frac ] [ exp ]; no range or precision limit")
silmaril language formats.cbor.drisl.language_drisl_no_floats_exact_cid :=
  Silmaril.Project.Languages.Catalogue.drislNoFloatsExactCid (domain := bytes) (op := decl)
  (title := "DRISL without floats (DASL CIDs, exact CID boundary)") (source := drisl)
  (doc := "Profile.drislNoFloatsExactCid: DRISL with major type 7 floats excluded; CIDs: codecs 55, 71 with (multihash 12, 32 bytes)")

open Silmaril.Project.Shapes in
section

silmaril instance formats.catalogue.json_number_rfc_1e2 (expect := THM) (title := "\"1e2\".toUTF8.toList ∈ RFC 8259 number tokens") :=
  silmaril.shapes.language.member (L := Silmaril.Project.Languages.Catalogue.jsonNumberRfc) (x := ("1e2".toUTF8.toList : List UInt8))

@[answers "formats.catalogue.json_number_rfc_1e2" thm]
public theorem catalogue_json_number_rfc_1e2 : Member Silmaril.Project.Languages.Catalogue.jsonNumberRfc ("1e2".toUTF8.toList : List UInt8) :=
  (show ("1e2".toUTF8.toList : List UInt8) ∈ Silmaril.Project.Languages.Catalogue.jsonNumberRfc from (by decide +kernel : ("1e2".toUTF8.toList : List UInt8) ∈ Silmaril.Formats.JsonNumbers.rfc))

silmaril instance formats.catalogue.json_number_rfc_inf (expect := CSA) (title := "\"Infinity\".toUTF8.toList ∉ RFC 8259 number tokens") :=
  silmaril.shapes.language.member (L := Silmaril.Project.Languages.Catalogue.jsonNumberRfc) (x := ("Infinity".toUTF8.toList : List UInt8))

@[answers "formats.catalogue.json_number_rfc_inf" csa]
public theorem catalogue_json_number_rfc_inf : ¬ Member Silmaril.Project.Languages.Catalogue.jsonNumberRfc ("Infinity".toUTF8.toList : List UInt8) :=
  (show ("Infinity".toUTF8.toList : List UInt8) ∉ Silmaril.Project.Languages.Catalogue.jsonNumberRfc from (by decide +kernel : ("Infinity".toUTF8.toList : List UInt8) ∉ Silmaril.Formats.JsonNumbers.rfc))

silmaril instance formats.catalogue.json_number_rfc_leading_zero (expect := CSA) (title := "\"01\".toUTF8.toList ∉ RFC 8259 number tokens") :=
  silmaril.shapes.language.member (L := Silmaril.Project.Languages.Catalogue.jsonNumberRfc) (x := ("01".toUTF8.toList : List UInt8))

@[answers "formats.catalogue.json_number_rfc_leading_zero" csa]
public theorem catalogue_json_number_rfc_leading_zero : ¬ Member Silmaril.Project.Languages.Catalogue.jsonNumberRfc ("01".toUTF8.toList : List UInt8) :=
  (show ("01".toUTF8.toList : List UInt8) ∉ Silmaril.Project.Languages.Catalogue.jsonNumberRfc from (by decide +kernel : ("01".toUTF8.toList : List UInt8) ∉ Silmaril.Formats.JsonNumbers.rfc))

silmaril instance formats.catalogue.drisl_no_floats_int (expect := THM) (title := "[0x01] ∈ DRISL without floats") :=
  silmaril.shapes.language.member (L := Silmaril.Project.Languages.Catalogue.drislNoFloatsExactCid) (x := ([0x01] : List UInt8))

@[answers "formats.catalogue.drisl_no_floats_int" thm]
public theorem catalogue_drisl_no_floats_int : Member Silmaril.Project.Languages.Catalogue.drislNoFloatsExactCid ([0x01] : List UInt8) :=
  (show ([0x01] : List UInt8) ∈ Silmaril.Project.Languages.Catalogue.drislNoFloatsExactCid from (by decide +kernel : ([0x01] : List UInt8) ∈ Silmaril.Formats.Cbor.Drisl.language .drislNoFloatsExactCid))

silmaril instance formats.catalogue.drisl_no_floats_float (expect := CSA) (title := "[0xFB, 0x3F, 0xF0, 0, 0, 0, 0, 0, 0] ∉ DRISL without floats") :=
  silmaril.shapes.language.member (L := Silmaril.Project.Languages.Catalogue.drislNoFloatsExactCid) (x := ([0xFB, 0x3F, 0xF0, 0, 0, 0, 0, 0, 0] : List UInt8))

@[answers "formats.catalogue.drisl_no_floats_float" csa]
public theorem catalogue_drisl_no_floats_float : ¬ Member Silmaril.Project.Languages.Catalogue.drislNoFloatsExactCid ([0xFB, 0x3F, 0xF0, 0, 0, 0, 0, 0, 0] : List UInt8) :=
  (show ([0xFB, 0x3F, 0xF0, 0, 0, 0, 0, 0, 0] : List UInt8) ∉ Silmaril.Project.Languages.Catalogue.drislNoFloatsExactCid from (by decide +kernel : ([0xFB, 0x3F, 0xF0, 0, 0, 0, 0, 0, 0] : List UInt8) ∉ Silmaril.Formats.Cbor.Drisl.language .drislNoFloatsExactCid))

silmaril instance formats.catalogue.drisl_no_floats_uint_2_63 (expect := THM) (title := "[0x1B, 0x80, 0, 0, 0, 0, 0, 0, 0] ∈ DRISL without floats") :=
  silmaril.shapes.language.member (L := Silmaril.Project.Languages.Catalogue.drislNoFloatsExactCid) (x := ([0x1B, 0x80, 0, 0, 0, 0, 0, 0, 0] : List UInt8))

@[answers "formats.catalogue.drisl_no_floats_uint_2_63" thm]
public theorem catalogue_drisl_no_floats_uint_2_63 : Member Silmaril.Project.Languages.Catalogue.drislNoFloatsExactCid ([0x1B, 0x80, 0, 0, 0, 0, 0, 0, 0] : List UInt8) :=
  (show ([0x1B, 0x80, 0, 0, 0, 0, 0, 0, 0] : List UInt8) ∈ Silmaril.Project.Languages.Catalogue.drislNoFloatsExactCid from (by decide +kernel : ([0x1B, 0x80, 0, 0, 0, 0, 0, 0, 0] : List UInt8) ∈ Silmaril.Formats.Cbor.Drisl.language .drislNoFloatsExactCid))

silmaril instance formats.relations.ascii_printable_sub_ascii (expect := THM) (title := "Printable ASCII ⊆ ASCII")
  (doc := "Silmaril.Formats.Ascii.printable_le") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.Ascii.lang1) (K := Silmaril.Project.Languages.FormatExamples.Ascii.lang0)

@[answers "formats.relations.ascii_printable_sub_ascii" thm]
public theorem relation_ascii_printable_sub_ascii : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.Ascii.lang1 Silmaril.Project.Languages.FormatExamples.Ascii.lang0 x :=
  fun _ h => Silmaril.Formats.Ascii.printable_le h

silmaril instance formats.relations.ascii_sub_utf8 (expect := THM) (title := "ASCII ⊆ UTF-8")
  (doc := "Silmaril.Formats.Ascii.language_le_utf8") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.Ascii.lang0) (K := ProjectSelfTest.Languages.utf8)

@[answers "formats.relations.ascii_sub_utf8" thm]
public theorem relation_ascii_sub_utf8 : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.Ascii.lang0 ProjectSelfTest.Languages.utf8 x :=
  fun _ h => Silmaril.Formats.Ascii.language_le_utf8 h

silmaril instance formats.relations.ascii_json_sub_json (expect := THM) (title := "ASCII-only JSON ⊆ JSON (RFC 8259)")
  (doc := "Silmaril.Formats.Ascii.json_le") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.Ascii.lang2) (K := ProjectSelfTest.Languages.jsonRfc8259)

@[answers "formats.relations.ascii_json_sub_json" thm]
public theorem relation_ascii_json_sub_json : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.Ascii.lang2 ProjectSelfTest.Languages.jsonRfc8259 x :=
  fun _ h => Silmaril.Formats.Ascii.json_le .rfc8259 h

silmaril instance formats.relations.ascii_json_sub_ascii (expect := THM) (title := "ASCII-only JSON ⊆ ASCII")
  (doc := "Silmaril.Formats.Ascii.json_le_ascii") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.Ascii.lang2) (K := Silmaril.Project.Languages.FormatExamples.Ascii.lang0)

@[answers "formats.relations.ascii_json_sub_ascii" thm]
public theorem relation_ascii_json_sub_ascii : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.Ascii.lang2 Silmaril.Project.Languages.FormatExamples.Ascii.lang0 x :=
  fun _ h => Silmaril.Formats.Ascii.json_le_ascii .rfc8259 h

silmaril instance formats.relations.json_int_token_sub_integral (expect := THM) (title := "Lexical integer tokens ⊆ integral-valued number tokens")
  (doc := "Silmaril.Formats.JsonNumbers.integerToken_le_integralNumber") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang7) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang1)

@[answers "formats.relations.json_int_token_sub_integral" thm]
public theorem relation_json_int_token_sub_integral : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang7 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang1 x :=
  fun _ h => Silmaril.Formats.JsonNumbers.integerToken_le_integralNumber h

silmaril instance formats.relations.json_integral_sub_rfc (expect := THM) (title := "Integral-valued number tokens ⊆ RFC 8259 numbers")
  (doc := "Silmaril.Formats.JsonNumbers.integralNumber_le_rfc") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang1) (K := Silmaril.Project.Languages.Catalogue.jsonNumberRfc)

@[answers "formats.relations.json_integral_sub_rfc" thm]
public theorem relation_json_integral_sub_rfc : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang1 Silmaril.Project.Languages.Catalogue.jsonNumberRfc x :=
  fun _ h => Silmaril.Formats.JsonNumbers.integralNumber_le_rfc h

silmaril instance formats.relations.json_int_token_sub_rfc (expect := THM) (title := "Lexical integer tokens ⊆ RFC 8259 numbers")
  (doc := "Silmaril.Formats.JsonNumbers.integerToken_le_rfc") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang7) (K := Silmaril.Project.Languages.Catalogue.jsonNumberRfc)

@[answers "formats.relations.json_int_token_sub_rfc" thm]
public theorem relation_json_int_token_sub_rfc : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang7 Silmaril.Project.Languages.Catalogue.jsonNumberRfc x :=
  fun _ h => Silmaril.Formats.JsonNumbers.integerToken_le_rfc h

silmaril instance formats.relations.json_safe_sub_int64 (expect := THM) (title := "I-JSON safe-range integers ⊆ int64 integers")
  (doc := "Silmaril.Formats.JsonNumbers.safeInteger_le_int64") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang4) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang2)

@[answers "formats.relations.json_safe_sub_int64" thm]
public theorem relation_json_safe_sub_int64 : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang4 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang2 x :=
  fun _ h => Silmaril.Formats.JsonNumbers.safeInteger_le_int64 h

silmaril instance formats.relations.json_safe_sub_binary64 (expect := THM) (title := "I-JSON safe-range integers ⊆ binary64-exact integers")
  (doc := "Silmaril.Formats.JsonNumbers.safeInteger_le_binary64Integer") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang4) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang3)

@[answers "formats.relations.json_safe_sub_binary64" thm]
public theorem relation_json_safe_sub_binary64 : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang4 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang3 x :=
  fun _ h => Silmaril.Formats.JsonNumbers.safeInteger_le_binary64Integer h

silmaril instance formats.relations.json_int64_sub_int_token (expect := THM) (title := "int64 integers ⊆ lexical integer tokens")
  (doc := "Silmaril.Formats.JsonNumbers.int64_le_integerToken") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang2) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang7)

@[answers "formats.relations.json_int64_sub_int_token" thm]
public theorem relation_json_int64_sub_int_token : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang2 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang7 x :=
  fun _ h => Silmaril.Formats.JsonNumbers.int64_le_integerToken h

silmaril instance formats.relations.json_uint64_sub_int_token (expect := THM) (title := "uint64 integers ⊆ lexical integer tokens")
  (doc := "Silmaril.Formats.JsonNumbers.uint64_le_integerToken") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang0) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang7)

@[answers "formats.relations.json_uint64_sub_int_token" thm]
public theorem relation_json_uint64_sub_int_token : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang0 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang7 x :=
  fun _ h => Silmaril.Formats.JsonNumbers.uint64_le_integerToken h

silmaril instance formats.relations.json_binary64_sub_int_token (expect := THM) (title := "binary64-exact integers ⊆ lexical integer tokens")
  (doc := "Silmaril.Formats.JsonNumbers.binary64Integer_le_integerToken") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang3) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang7)

@[answers "formats.relations.json_binary64_sub_int_token" thm]
public theorem relation_json_binary64_sub_int_token : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang3 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang7 x :=
  fun _ h => Silmaril.Formats.JsonNumbers.binary64Integer_le_integerToken h

silmaril instance formats.relations.json_rfc_sub_python_infinity (expect := THM) (title := "RFC 8259 numbers ⊆ RFC + Python Infinity/-Infinity (not JSON)")
  (doc := "Silmaril.Formats.JsonNumbers.rfc_le_withPythonInfinity") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.Catalogue.jsonNumberRfc) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang5)

@[answers "formats.relations.json_rfc_sub_python_infinity" thm]
public theorem relation_json_rfc_sub_python_infinity : ∀ x, SubsetAt Silmaril.Project.Languages.Catalogue.jsonNumberRfc Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang5 x :=
  fun _ h => Silmaril.Formats.JsonNumbers.rfc_le_withPythonInfinity h

silmaril instance formats.relations.json_python_infinity_sub_nonfinite (expect := THM) (title := "RFC + Python Infinity ⊆ RFC + Python Infinity/NaN (not JSON)")
  (doc := "Silmaril.Formats.JsonNumbers.withPythonInfinity_le_withPythonNonFinite") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang5) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang6)

@[answers "formats.relations.json_python_infinity_sub_nonfinite" thm]
public theorem relation_json_python_infinity_sub_nonfinite : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang5 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang6 x :=
  fun _ h => Silmaril.Formats.JsonNumbers.withPythonInfinity_le_withPythonNonFinite h

silmaril instance formats.relations.json_text_int_token_sub_integral (expect := THM) (title := "JSON with lexical integers only ⊆ JSON with integral values only")
  (doc := "Silmaril.Formats.JsonNumbers.integerToken_text_le_integralNumber") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang9) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang10)

@[answers "formats.relations.json_text_int_token_sub_integral" thm]
public theorem relation_json_text_int_token_sub_integral : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang9 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang10 x :=
  fun _ h => Silmaril.Formats.JsonNumbers.integerToken_text_le_integralNumber .rfc8259 h

silmaril instance formats.relations.json_text_int64_sub_int_token (expect := THM) (title := "JSON with int64 integers only ⊆ JSON with lexical integers only")
  (doc := "Silmaril.Formats.JsonNumbers.int64_text_le") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang8) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang9)

@[answers "formats.relations.json_text_int64_sub_int_token" thm]
public theorem relation_json_text_int64_sub_int_token : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang8 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang9 x :=
  fun _ h => Silmaril.Formats.JsonNumbers.int64_text_le .rfc8259 h

silmaril instance formats.relations.json_text_binary64_sub_int_token (expect := THM) (title := "JSON with binary64-exact integers only ⊆ JSON with lexical integers only")
  (doc := "Silmaril.Formats.JsonNumbers.binary64Integer_text_le") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang11) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang9)

@[answers "formats.relations.json_text_binary64_sub_int_token" thm]
public theorem relation_json_text_binary64_sub_int_token : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang11 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang9 x :=
  fun _ h => Silmaril.Formats.JsonNumbers.binary64Integer_text_le .rfc8259 h

silmaril instance formats.relations.json_text_integral_sub_json (expect := THM) (title := "JSON with integral values only ⊆ JSON (RFC 8259)")
  (doc := "Silmaril.Formats.JsonNumbers.integralNumber_text_le") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang10) (K := ProjectSelfTest.Languages.jsonRfc8259)

@[answers "formats.relations.json_text_integral_sub_json" thm]
public theorem relation_json_text_integral_sub_json : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang10 ProjectSelfTest.Languages.jsonRfc8259 x :=
  fun _ h => Silmaril.Formats.JsonNumbers.integralNumber_text_le .rfc8259 h

silmaril instance formats.relations.json_sub_python_infinity_text (expect := THM) (title := "JSON (RFC 8259) ⊆ JSON + Python Infinity (not JSON)")
  (doc := "Silmaril.Formats.JsonNumbers.json_le_withPythonInfinity") := silmaril.shapes.language.subset_at
  (L := ProjectSelfTest.Languages.jsonRfc8259) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang14)

@[answers "formats.relations.json_sub_python_infinity_text" thm]
public theorem relation_json_sub_python_infinity_text : ∀ x, SubsetAt ProjectSelfTest.Languages.jsonRfc8259 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang14 x :=
  fun _ h => Silmaril.Formats.JsonNumbers.json_le_withPythonInfinity .rfc8259 h

silmaril instance formats.relations.json_python_infinity_text_sub_nonfinite (expect := THM) (title := "JSON + Python Infinity ⊆ JSON + Python Infinity/NaN (not JSON)")
  (doc := "Silmaril.Formats.JsonNumbers.withPythonInfinity_text_le") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang14) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang13)

@[answers "formats.relations.json_python_infinity_text_sub_nonfinite" thm]
public theorem relation_json_python_infinity_text_sub_nonfinite : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang14 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang13 x :=
  fun _ h => Silmaril.Formats.JsonNumbers.withPythonInfinity_text_le .rfc8259 h

silmaril instance formats.relations.drisl_atproto_core_sub_no_floats (expect := THM) (title := "atproto CBOR core (no floats, int64, DASL CIDs) ⊆ DRISL without floats")
  (doc := "Silmaril.Formats.Cbor.Drisl.atprotoCore_le_drislNoFloats") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang1) (K := Silmaril.Project.Languages.Catalogue.drislNoFloatsExactCid)

@[answers "formats.relations.drisl_atproto_core_sub_no_floats" thm]
public theorem relation_drisl_atproto_core_sub_no_floats : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.CborDrisl.lang1 Silmaril.Project.Languages.Catalogue.drislNoFloatsExactCid x :=
  fun _ h => Silmaril.Formats.Cbor.Drisl.atprotoCore_le_drislNoFloats h

silmaril instance formats.relations.drisl_no_floats_sub_drisl (expect := THM) (title := "DRISL without floats ⊆ DRISL (DASL CIDs, exact boundary)")
  (doc := "Silmaril.Formats.Cbor.Drisl.drislNoFloats_le_drisl") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.Catalogue.drislNoFloatsExactCid) (K := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0)

@[answers "formats.relations.drisl_no_floats_sub_drisl" thm]
public theorem relation_drisl_no_floats_sub_drisl : ∀ x, SubsetAt Silmaril.Project.Languages.Catalogue.drislNoFloatsExactCid Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0 x :=
  fun _ h => Silmaril.Formats.Cbor.Drisl.drislNoFloats_le_drisl h

silmaril instance formats.relations.drisl_exact_sub_prefix (expect := THM) (title := "DRISL (exact CID boundary) ⊆ DRISL (CID prefix boundary)")
  (doc := "Silmaril.Formats.Cbor.Drisl.drislExactCid_le_drislCidPrefix") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0) (K := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang2)

@[answers "formats.relations.drisl_exact_sub_prefix" thm]
public theorem relation_drisl_exact_sub_prefix : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0 Silmaril.Project.Languages.FormatExamples.CborDrisl.lang2 x :=
  fun _ h => Silmaril.Formats.Cbor.Drisl.drislExactCid_le_drislCidPrefix h

silmaril instance formats.relations.drisl_sub_bdasl (expect := THM) (title := "DRISL with DASL CIDs ⊆ DRISL with BDASL CIDs")
  (doc := "Silmaril.Formats.Cbor.Drisl.drisl_le_drislBdasl") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0) (K := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang3)

@[answers "formats.relations.drisl_sub_bdasl" thm]
public theorem relation_drisl_sub_bdasl : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0 Silmaril.Project.Languages.FormatExamples.CborDrisl.lang3 x :=
  fun _ h => Silmaril.Formats.Cbor.Drisl.drisl_le_drislBdasl h

silmaril instance formats.relations.drisl_bdasl_exact_sub_prefix (expect := THM) (title := "DRISL/BDASL (exact CID boundary) ⊆ DRISL/BDASL (CID prefix boundary)")
  (doc := "Silmaril.Formats.Cbor.Drisl.drislBdaslExactCid_le_drislBdaslCidPrefix") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang3) (K := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang5)

@[answers "formats.relations.drisl_bdasl_exact_sub_prefix" thm]
public theorem relation_drisl_bdasl_exact_sub_prefix : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.CborDrisl.lang3 Silmaril.Project.Languages.FormatExamples.CborDrisl.lang5 x :=
  fun _ h => Silmaril.Formats.Cbor.Drisl.drislBdaslExactCid_le_drislBdaslCidPrefix h

silmaril instance formats.relations.drisl_no_links_sub_drisl (expect := THM) (title := "DRISL without links ⊆ DRISL")
  (doc := "Silmaril.Formats.Cbor.Drisl.drislNoLinks_le_drisl") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang6) (K := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0)

@[answers "formats.relations.drisl_no_links_sub_drisl" thm]
public theorem relation_drisl_no_links_sub_drisl : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.CborDrisl.lang6 Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0 x :=
  fun _ h => Silmaril.Formats.Cbor.Drisl.drislNoLinks_le_drisl h

silmaril instance formats.relations.drisl_sub_cbor (expect := THM) (title := "DRISL ⊆ well-formed CBOR")
  (doc := "Silmaril.Formats.Cbor.Drisl.language_le_wellFormed") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0) (K := ProjectSelfTest.Languages.cborWellFormed)

@[answers "formats.relations.drisl_sub_cbor" thm]
public theorem relation_drisl_sub_cbor : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0 ProjectSelfTest.Languages.cborWellFormed x :=
  fun _ h => Silmaril.Formats.Cbor.Drisl.language_le_wellFormed .drislExactCid h

silmaril instance formats.relations.drisl_bdasl_prefix_sub_cbor (expect := THM) (title := "DRISL/BDASL (CID prefix) ⊆ well-formed CBOR")
  (doc := "Silmaril.Formats.Cbor.Drisl.language_le_wellFormed") := silmaril.shapes.language.subset_at
  (L := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang5) (K := ProjectSelfTest.Languages.cborWellFormed)

@[answers "formats.relations.drisl_bdasl_prefix_sub_cbor" thm]
public theorem relation_drisl_bdasl_prefix_sub_cbor : ∀ x, SubsetAt Silmaril.Project.Languages.FormatExamples.CborDrisl.lang5 ProjectSelfTest.Languages.cborWellFormed x :=
  fun _ h => Silmaril.Formats.Cbor.Drisl.language_le_wellFormed .drislBdaslCidPrefix h

silmaril instance formats.relations.utf8_sub_ascii (expect := CSA) (title := "UTF-8 ⊆ ASCII (fails: é)") :=
  silmaril.shapes.language.subset_at (L := ProjectSelfTest.Languages.utf8) (K := Silmaril.Project.Languages.FormatExamples.Ascii.lang0)

@[answers "formats.relations.utf8_sub_ascii" csa]
public theorem relation_utf8_sub_ascii : ∃ x, ¬ SubsetAt ProjectSelfTest.Languages.utf8 Silmaril.Project.Languages.FormatExamples.Ascii.lang0 x :=
  ⟨[0xC3, 0xA9], fun h => (show ([0xC3, 0xA9] : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.Ascii.lang0 from (by decide +kernel : ([0xC3, 0xA9] : List UInt8) ∉ Silmaril.Formats.Ascii.language))
    (h (show ([0xC3, 0xA9] : List UInt8) ∈ ProjectSelfTest.Languages.utf8 from Silmaril.Formats.Utf8.isWellFormed_iff.mp (by decide +kernel)))⟩

silmaril instance formats.relations.ascii_sub_printable (expect := CSA) (title := "ASCII ⊆ printable ASCII (fails: LF)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.Ascii.lang0) (K := Silmaril.Project.Languages.FormatExamples.Ascii.lang1)

@[answers "formats.relations.ascii_sub_printable" csa]
public theorem relation_ascii_sub_printable : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.Ascii.lang0 Silmaril.Project.Languages.FormatExamples.Ascii.lang1 x :=
  ⟨[0x0A], fun h => (show ([0x0A] : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.Ascii.lang1 from (by decide +kernel : ([0x0A] : List UInt8) ∉ Silmaril.Formats.Ascii.printable))
    (h (show ([0x0A] : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.Ascii.lang0 from (by decide +kernel : ([0x0A] : List UInt8) ∈ Silmaril.Formats.Ascii.language)))⟩

silmaril instance formats.relations.utf16be_sub_utf16le (expect := CSA) (title := "UTF-16BE ⊆ UTF-16LE (fails: 00 D8)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.Utf16.lang0) (K := Silmaril.Project.Languages.FormatExamples.Utf16.lang1)

@[answers "formats.relations.utf16be_sub_utf16le" csa]
public theorem relation_utf16be_sub_utf16le : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.Utf16.lang0 Silmaril.Project.Languages.FormatExamples.Utf16.lang1 x :=
  ⟨[0x00, 0xD8], fun h => (show ([0x00, 0xD8] : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.Utf16.lang1 from (by decide +kernel : ([0x00, 0xD8] : List UInt8) ∉ Silmaril.Formats.Utf16.language .little))
    (h (show ([0x00, 0xD8] : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.Utf16.lang0 from (by decide +kernel : ([0x00, 0xD8] : List UInt8) ∈ Silmaril.Formats.Utf16.language .big)))⟩

silmaril instance formats.relations.utf16le_sub_utf16be (expect := CSA) (title := "UTF-16LE ⊆ UTF-16BE (fails: D8 00)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.Utf16.lang1) (K := Silmaril.Project.Languages.FormatExamples.Utf16.lang0)

@[answers "formats.relations.utf16le_sub_utf16be" csa]
public theorem relation_utf16le_sub_utf16be : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.Utf16.lang1 Silmaril.Project.Languages.FormatExamples.Utf16.lang0 x :=
  ⟨[0xD8, 0x00], fun h => (show ([0xD8, 0x00] : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.Utf16.lang0 from (by decide +kernel : ([0xD8, 0x00] : List UInt8) ∉ Silmaril.Formats.Utf16.language .big))
    (h (show ([0xD8, 0x00] : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.Utf16.lang1 from (by decide +kernel : ([0xD8, 0x00] : List UInt8) ∈ Silmaril.Formats.Utf16.language .little)))⟩

silmaril instance formats.relations.utf16be_sub_scheme (expect := CSA) (title := "UTF-16BE ⊆ UTF-16 scheme (fails: FF FE 00 D8, read as BOM + little-endian)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.Utf16.lang0) (K := Silmaril.Project.Languages.FormatExamples.Utf16.lang2)

@[answers "formats.relations.utf16be_sub_scheme" csa]
public theorem relation_utf16be_sub_scheme : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.Utf16.lang0 Silmaril.Project.Languages.FormatExamples.Utf16.lang2 x :=
  ⟨[0xFF, 0xFE, 0x00, 0xD8], fun h => (show ([0xFF, 0xFE, 0x00, 0xD8] : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.Utf16.lang2 from (by decide +kernel : ([0xFF, 0xFE, 0x00, 0xD8] : List UInt8) ∉ Silmaril.Formats.Utf16.schemeLanguage))
    (h (show ([0xFF, 0xFE, 0x00, 0xD8] : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.Utf16.lang0 from (by decide +kernel : ([0xFF, 0xFE, 0x00, 0xD8] : List UInt8) ∈ Silmaril.Formats.Utf16.language .big)))⟩

silmaril instance formats.relations.json_integral_sub_int_token (expect := CSA) (title := "Integral-valued number tokens ⊆ lexical integers (fails: 1.0e0)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang1) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang7)

@[answers "formats.relations.json_integral_sub_int_token" csa]
public theorem relation_json_integral_sub_int_token : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang1 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang7 x :=
  ⟨"1.0e0".toUTF8.toList, fun h => (show ("1.0e0".toUTF8.toList : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang7 from (by decide +kernel : ("1.0e0".toUTF8.toList : List UInt8) ∉ Silmaril.Formats.JsonNumbers.integerToken))
    (h (show ("1.0e0".toUTF8.toList : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang1 from (by decide +kernel : ("1.0e0".toUTF8.toList : List UInt8) ∈ Silmaril.Formats.JsonNumbers.integralNumber)))⟩

silmaril instance formats.relations.json_rfc_sub_integral (expect := CSA) (title := "RFC 8259 numbers ⊆ integral-valued (fails: 1.5)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.Catalogue.jsonNumberRfc) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang1)

@[answers "formats.relations.json_rfc_sub_integral" csa]
public theorem relation_json_rfc_sub_integral : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.Catalogue.jsonNumberRfc Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang1 x :=
  ⟨"1.5".toUTF8.toList, fun h => (show ("1.5".toUTF8.toList : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang1 from (by decide +kernel : ("1.5".toUTF8.toList : List UInt8) ∉ Silmaril.Formats.JsonNumbers.integralNumber))
    (h (show ("1.5".toUTF8.toList : List UInt8) ∈ Silmaril.Project.Languages.Catalogue.jsonNumberRfc from (by decide +kernel : ("1.5".toUTF8.toList : List UInt8) ∈ Silmaril.Formats.JsonNumbers.rfc)))⟩

silmaril instance formats.relations.json_binary64_sub_safe (expect := CSA) (title := "binary64-exact integers ⊆ I-JSON safe range (fails: 2^53)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang3) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang4)

@[answers "formats.relations.json_binary64_sub_safe" csa]
public theorem relation_json_binary64_sub_safe : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang3 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang4 x :=
  ⟨"9007199254740992".toUTF8.toList, fun h => (show ("9007199254740992".toUTF8.toList : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang4 from (by decide +kernel : ("9007199254740992".toUTF8.toList : List UInt8) ∉ Silmaril.Formats.JsonNumbers.safeInteger))
    (h (show ("9007199254740992".toUTF8.toList : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang3 from (by decide +kernel : ("9007199254740992".toUTF8.toList : List UInt8) ∈ Silmaril.Formats.JsonNumbers.binary64Integer)))⟩

silmaril instance formats.relations.json_int64_sub_binary64 (expect := CSA) (title := "int64 integers ⊆ binary64-exact (fails: 2^53 + 1)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang2) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang3)

@[answers "formats.relations.json_int64_sub_binary64" csa]
public theorem relation_json_int64_sub_binary64 : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang2 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang3 x :=
  ⟨"9007199254740993".toUTF8.toList, fun h => (show ("9007199254740993".toUTF8.toList : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang3 from (by decide +kernel : ("9007199254740993".toUTF8.toList : List UInt8) ∉ Silmaril.Formats.JsonNumbers.binary64Integer))
    (h (show ("9007199254740993".toUTF8.toList : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang2 from (by decide +kernel : ("9007199254740993".toUTF8.toList : List UInt8) ∈ Silmaril.Formats.JsonNumbers.int64)))⟩

silmaril instance formats.relations.json_binary64_sub_int64 (expect := CSA) (title := "binary64-exact integers ⊆ int64 (fails: 2^64)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang3) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang2)

@[answers "formats.relations.json_binary64_sub_int64" csa]
public theorem relation_json_binary64_sub_int64 : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang3 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang2 x :=
  ⟨"18446744073709551616".toUTF8.toList, fun h => (show ("18446744073709551616".toUTF8.toList : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang2 from (by decide +kernel : ("18446744073709551616".toUTF8.toList : List UInt8) ∉ Silmaril.Formats.JsonNumbers.int64))
    (h (show ("18446744073709551616".toUTF8.toList : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang3 from (by decide +kernel : ("18446744073709551616".toUTF8.toList : List UInt8) ∈ Silmaril.Formats.JsonNumbers.binary64Integer)))⟩

silmaril instance formats.relations.json_binary64_sub_uint64 (expect := CSA) (title := "binary64-exact integers ⊆ uint64 (fails: 2^64)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang3) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang0)

@[answers "formats.relations.json_binary64_sub_uint64" csa]
public theorem relation_json_binary64_sub_uint64 : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang3 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang0 x :=
  ⟨"18446744073709551616".toUTF8.toList, fun h => (show ("18446744073709551616".toUTF8.toList : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang0 from (by decide +kernel : ("18446744073709551616".toUTF8.toList : List UInt8) ∉ Silmaril.Formats.JsonNumbers.uint64))
    (h (show ("18446744073709551616".toUTF8.toList : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang3 from (by decide +kernel : ("18446744073709551616".toUTF8.toList : List UInt8) ∈ Silmaril.Formats.JsonNumbers.binary64Integer)))⟩

silmaril instance formats.relations.json_int64_sub_uint64 (expect := CSA) (title := "int64 ⊆ uint64 (fails: -1)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang2) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang0)

@[answers "formats.relations.json_int64_sub_uint64" csa]
public theorem relation_json_int64_sub_uint64 : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang2 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang0 x :=
  ⟨"-1".toUTF8.toList, fun h => (show ("-1".toUTF8.toList : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang0 from (by decide +kernel : ("-1".toUTF8.toList : List UInt8) ∉ Silmaril.Formats.JsonNumbers.uint64))
    (h (show ("-1".toUTF8.toList : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang2 from (by decide +kernel : ("-1".toUTF8.toList : List UInt8) ∈ Silmaril.Formats.JsonNumbers.int64)))⟩

silmaril instance formats.relations.json_uint64_sub_int64 (expect := CSA) (title := "uint64 ⊆ int64 (fails: 2^63)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang0) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang2)

@[answers "formats.relations.json_uint64_sub_int64" csa]
public theorem relation_json_uint64_sub_int64 : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang0 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang2 x :=
  ⟨"9223372036854775808".toUTF8.toList, fun h => (show ("9223372036854775808".toUTF8.toList : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang2 from (by decide +kernel : ("9223372036854775808".toUTF8.toList : List UInt8) ∉ Silmaril.Formats.JsonNumbers.int64))
    (h (show ("9223372036854775808".toUTF8.toList : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang0 from (by decide +kernel : ("9223372036854775808".toUTF8.toList : List UInt8) ∈ Silmaril.Formats.JsonNumbers.uint64)))⟩

silmaril instance formats.relations.json_python_infinity_sub_rfc (expect := CSA) (title := "RFC + Python Infinity ⊆ RFC 8259 numbers (fails: Infinity)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang5) (K := Silmaril.Project.Languages.Catalogue.jsonNumberRfc)

@[answers "formats.relations.json_python_infinity_sub_rfc" csa]
public theorem relation_json_python_infinity_sub_rfc : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang5 Silmaril.Project.Languages.Catalogue.jsonNumberRfc x :=
  ⟨"Infinity".toUTF8.toList, fun h => (show ("Infinity".toUTF8.toList : List UInt8) ∉ Silmaril.Project.Languages.Catalogue.jsonNumberRfc from (by decide +kernel : ("Infinity".toUTF8.toList : List UInt8) ∉ Silmaril.Formats.JsonNumbers.rfc))
    (h (show ("Infinity".toUTF8.toList : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang5 from (by decide +kernel : ("Infinity".toUTF8.toList : List UInt8) ∈ Silmaril.Formats.JsonNumbers.withPythonInfinity)))⟩

silmaril instance formats.relations.json_python_nonfinite_sub_infinity (expect := CSA) (title := "RFC + Python Infinity/NaN ⊆ RFC + Python Infinity (fails: NaN)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang6) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang5)

@[answers "formats.relations.json_python_nonfinite_sub_infinity" csa]
public theorem relation_json_python_nonfinite_sub_infinity : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang6 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang5 x :=
  ⟨"NaN".toUTF8.toList, fun h => (show ("NaN".toUTF8.toList : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang5 from (by decide +kernel : ("NaN".toUTF8.toList : List UInt8) ∉ Silmaril.Formats.JsonNumbers.withPythonInfinity))
    (h (show ("NaN".toUTF8.toList : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang6 from (by decide +kernel : ("NaN".toUTF8.toList : List UInt8) ∈ Silmaril.Formats.JsonNumbers.withPythonNonFinite)))⟩

silmaril instance formats.relations.json_text_integral_sub_int_token (expect := CSA) (title := "JSON with integral values ⊆ JSON with lexical integers (fails: [1.0e0])") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang10) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang9)

@[answers "formats.relations.json_text_integral_sub_int_token" csa]
public theorem relation_json_text_integral_sub_int_token : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang10 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang9 x :=
  ⟨"[1.0e0]".toUTF8.toList, fun h => (show ("[1.0e0]".toUTF8.toList : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang9 from (by decide +kernel : ("[1.0e0]".toUTF8.toList : List UInt8) ∉ Silmaril.Formats.JsonNumbers.language .rfc8259 Silmaril.Formats.JsonNumbers.integerToken))
    (h (show ("[1.0e0]".toUTF8.toList : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang10 from (by decide +kernel : ("[1.0e0]".toUTF8.toList : List UInt8) ∈ Silmaril.Formats.JsonNumbers.language .rfc8259 Silmaril.Formats.JsonNumbers.integralNumber)))⟩

silmaril instance formats.relations.json_text_int64_sub_binary64 (expect := CSA) (title := "JSON with int64 integers ⊆ JSON with binary64-exact integers (fails: [9007199254740993])") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang8) (K := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang11)

@[answers "formats.relations.json_text_int64_sub_binary64" csa]
public theorem relation_json_text_int64_sub_binary64 : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang8 Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang11 x :=
  ⟨"[9007199254740993]".toUTF8.toList, fun h => (show ("[9007199254740993]".toUTF8.toList : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang11 from (by decide +kernel : ("[9007199254740993]".toUTF8.toList : List UInt8) ∉ Silmaril.Formats.JsonNumbers.language .rfc8259 Silmaril.Formats.JsonNumbers.binary64Integer))
    (h (show ("[9007199254740993]".toUTF8.toList : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang8 from (by decide +kernel : ("[9007199254740993]".toUTF8.toList : List UInt8) ∈ Silmaril.Formats.JsonNumbers.language .rfc8259 Silmaril.Formats.JsonNumbers.int64)))⟩

silmaril instance formats.relations.json_python_nonfinite_text_sub_json (expect := CSA) (title := "JSON + Python Infinity/NaN ⊆ JSON (fails: [NaN])") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang13) (K := ProjectSelfTest.Languages.jsonRfc8259)

@[answers "formats.relations.json_python_nonfinite_text_sub_json" csa]
public theorem relation_json_python_nonfinite_text_sub_json : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang13 ProjectSelfTest.Languages.jsonRfc8259 x :=
  ⟨"[NaN]".toUTF8.toList, fun h => (show ("[NaN]".toUTF8.toList : List UInt8) ∉ ProjectSelfTest.Languages.jsonRfc8259 from (by decide +kernel : ("[NaN]".toUTF8.toList : List UInt8) ∉ Silmaril.Formats.JsonBytes.language .rfc8259))
    (h (show ("[NaN]".toUTF8.toList : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.JsonNumbers.lang13 from (by decide +kernel : ("[NaN]".toUTF8.toList : List UInt8) ∈ Silmaril.Formats.JsonNumbers.language .rfc8259 Silmaril.Formats.JsonNumbers.withPythonNonFinite)))⟩

silmaril instance formats.relations.drisl_sub_atproto_core (expect := CSA) (title := "DRISL ⊆ atproto CBOR core (fails: the float 1.0)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0) (K := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang1)

@[answers "formats.relations.drisl_sub_atproto_core" csa]
public theorem relation_drisl_sub_atproto_core : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0 Silmaril.Project.Languages.FormatExamples.CborDrisl.lang1 x :=
  ⟨[0xFB, 0x3F, 0xF0, 0, 0, 0, 0, 0, 0], fun h => (show ([0xFB, 0x3F, 0xF0, 0, 0, 0, 0, 0, 0] : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.CborDrisl.lang1 from (by decide +kernel : ([0xFB, 0x3F, 0xF0, 0, 0, 0, 0, 0, 0] : List UInt8) ∉ Silmaril.Formats.Cbor.Drisl.language .atprotoCoreExactCid))
    (h (show ([0xFB, 0x3F, 0xF0, 0, 0, 0, 0, 0, 0] : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0 from (by decide +kernel : ([0xFB, 0x3F, 0xF0, 0, 0, 0, 0, 0, 0] : List UInt8) ∈ Silmaril.Formats.Cbor.Drisl.language .drislExactCid)))⟩

silmaril instance formats.relations.drisl_sub_no_floats (expect := CSA) (title := "DRISL ⊆ DRISL without floats (fails: the float 1.0)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0) (K := Silmaril.Project.Languages.Catalogue.drislNoFloatsExactCid)

@[answers "formats.relations.drisl_sub_no_floats" csa]
public theorem relation_drisl_sub_no_floats : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0 Silmaril.Project.Languages.Catalogue.drislNoFloatsExactCid x :=
  ⟨[0xFB, 0x3F, 0xF0, 0, 0, 0, 0, 0, 0], fun h => (show ([0xFB, 0x3F, 0xF0, 0, 0, 0, 0, 0, 0] : List UInt8) ∉ Silmaril.Project.Languages.Catalogue.drislNoFloatsExactCid from (by decide +kernel : ([0xFB, 0x3F, 0xF0, 0, 0, 0, 0, 0, 0] : List UInt8) ∉ Silmaril.Formats.Cbor.Drisl.language .drislNoFloatsExactCid))
    (h (show ([0xFB, 0x3F, 0xF0, 0, 0, 0, 0, 0, 0] : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0 from (by decide +kernel : ([0xFB, 0x3F, 0xF0, 0, 0, 0, 0, 0, 0] : List UInt8) ∈ Silmaril.Formats.Cbor.Drisl.language .drislExactCid)))⟩

silmaril instance formats.relations.drisl_no_floats_sub_atproto_core (expect := CSA) (title := "DRISL without floats ⊆ atproto CBOR core (fails: 2^63, outside int64)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.Catalogue.drislNoFloatsExactCid) (K := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang1)

@[answers "formats.relations.drisl_no_floats_sub_atproto_core" csa]
public theorem relation_drisl_no_floats_sub_atproto_core : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.Catalogue.drislNoFloatsExactCid Silmaril.Project.Languages.FormatExamples.CborDrisl.lang1 x :=
  ⟨[0x1B, 0x80, 0, 0, 0, 0, 0, 0, 0], fun h => (show ([0x1B, 0x80, 0, 0, 0, 0, 0, 0, 0] : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.CborDrisl.lang1 from (by decide +kernel : ([0x1B, 0x80, 0, 0, 0, 0, 0, 0, 0] : List UInt8) ∉ Silmaril.Formats.Cbor.Drisl.language .atprotoCoreExactCid))
    (h (show ([0x1B, 0x80, 0, 0, 0, 0, 0, 0, 0] : List UInt8) ∈ Silmaril.Project.Languages.Catalogue.drislNoFloatsExactCid from (by decide +kernel : ([0x1B, 0x80, 0, 0, 0, 0, 0, 0, 0] : List UInt8) ∈ Silmaril.Formats.Cbor.Drisl.language .drislNoFloatsExactCid)))⟩

silmaril instance formats.relations.drisl_bdasl_sub_drisl (expect := CSA) (title := "DRISL/BDASL ⊆ DRISL/DASL (fails: a BLAKE3 CID, multihash 1E)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang3) (K := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0)

@[answers "formats.relations.drisl_bdasl_sub_drisl" csa]
public theorem relation_drisl_bdasl_sub_drisl : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.CborDrisl.lang3 Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0 x :=
  ⟨[0xD8, 0x2A, 0x58, 0x25, 0x00, 0x01, 0x55, 0x1E, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00], fun h => (show ([0xD8, 0x2A, 0x58, 0x25, 0x00, 0x01, 0x55, 0x1E, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0 from (by decide +kernel : ([0xD8, 0x2A, 0x58, 0x25, 0x00, 0x01, 0x55, 0x1E, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] : List UInt8) ∉ Silmaril.Formats.Cbor.Drisl.language .drislExactCid))
    (h (show ([0xD8, 0x2A, 0x58, 0x25, 0x00, 0x01, 0x55, 0x1E, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.CborDrisl.lang3 from (by decide +kernel : ([0xD8, 0x2A, 0x58, 0x25, 0x00, 0x01, 0x55, 0x1E, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] : List UInt8) ∈ Silmaril.Formats.Cbor.Drisl.language .drislBdaslExactCid)))⟩

silmaril instance formats.relations.drisl_prefix_sub_exact (expect := CSA) (title := "DRISL (CID prefix) ⊆ DRISL (exact CID) (fails: a byte after the digest)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang2) (K := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0)

@[answers "formats.relations.drisl_prefix_sub_exact" csa]
public theorem relation_drisl_prefix_sub_exact : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.CborDrisl.lang2 Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0 x :=
  ⟨[0xD8, 0x2A, 0x58, 0x26, 0x00, 0x01, 0x71, 0x12, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00], fun h => (show ([0xD8, 0x2A, 0x58, 0x26, 0x00, 0x01, 0x71, 0x12, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0 from (by decide +kernel : ([0xD8, 0x2A, 0x58, 0x26, 0x00, 0x01, 0x71, 0x12, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] : List UInt8) ∉ Silmaril.Formats.Cbor.Drisl.language .drislExactCid))
    (h (show ([0xD8, 0x2A, 0x58, 0x26, 0x00, 0x01, 0x71, 0x12, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.CborDrisl.lang2 from (by decide +kernel : ([0xD8, 0x2A, 0x58, 0x26, 0x00, 0x01, 0x71, 0x12, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] : List UInt8) ∈ Silmaril.Formats.Cbor.Drisl.language .drislCidPrefix)))⟩

silmaril instance formats.relations.drisl_sub_no_links (expect := CSA) (title := "DRISL ⊆ DRISL without links (fails: a tag-42 CID)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0) (K := Silmaril.Project.Languages.FormatExamples.CborDrisl.lang6)

@[answers "formats.relations.drisl_sub_no_links" csa]
public theorem relation_drisl_sub_no_links : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0 Silmaril.Project.Languages.FormatExamples.CborDrisl.lang6 x :=
  ⟨[0xD8, 0x2A, 0x58, 0x25, 0x00, 0x01, 0x71, 0x12, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00], fun h => (show ([0xD8, 0x2A, 0x58, 0x25, 0x00, 0x01, 0x71, 0x12, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] : List UInt8) ∉ Silmaril.Project.Languages.FormatExamples.CborDrisl.lang6 from (by decide +kernel : ([0xD8, 0x2A, 0x58, 0x25, 0x00, 0x01, 0x71, 0x12, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] : List UInt8) ∉ Silmaril.Formats.Cbor.Drisl.language .drislNoLinks))
    (h (show ([0xD8, 0x2A, 0x58, 0x25, 0x00, 0x01, 0x71, 0x12, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.CborDrisl.lang0 from (by decide +kernel : ([0xD8, 0x2A, 0x58, 0x25, 0x00, 0x01, 0x71, 0x12, 0x20, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] : List UInt8) ∈ Silmaril.Formats.Cbor.Drisl.language .drislExactCid)))⟩

silmaril instance formats.relations.spki_sub_utf8 (expect := CSA) (title := "Canonical SPKI S-expressions ⊆ UTF-8 (fails: octets 00 FF)") :=
  silmaril.shapes.language.subset_at (L := Silmaril.Project.Languages.FormatExamples.Spki.lang0) (K := ProjectSelfTest.Languages.utf8)

@[answers "formats.relations.spki_sub_utf8" csa]
public theorem relation_spki_sub_utf8 : ∃ x, ¬ SubsetAt Silmaril.Project.Languages.FormatExamples.Spki.lang0 ProjectSelfTest.Languages.utf8 x :=
  ⟨[0x32, 0x3A, 0x00, 0xFF], fun h => (show ([0x32, 0x3A, 0x00, 0xFF] : List UInt8) ∉ ProjectSelfTest.Languages.utf8 from fun h => absurd (Silmaril.Formats.Utf8.isWellFormed_iff.mpr h) (by decide +kernel))
    (h (show ([0x32, 0x3A, 0x00, 0xFF] : List UInt8) ∈ Silmaril.Project.Languages.FormatExamples.Spki.lang0 from (by decide +kernel : ([0x32, 0x3A, 0x00, 0xFF] : List UInt8) ∈ Silmaril.Formats.Spki.canonical)))⟩

end
