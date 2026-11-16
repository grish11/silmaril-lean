module

public import Silmaril.Project.Shapes.Language.Thms
public import Silmaril.Project.Languages.Wasm.Defs
public import Silmaril.Project.Formats.Defs
public import Silmaril.Formats.JsonBytes.Thms
public import Silmaril.Formats.JsonBytes.Decide.Thms
public import Silmaril.Formats.Utf8.Thms
public import Silmaril.Formats.Cbor.WellFormed.Thms
public import Silmaril.Formats.JsonEvents.Defs
public import Silmaril.Semantics.Accept.MonoidRegex.Examples
-- the registry's artifacts are declared by these modules first (as in `ProjectSelfTest`)
public import Silmaril.Project.WasmComponents.Thms
public import Silmaril.Project.WasmComponents.Relations.Thms
public import Silmaril.Project.WasmComponents.Toy.Thms
public import Silmaril.Project.WasmComponents.Versions.Thms
public import Silmaril.Project.WasmComponents.Wac.Thms
public import Silmaril.Project.WasmComponents.Wac.Verdicts.Thms

/-!
# The `sil project` self-test: languages

Languages built with every `op` of `silmaril language`, over three domains, and the standard
language problems about them (`silmaril.shapes.language.*`), with answers where a proof
exists and none where it does not:

* **existing Lean languages** (`op := decl`): JSON texts under both escape profiles
  (`Silmaril.Formats.JsonBytes.language`, RFC 8259), well-formed UTF-8
  (`Silmaril.Formats.Utf8.language`, RFC 3629), and *well-formed* CBOR data items
  (`Silmaril.Formats.Cbor.wellFormed`, RFC 8949 §1.2: well-formed only — not *valid*, which
  would also require UTF-8 text strings and unique map keys);
* a **project format** (`op := format`): the byte strings that the project's `json` format
  parses;
* an **interpreted Wasm module** (`op := artifact`): the bytes that the CID-pinned
  `examples/project-formats/example.wasm` passes to `env.accept`, under
  `wasm.core.accept_bytes32`;
* **set operations** (`union`, `inter`, `diff`), a **byte regular expression** `[0-9]+`
  (`regex`, list semantics), a regular expression over the monoid `(ℕ, +)` (`2*`, monoid
  semantics), and a **measure restriction** (`within`);
* the problems: inclusions in both directions (with a preserved counterexample), sentence
  and artifact membership, nonempty/empty/universal/nonuniversal, a measure bound, equality
  with a measure-restricted language, and two open problems (equality of the format's language
  with RFC 8259's, and acceptance by the Wasm module) that stay unknown.
-/

namespace ProjectSelfTest.Languages

open Silmaril.Formats Silmaril.Project.Shapes

@[expose] public section

/-- JSON texts, RFC 8259 (any four hex digits in `\u` escapes). -/
def jsonRfc8259 : Set (List UInt8) := JsonBytes.language .rfc8259
/-- JSON texts whose escapes all denote Unicode scalar values. -/
def jsonScalarEscapes : Set (List UInt8) := JsonBytes.language .scalarEscapes
/-- Well-formed UTF-8. -/
def utf8 : Set (List UInt8) := Utf8.language
/-- Well-formed CBOR data items (not validity). -/
def cborWellFormed : Set (List UInt8) := Cbor.wellFormed

/-- An ASCII digit, as a Bool class. -/
def isDigitB (b : UInt8) : Bool := 0x30 ≤ b && b ≤ 0x39

/-- `[0-9]+` over bytes. -/
def digitsRe : Silmaril.Accept.Regex.Expr (Fin 0) UInt8 := .comp (.cls isDigitB) (.star (.cls isDigitB))

/-- `[0-9]*` over bytes: the first, wrong, version of `digitsRe` (it admits the empty input). -/
def digitsV0Re : Silmaril.Accept.Regex.Expr (Fin 0) UInt8 := .star (.cls isDigitB)

/-- `2*` over `(ℕ, +)`: sums of twos. -/
def evensRe : Silmaril.Accept.MonoidRegex.Expr (Fin 0) (Multiplicative ℕ) :=
  .star (.atom (Multiplicative.ofAdd 2))

/-- Ordered JSON trees with string keys and scalars (lexemes). -/
abbrev JsonTree : Type := JsonEvents.Tree String String
/-- The nesting depth of a JSON tree. -/
def jsonTreeDepth (t : JsonTree) : ℕ := t.depth
/-- JSON event streams. -/
abbrev JsonEventStream : Type := List (JsonEvents.Event String String)
/-- The well-formed event streams: those of some tree. -/
def jsonEventsLang : Set JsonEventStream := JsonEvents.language String String

end

end ProjectSelfTest.Languages

/-! ## Values: CID-pinned artifacts of the registry -/

silmaril_artifacts_refresh "silmaril/artifacts.toml"
silmaril value silmaril.selftest.languages.hello : bytes := silmaril.selftest.hello_txt
silmaril value silmaril.selftest.languages.example_wasm : wasm := silmaril.selftest.example_wasm

/-! ## Domains and measures of this project -/

silmaril language_domain silmaril.selftest.json.tree := ProjectSelfTest.Languages.JsonTree
  (doc := "Ordered JSON trees (Silmaril.Formats.JsonEvents.Tree String String)")
silmaril language_domain silmaril.selftest.json.events := ProjectSelfTest.Languages.JsonEventStream
  (doc := "JSON event streams (List (Silmaril.Formats.JsonEvents.Event String String))")
silmaril measure silmaril.selftest.json.tree.depth := ProjectSelfTest.Languages.jsonTreeDepth
  (domain := silmaril.selftest.json.tree) (doc := "Nesting depth (Tree.depth)")

/-! ## Languages -/

silmaril language silmaril.selftest.lang.json := ProjectSelfTest.Languages.jsonRfc8259
  (domain := bytes) (op := decl) (title := "JSON texts (RFC 8259)") (source := rfc8259)
silmaril language silmaril.selftest.lang.json.scalar := ProjectSelfTest.Languages.jsonScalarEscapes
  (domain := bytes) (op := decl) (title := "JSON texts with scalar-value escapes")
  (source := rfc8259)
silmaril language silmaril.selftest.lang.utf8 := ProjectSelfTest.Languages.utf8
  (domain := bytes) (op := decl) (title := "Well-formed UTF-8 (RFC 3629)") (source := rfc3629)
silmaril language silmaril.selftest.lang.cbor := ProjectSelfTest.Languages.cborWellFormed
  (domain := bytes) (op := decl) (title := "Well-formed CBOR data items (not validity)")
  (source := rfc8949) (doc := "RFC 8949 §1.2 well-formedness only: text strings need not be UTF-8 and map keys may repeat")
silmaril language silmaril.selftest.lang.json.events := ProjectSelfTest.Languages.jsonEventsLang
  (domain := silmaril.selftest.json.events) (op := decl) (title := "Well-formed JSON event streams")

silmaril language silmaril.selftest.lang.json.format (domain := bytes) (op := format)
  (format := json) (title := "Byte strings the project's json format parses")

silmaril language silmaril.selftest.lang.wasm.accept (domain := bytes) (op := artifact)
  (value := silmaril.selftest.languages.example_wasm) (interpretation := wasm.core.accept_bytes32)
  (title := "Bytes example.wasm passes to env.accept")

silmaril language silmaril.selftest.lang.json_or_cbor (domain := bytes) (op := union)
  (args := [silmaril.selftest.lang.json, silmaril.selftest.lang.cbor])
silmaril language silmaril.selftest.lang.cbor_utf8 (domain := bytes) (op := inter)
  (args := [silmaril.selftest.lang.cbor, silmaril.selftest.lang.utf8])
silmaril language silmaril.selftest.lang.json_not_utf8 (domain := bytes) (op := diff)
  (args := [silmaril.selftest.lang.json, silmaril.selftest.lang.utf8])

silmaril language silmaril.selftest.lang.digits := ProjectSelfTest.Languages.digitsRe
  (domain := bytes) (op := regex) (title := "[0-9]+")
-- a deprecated language stays, pointing at its successor
silmaril language silmaril.selftest.lang.digits.v0 := ProjectSelfTest.Languages.digitsV0Re
  (domain := bytes) (op := regex) (title := "[0-9]* (deprecated)")
silmaril deprecation silmaril.selftest.lang.digits.v0
  (reason := "admits the empty input; numbers have at least one digit")
  (superseded_by := [silmaril.selftest.lang.digits])
silmaril language silmaril.selftest.lang.digits.short (domain := bytes) (op := within)
  (args := [silmaril.selftest.lang.digits]) (measure := bytes.length) (bound := 3)
  (title := "[0-9]+ of at most 3 bytes")
silmaril language silmaril.selftest.lang.evens := ProjectSelfTest.Languages.evensRe
  (domain := nat.additive) (op := regex) (title := "2* over (ℕ, +): the even numbers")

/-! ## Problems -/

open ProjectSelfTest.Languages Silmaril.Project.Shapes Silmaril.Formats in
section

-- inclusion, proved: the scalar-escape profile refines RFC 8259
silmaril instance silmaril.selftest.languages.json_scalar_sub_json (expect := THM)
  (title := "JSON with scalar escapes ⊆ JSON") := silmaril.shapes.language.subset_at
  (L := ProjectSelfTest.Languages.jsonScalarEscapes) (K := ProjectSelfTest.Languages.jsonRfc8259)

@[answers "silmaril.selftest.languages.json_scalar_sub_json" thm]
public theorem json_scalar_sub_json : ∀ x, SubsetAt jsonScalarEscapes jsonRfc8259 x :=
  fun _ h => JsonBytes.language_scalarEscapes_le h

-- inclusion, proved: every JSON text is UTF-8 (RFC 8259 §8.1)
silmaril instance silmaril.selftest.languages.json_sub_utf8 (expect := THM)
  (title := "JSON ⊆ UTF-8") := silmaril.shapes.language.subset_at
  (L := ProjectSelfTest.Languages.jsonRfc8259) (K := ProjectSelfTest.Languages.utf8)

@[answers "silmaril.selftest.languages.json_sub_utf8" thm]
public theorem json_sub_utf8 : ∀ x, SubsetAt jsonRfc8259 utf8 x :=
  fun _ h => JsonBytes.language_isWellFormed h

-- the converse fails, with the counterexample kept: the empty input is UTF-8 but not JSON
silmaril instance silmaril.selftest.languages.utf8_sub_json (expect := CSA)
  (title := "UTF-8 ⊆ JSON (fails: the empty input)") := silmaril.shapes.language.subset_at
  (L := ProjectSelfTest.Languages.utf8) (K := ProjectSelfTest.Languages.jsonRfc8259)

@[answers "silmaril.selftest.languages.utf8_sub_json" csa]
public theorem utf8_sub_json : ∃ x, ¬ SubsetAt utf8 jsonRfc8259 x :=
  ⟨[], fun h => JsonBytes.nil_not_mem_language _ (h Utf8.isWellFormed_nil)⟩

-- the difference JSON \ UTF-8 is empty
silmaril instance silmaril.selftest.languages.json_not_utf8_empty (expect := UNS)
  (title := "JSON \\ UTF-8 is empty") := silmaril.shapes.language.member
  (L := silmaril.selftest.lang.json_not_utf8)

@[answers "silmaril.selftest.languages.json_not_utf8_empty" uns]
public theorem json_not_utf8_empty : ∀ x, ¬ Member silmaril.selftest.lang.json_not_utf8 x :=
  fun _ h => h.2 (JsonBytes.language_isWellFormed h.1)

-- JSON is nonempty and not universal: contingent, not "nontrivial" by one answer
silmaril instance silmaril.selftest.languages.json_member (expect := contingent)
  (title := "Membership in JSON") := silmaril.shapes.language.member
  (L := ProjectSelfTest.Languages.jsonRfc8259)

@[answers "silmaril.selftest.languages.json_member" sat]
public theorem json_nonempty : ∃ x, Member jsonRfc8259 x :=
  ⟨[0x31], JsonBytes.Decide.textB_iff.mp (by decide)⟩

@[answers "silmaril.selftest.languages.json_member" csa]
public theorem json_nonuniversal : ∃ x, ¬ Member jsonRfc8259 x :=
  ⟨[], JsonBytes.nil_not_mem_language _⟩

-- sentence membership, closed: `1` is JSON; the break byte alone is not a CBOR item
silmaril instance silmaril.selftest.languages.json_has_one (expect := THM)
  (title := "`1` is a JSON text") := silmaril.shapes.language.member
  (L := ProjectSelfTest.Languages.jsonRfc8259) (x := [0x31])

@[answers "silmaril.selftest.languages.json_has_one" thm]
public theorem json_has_one : Member jsonRfc8259 [0x31] :=
  JsonBytes.Decide.textB_iff.mp (by decide)

silmaril instance silmaril.selftest.languages.cbor_has_break (expect := UNS)
  (title := "0xFF alone is a CBOR data item (fails: a break is not an item)") :=
  silmaril.shapes.language.member (L := ProjectSelfTest.Languages.cborWellFormed) (x := [0xFF])

@[answers "silmaril.selftest.languages.cbor_has_break" csa]
public theorem cbor_has_break : ¬ Member cborWellFormed [0xFF] :=
  fun h => absurd (Cbor.isWellFormed_iff.mpr h) (by decide)

-- an intersection is nonempty
silmaril instance silmaril.selftest.languages.cbor_utf8_nonempty (expect := SAT)
  (title := "Some CBOR item is UTF-8") := silmaril.shapes.language.member
  (L := silmaril.selftest.lang.cbor_utf8)

@[answers "silmaril.selftest.languages.cbor_utf8_nonempty" sat]
public theorem cbor_utf8_nonempty : ∃ x, Member silmaril.selftest.lang.cbor_utf8 x :=
  ⟨[0x00], Cbor.isWellFormed_iff.mp (by decide), Utf8.isWellFormed_iff.mp (by decide)⟩

-- `[0-9]+` is not included in JSON: `00` has a leading zero
silmaril instance silmaril.selftest.languages.digits_sub_json (expect := CSA)
  (title := "[0-9]+ ⊆ JSON (fails: 00)") := silmaril.shapes.language.subset_at
  (L := silmaril.selftest.lang.digits) (K := ProjectSelfTest.Languages.jsonRfc8259)

@[answers "silmaril.selftest.languages.digits_sub_json" csa]
public theorem digits_sub_json : ∃ x, ¬ SubsetAt silmaril.selftest.lang.digits jsonRfc8259 x :=
  ⟨[0x30, 0x30], fun h => absurd (JsonBytes.Decide.textB_iff.mpr (h
    ⟨[0x30], ⟨0x30, rfl, rfl⟩, [0x30], ⟨[[0x30]], rfl, fun y hy => by
      rw [List.mem_singleton.mp hy]; exact ⟨0x30, rfl, rfl⟩⟩, rfl⟩))
    (by decide)⟩

-- a measure bound and equality with a measure-restricted language
silmaril instance silmaril.selftest.languages.digits_short_bound (expect := THM)
  (title := "Short digit strings have at most 3 bytes") := silmaril.shapes.language.bound_at
  (L := silmaril.selftest.lang.digits.short) (μ := Silmaril.Project.Languages.bytesLength) (b := 3)

@[answers "silmaril.selftest.languages.digits_short_bound" thm]
public theorem digits_short_bound :
    ∀ x, BoundAt silmaril.selftest.lang.digits.short Silmaril.Project.Languages.bytesLength 3 x :=
  fun _ h => h.2

silmaril instance silmaril.selftest.languages.digits_short_eq (expect := THM)
  (title := "Short digit strings are [0-9]+ restricted to 3 bytes") :=
  silmaril.shapes.language.eq_within_at (L := silmaril.selftest.lang.digits.short)
  (K := silmaril.selftest.lang.digits) (μ := Silmaril.Project.Languages.bytesLength) (b := 3)

@[answers "silmaril.selftest.languages.digits_short_eq" thm]
public theorem digits_short_eq : ∀ x, EqWithinAt silmaril.selftest.lang.digits.short
    silmaril.selftest.lang.digits Silmaril.Project.Languages.bytesLength 3 x :=
  fun _ => Iff.rfl

-- numbers: 6 is a sum of twos, 7 is not (an expected negative result)
silmaril instance silmaril.selftest.languages.evens_has_6 (expect := THM)
  (title := "6 ∈ 2*") := silmaril.shapes.language.member
  (L := silmaril.selftest.lang.evens) (x := Multiplicative.ofAdd 6)

@[answers "silmaril.selftest.languages.evens_has_6" thm]
public theorem evens_has_6 : Member silmaril.selftest.lang.evens (Multiplicative.ofAdd 6) :=
  ⟨[Multiplicative.ofAdd 2, Multiplicative.ofAdd 2, Multiplicative.ofAdd 2], by simp, rfl⟩

silmaril instance silmaril.selftest.languages.evens_has_7 (expect := UNS)
  (title := "7 ∈ 2* (fails)") := silmaril.shapes.language.member
  (L := silmaril.selftest.lang.evens) (x := Multiplicative.ofAdd 7)

@[answers "silmaril.selftest.languages.evens_has_7" csa]
public theorem evens_has_7 : ¬ Member silmaril.selftest.lang.evens (Multiplicative.ofAdd 7) := by
  rintro ⟨l, hl, hprod⟩
  have hrep : l = List.replicate l.length Silmaril.Accept.MonoidRegexExamples.two :=
    List.eq_replicate_iff.mpr ⟨rfl, fun y hy => hl y hy⟩
  rw [hrep, Silmaril.Accept.MonoidRegexExamples.prod_replicate_two] at hprod
  have : 2 * l.length = 7 := congrArg Multiplicative.toAdd hprod
  omega

-- artifact membership: the bytes of examples/project/data/hello.txt are UTF-8
instance : DecidablePred fun b : Silmaril.Formats.Bytes => BytesMember utf8 b :=
  fun b => decidable_of_iff _ (Utf8.isWellFormed_iff (w := b.toList))

silmaril instance silmaril.selftest.languages.hello_utf8 (expect := THM)
  (title := "hello.txt is UTF-8") := silmaril.shapes.language.bytes_member
  (L := ProjectSelfTest.Languages.utf8) (b := silmaril.selftest.languages.hello)

@[answers "silmaril.selftest.languages.hello_utf8" thm]
public theorem hello_utf8 : silmaril.selftest.languages.hello.Satisfies (fun b => BytesMember utf8 b) :=
  Silmaril.Project.Value.satisfies_of_any (by decide)

-- open: the format's parser against the RFC grammar, and what the Wasm module accepts
silmaril instance silmaril.selftest.languages.json_format_eq_json (expect := OPN)
  (title := "The json format's language is RFC 8259's") := silmaril.shapes.language.eq_at
  (L := silmaril.selftest.lang.json.format) (K := ProjectSelfTest.Languages.jsonRfc8259)

silmaril instance silmaril.selftest.languages.wasm_accept_member (expect := OPN)
  (title := "Membership in what example.wasm accepts") := silmaril.shapes.language.member
  (L := silmaril.selftest.lang.wasm.accept)

end

@[solves "silmaril.selftest.languages.hello.parses"] public theorem hello_parses :
    silmaril.selftest.languages.hello.parses := by
  silmaril_decide

@[solves "silmaril.selftest.languages.example_wasm.parses"] public theorem example_wasm_parses :
    silmaril.selftest.languages.example_wasm.parses := by
  silmaril_decide

silmaril group silmaril.selftest.languages (title := "Languages")
  (children := [silmaril.selftest.languages.json_scalar_sub_json,
    silmaril.selftest.languages.json_sub_utf8, silmaril.selftest.languages.utf8_sub_json,
    silmaril.selftest.languages.json_not_utf8_empty, silmaril.selftest.languages.json_member,
    silmaril.selftest.languages.json_has_one, silmaril.selftest.languages.cbor_has_break,
    silmaril.selftest.languages.cbor_utf8_nonempty, silmaril.selftest.languages.digits_sub_json,
    silmaril.selftest.languages.digits_short_bound, silmaril.selftest.languages.digits_short_eq,
    silmaril.selftest.languages.evens_has_6, silmaril.selftest.languages.evens_has_7,
    silmaril.selftest.languages.hello_utf8, silmaril.selftest.languages.json_format_eq_json,
    silmaril.selftest.languages.wasm_accept_member,
    silmaril.selftest.languages.hello.parses, silmaril.selftest.languages.example_wasm.parses])
