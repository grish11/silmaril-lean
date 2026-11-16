# Byte languages of formats: coverage

What `Silmaril/Formats` defines as an exact byte language (`Language UInt8`), how the languages
relate, and what is still missing. Each row names the module and the theorems that carry the
evidence. A family is listed as **staged** until its language is defined with a proof that it is
decided, or with an explicit statement of why it is not. A row that names a parser but no
language does not count as covered: a parser that accepts something is not a definition of
validity until a theorem relates the two.

Registrations for the Schema/Language page will go through the project language registry that
the registry task is adding; this file lists the declarations those registrations point at.

## Text encodings

| Language | Declaration | Evidence |
| --- | --- | --- |
| ASCII (`00..7F`, RFC 20) | `Formats.Ascii.language` | `isAscii_iff` (decided), `language_le_utf8`, `mem_language_iff_exists_chars` |
| Printable ASCII (`20..7E`) | `Formats.Ascii.printable` | `printable_le` |
| UTF-8 (Unicode Table 3-7, RFC 3629) | `Formats.Utf8.language` | `isWellFormed_iff`, `isWellFormed_iff_exists_chars`, `validateUTF8_iff` |
| UTF-16BE / UTF-16LE (Unicode §3.10) | `Formats.Utf16.language .big` / `.little` | `isWellFormed_iff`, `mem_language_iff_exists_chars`, `encodeChar_injective` |
| UTF-16 scheme with BOM (Unicode §3.10, RFC 2781 §4.3) | `Formats.Utf16.schemeLanguage` | `mem_schemeLanguage_iff` (decided) |

BOM policy: explicit-endian UTF-16 keeps `FE FF`/`FF FE` as `U+FEFF`; the UTF-16 scheme reads an
initial `FF FE` as the little-endian mark and anything else as big-endian. UTF-8 and JSON do not
strip a BOM (`Formats.JsonBytes` documents that a BOM-prefixed text is not in the language).

Relations: `printable ≤ Ascii.language ≤ Utf8.language`.

## JSON

| Language | Declaration | Evidence |
| --- | --- | --- |
| RFC 8259 JSON text over UTF-8 | `JsonBytes.language .rfc8259` | `JsonBytes.Decide.textB_iff`, `language_isWellFormed` |
| JSON with scalar-value escapes (no lone surrogate escapes) | `JsonBytes.language .scalarEscapes` | `language_scalarEscapes_le` |
| Bounded nesting depth | `JsonBytes.Depth` | owned by the format task |
| JSON Lines / NDJSON | `JsonLines` | owned by the format task |
| ASCII-only JSON | `Ascii.json p` | `json_le`, `json_le_ascii` |
| JSON with number tokens from `N` | `JsonNumbers.language p N` | `language_rfc` (`N = rfc` gives `JsonBytes.language`), `language_mono`, `textB_iff` |

Number-token languages (`Formats.JsonNumbers`), each a set of byte strings:

| Tokens | Declaration | Meaning |
| --- | --- | --- |
| RFC 8259 §6 numbers | `rfc` | the `number` rule |
| Lexical integers | `integerToken` | `[ minus ] int`; `-0` included |
| Integral values | `integralNumber` | RFC numbers with integer value (`1.0`, `1e2`) |
| Signed 64-bit | `int64` | lexical integers (form) with value in `[-2^63, 2^63-1]`; `1.0e0` is not in it |
| Unsigned 64-bit | `uint64` | lexical integers (form) with value in `[0, 2^64-1]`; `-0` is in it (value `0`) |
| I-JSON safe range | `safeInteger` | lexical integers in `[-(2^53-1), 2^53-1]` (RFC 7493 §2.2); not full I-JSON |
| Exactly binary64 | `binary64Integer` | lexical integers equal to some finite IEEE 754 binary64 (`m·2^e`, `m < 2^53`, `e ≤ 971`) |
| RFC + `Infinity`, `-Infinity` (not JSON) | `withPythonInfinity` | Python `json` spelling |
| RFC + `Infinity`, `-Infinity`, `NaN` (not JSON) | `withPythonNonFinite` | Python `json` spelling |

Proved relations (each lifts to texts through `language_mono`):

```
safeInteger ≤ int64 ≤ integerToken          uint64 ≤ integerToken
safeInteger ≤ binary64Integer ≤ integerToken
integerToken ≤ integralNumber ≤ rfc ≤ withPythonInfinity ≤ withPythonNonFinite
```

Proved non-inclusions, with witnesses: `integralNumber ⊄ integerToken` (`1.0`),
`rfc ⊄ integralNumber` (`1.5`), `binary64Integer ⊄ safeInteger` (`2^53`),
`int64 ⊄ binary64Integer` (`2^53 + 1`), `binary64Integer ⊄ int64`, `⊄ uint64` (`2^64`),
`int64 ⊄ uint64` (`-1`), `uint64 ⊄ int64` (`2^63`), `withPythonInfinity ⊄ rfc` (`Infinity`),
`withPythonNonFinite ⊄ withPythonInfinity` (`NaN`).

## S-expressions

| Language | Declaration | Evidence |
| --- | --- | --- |
| SPKI S-expressions, canonical form (RFC 9804 §6.2, §7.2) | `Spki.canonical` (the image of `Spki.encode`) | `mem_canonical_iff` (equals the transcribed ABNF `Spki.ABNF`), `decode_eq_some_iff`, `encode_injective` (the canonical form is unique, as §6.2 says), decided |

## CBOR

Owned by the format task: `Cbor.WellFormed` (RFC 8949 well-formedness), `Cbor.ModelValid`,
`Cbor.Deterministic` (with an explicit float rule), and `Cbor.Drisl` (DRISL and the ATProto
profile as separately named, pinned definitions). This catalogue consumes them.

## Staged

Not yet defined as byte languages here. Each needs a pinned source before it is defined; none is
claimed by this file.

| Family | Notes |
| --- | --- |
| I-JSON (RFC 7493) as a whole | needs string (noncharacters), duplicate-name and number-precision rules on top of `scalarEscapes` and `safeInteger` |
| "Portable JSON" | no single standard; to be defined only against a named profile |
| Value-only 64-bit ranges | `integralNumber` with a value range, so `1.0e0` would count as an int64. Not defined: `int64`/`uint64`/`safeInteger`/`binary64Integer` require the lexical integer form, and the range is checked on the value |
| Unicode-string JSON variants | e.g. no noncharacters, NFC; `scalarEscapes` is the surrogate part |
| Canonical JSON | RFC 8785 (JCS) as a serialization profile; uniqueness only with a theorem |
| JSON5, canonical JSON5 | grammar of the pinned JSON5 spec version |
| S-expressions, transport and advanced (RFC 9804 §6.3, §6.4, §7.1) | base-64 transport, tokens, quoted strings, hexadecimal, whitespace; the older reader `RivestSExp.parseCanonical?` (no display hints) is not yet related to `Spki.canonical` |
| WAT S-expressions | the WAT lexical grammar in `Formats.SExp.EncodingWat*`; no byte language with a theorem yet |
| WAT text, Wasm binary 1.0 / 2.0 / 3.0, components | `Wasm` has grammars and parsers; the abstract acceptors and WIT bridges are owned by the Wasm task |
| ELF | `Formats.ELF` has readers and a CST; no byte language with a theorem yet |
