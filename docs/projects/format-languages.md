# Format languages

This page describes the byte languages of data formats in `Silmaril/Formats`: which inputs are
*valid*, given as Mathlib `Language UInt8`s. Each language has a proved decision procedure, and
depth, line or profile variants as named definitions. These are specifications. They are what
readers, validators and Wasm components are checked against, and they say nothing about the
correctness of any particular parser.

Each module states its standard, dialect and every choice in its documentation. Sources are
pinned in [`references.bib`](../../references.bib) with SHA-256.

## Stable semantic APIs

| Topic | Language and main definitions | Decision and key theorems | Source |
|---|---|---|---|
| `Formats.Utf8` | `Utf8.language`, `Utf8.IsWellFormed`, `Utf8.scalar`, `Utf8.multibyte`, `Bytes.IsUtf8` | `Utf8.isWellFormed_iff`, `isWellFormed_iff_exists_chars`, `isValidUTF8_iff` (Lean core), `decides_isWellFormed` | Unicode 15 Table 3-7, RFC 3629 |
| `Formats.JsonBytes` | `JsonBytes.language p` with `Profile.rfc8259` and `Profile.scalarEscapes`; `Text`, `Value`, `Elements`, `Members`; lexical `RegularExpression`s (`ws`, `number`, `string p`, `scalar p`); `Bytes.IsJson` | `Decide.textB_iff`, `decides_textB`, `language_isWellFormed` (UTF-8), `language_scalarEscapes_le` | RFC 8259 |
| `Formats.JsonBytes.Depth` | `JsonBytes.languageAt p d` (scalars depth 0, containers 1 + deepest child); `ValueAt` | `Decide.textAtB_iff`, `iUnion_languageAt`, `languageAt_mono`, `byteBracket_not_jsonDepth` | RFC 8259 §9 |
| `Formats.JsonLines` | `JsonLines.Policy` (`final`, `blankLines`, `crInText`) with `Policy.jsonLines` and `Policy.ndjson`; `lineOf pol L`, `frameLang pol L`, `language pol p`, `languageAt pol p d` | `frameB_iff`, `terminated_eq_frameItems`, `terminated_mem_itemBound_iff`, `language_isWellFormed`, `iUnion_languageAt` | jsonlines.org, NDJSON spec |
| `Formats.JsonEvents` | `Tree K S` (ordered, duplicates kept), `Event K S`, `Event.kind`, `Tree.toEvents`, `ofEvents?`, `language K S`, `Tree.depth` | `equivLanguage : Tree K S ≃ language K S`, `ofEvents?_eq_some_iff`, `toEvents_mem_depthBound_iff` | — |
| `Formats.Cbor.WellFormed` | `Cbor.wellFormed` (one well-formed item), `Item`, `Items`, `Head` | `isWellFormed_iff`, `skip_sound`, `item_skip`; all RFC 8949 Appendix F.1 vectors | RFC 8949 §3, App. C |
| `Formats.Cbor.Value` | `Cbor.Value` (representation-level: ordered maps, floats as width and bits), `encodeHead`, `Value.encode`, `decode`, `Value.Encodable` | `decode_encode`, `encode_injective`, `encode_mem_wellFormed` | RFC 8949 §4.2.1 heads |
| `Formats.Cbor.Drisl` | `Drisl.language P`; profiles `drislExactCid`, `drislCidPrefix`, `drislNoFloatsExactCid`, `atprotoCoreExactCid`; `CidBoundary`, `IsDaslCid` | `check_iff`, `language_le_wellFormed`, `value_unique`, `language_mono` | DRISL 2026-10-22, DASL CID, CBOR/c-42, atproto data model |
| `Formats.Streaming` | `derivAcceptor r`, `utf8Acceptor`, `jsonAcceptor`, `jsonLinesAcceptor`, `cborAcceptor`, `jsonDepthAcceptor` | `…_correctInterleaved` (`Semantics.Acceptors`), `jsonDepthAcceptor_soundFold`, `jsonDepthAcceptor_completeFoldOn` | — |
| `Formats.JsonBytes.Accept` | `scalarHead`, `profileLang` | `decides_textB`, `decidesOn_scalarHead`, `profile_lt` (`Semantics.Accept`) | — |

Each decision theorem gives a `Decidable` instance, so `decide +kernel` checks closed examples.
`Silmaril.Formats.Accept.Lang.exact_ofBool_iff` turns a `Decides` fact into
`Lang.Exact (ofBool check) L`. `Silmaril.Formats.Format.ofLanguage L` makes any of these
languages a `Format`.

## Integration points

The WIT representations of JSON event streams and JSON Lines items are in
`Silmaril.Wasm.Component.Reference.WIT.Repr.Json` (#553), and the WIT string and item
languages in `Silmaril.Wasm.Component.Reference.WIT.Json`. The language registry and catalogue
use the definitions above; they do not restate them.

## Named assumptions and limits

- **JSON strings:** lone surrogate escapes are in `Profile.rfc8259`, not in
  `Profile.scalarEscapes`. `scalarEscapes` is I-JSON's surrogate rule only, not full I-JSON.
- **JSON Lines:** the empty file is zero lines under every policy, which neither source addresses.
  With an optional final newline and blank lines allowed, the bytes do not determine the
  item list.
- **CBOR values:** `Cbor.Value` is finer than RFC 8949's generic data model. Floats of different
  widths, and definite versus indefinite strings, are different values.
- **CBOR coverage:** generic §5.3 validity, generic §4.2.1 determinism with preferred float
  serialization, and CBOR events are not yet defined.
- **DRISL tag 42:** whether bytes may follow the 36-byte CID is not settled by the normative DASL
  CID text. It is the profile parameter `CidBoundary`, and the named profiles carry it.
- **Repository CIDs:** the artifact registry's BLAKE3 CIDs use hash type `0x1e`. The pinned DASL CID
  spec allows only SHA-256 (`0x12`), so DRISL rejects them inside tag 42.
- **ATProto:** `atprotoCoreExactCid` covers only no floats and signed 64-bit integers.
  `blob` structure, reserved `$` fields and Lexicon constraints are not checked.
- **Readers:** no theorem relates these languages to `JsonWire.parse?` or any other reader, and no
  lexer from bytes to events is proved.
- **Acceptors:** the JSON, JSON Lines and CBOR acceptors buffer their input; only
  `utf8Acceptor` is incremental.

## Checking

```sh
lake build --wfail Silmaril.Formats.JsonLines.Thms Silmaril.Formats.JsonEvents.Thms \
  Silmaril.Formats.Cbor.Drisl.Thms Silmaril.Formats.Streaming.Thms \
  Silmaril.Formats.JsonBytes.Accept.Thms
```
