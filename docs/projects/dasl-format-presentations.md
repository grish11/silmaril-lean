# JSON and S-expression presentations in DASL

These presentations use the actual `Silmaril.Formats.Dasl.Value` AST. A
`Dasl.Encode.TotalCodec` provides a concrete encoder and a checked partial
inverse. Its `Abstract` is the subtype of values in the **exact encoder
image**, not the possibly broader domain of its decoder.

For each codec `c`, the following diagrams commute in Lean:

```text
                     parse
Input ─────────────────────────────────> Option AST
  │                                           │
  │ c.parseAbstract? parse                    │ Option.map c.intoAbstract
  ▼                                           ▼
Option c.Abstract ─────────────────────> Option c.Abstract
                     identity
```

Binding `c.fromAbstract?` after `c.parseAbstract? parse` gives `parse`. The
two AST/image round trips are `from_intoAbstract` and `into_fromAbstract`;
the latter is restricted to the exact image. `pull_abstract_equality`
identifies AST equality with the image equality pulled back along the
embedding. `parseAbstract_per` identifies the two wire PERs: both inputs must
parse successfully, and their resulting ASTs must agree. Failed inputs have
no support and are not related, even to themselves.

| Profile | Source AST | DASL subtype | Concrete parser |
| --- | --- | --- | --- |
| Safe JSON | `JsonWire.Ast SafeInt` | `safe.Abstract` | `parseSafe?` |
| I64 JSON | `JsonWire.Ast Int64` | `i64.Abstract` | `parseI64?` |
| RFC JSON | `JsonWire.Ast JsonWire.Decimal` | `rfc.Abstract` | `JsonWire.parse?` |
| Safe JSON + bytes | `BytesAst SafeInt` | `safeBytes.Abstract` | Typed AST only |
| I64 JSON + bytes | `BytesAst Int64` | `i64Bytes.Abstract` | Typed AST only |
| RFC JSON + bytes | `BytesAst JsonWire.Decimal` | `rfcBytes.Abstract` | Typed AST only |
| Proper symbol S-expressions | `SExp String` | `symbols.Abstract` | `SExpParser.parseSExp?` |
| Canonical Rivest S-expressions | `SExp Bytes` | `rivest.Abstract` | `RivestSExp.parseCanonical?` |

The three byte-extended JSON ASTs reuse the raw `RawSyn` grammar and add
`ByteArray` as a disjoint scalar. `includeBytes_commutes` and
`parse_includeBytes_commutes` compare the ordinary and extended profiles in
the common carrier `Value`; ordinary ASTs embed identically. Wire syntax for
literal bytes in JSON is deliberately unspecified. `orderedWithBytes` also
adapts the existing `JsonWithBytes.Ordered` String-based AST, which is not a
representation of raw UTF-16 code units. The S-expression API is generic in
the atom codec; it does not identify symbol text with opaque bytes or claim
to parse improper lists through a proper-list profile.

## Observation limits

- Safe and I64 use **value-based** integral parsing: for example `1e2` and
  `100` yield the same exact integer. They reject fractional values and
  out-of-range integers. Safe means `|n| ≤ 2^53−1`, not all of I-JSON.
- RFC recovers the exact AST fields (sign including negative zero, unsigned
  coefficient, signed unbounded exponent), not the original number lexeme,
  escape spelling, or whitespace. It does not quotient by mathematical
  decimal equality, round through binary floats, or expand the exponent.
- Keys and strings preserve all UTF-16 units including lone surrogates.
  Object membership is an ordered sequence of pairs including duplicates,
  encoded as tagged lists, **not** a native unordered DASL dict. The numeric
  tag distinguishes exact decimals and integers from strings or byte data.
- These are tagged presentations, not untagged DASL/JSON compatibility,
  DRISL byte equivalence, or a canonical RFC JSON text printer.

Local check:

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Json.Dasl.Examples +Silmaril.Formats.SExp.Dasl.Examples'
```
