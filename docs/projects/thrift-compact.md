# Thrift Compact values for Parquet metadata

The wire reference is Apache Thrift's *Thrift Compact protocol encoding*, pinned to
v0.23.0 at commit `e4b684f5ff4f9c3a42cd7ec0a667c3d9bd7f6ac1`. The specification
file's SHA-256 is `a8b78a102c618215dd006dd484f38bc99f5e723bb86ab96615792c5407789bd5`.
See `apache-thrift-compact-v023` in [references.bib](../../references.bib) and the
[pinned specification][spec].

## Wire rules

- An `i8` is a signed octet. Signed `i16`, `i32`, and `i64` use ZigZag followed
  by base-128 groups in least-significant-first order. Each nonterminal octet
  sets bit 7. An enum uses the `i32` representation.
- Binary starts with an unsigned varint byte count. Strings carry UTF-8 in
  that same layout, with no delimiter. Doubles carry eight little-endian
  bytes in IEEE 754 layout. UUIDs carry sixteen bytes in network order.
- A struct header's low nibble tags the field type. A nonzero high nibble is
  a positive field-ID delta. A zero high nibble is followed by a signed
  ZigZag `i16` ID. The initial previous ID is zero. The single byte
  `00` ends the struct. Field boolean tags 1 and 2 carry true and false and
  consume zero payload bytes. Boolean elements use their own octet, 1 or 2.
- List and set headers carry a type nibble and a count from 0 to 14, or a
  count nibble of 15 followed by the unsigned varint count. Empty maps carry
  a zero count. Nonempty maps carry the count and then a byte with key type
  in the high nibble and value type in the low nibble. Both boolean type
  tags are valid in collection headers. [Apache Thrift Compact encoding][spec]

## Reader profile

- Choose `VarintMode.canonical` to reject redundant high zero groups, or
  `VarintMode.permissive` to accept them within the same bounds. Both modes
  limit `i16`, `i32`, and `i64` varints to 3, 5, and 10 bytes respectively
  and reject terminal bits outside the requested width. A continuation on
  the last permitted byte is overflow. Running out of input before that
  point is truncation. The signed encoder emits the shortest spelling.
- Binary and collection lengths must fit the nonnegative `i32` domain and
  the explicit caller cap. A binary payload must fit in the source before
  it is copied. The string reader uses Lean's checked UTF-8 decoder.
- A field ID obtained by delta addition must fit signed `i16`. Explicit
  signed IDs are accepted even when a writer could have used a short header.
  The list/set reader rejects extended counts below 15. Both modes reject
  unknown type nibbles, type zero in a nonzero field header, and standalone
  boolean values outside 1 and 2. Varint mode controls only varint spelling.

## API for the Parquet metadata reader

Import `Silmaril.Formats.ThriftCompact.Defs` for executable code or
`Silmaril.Formats.ThriftCompact.Thms` for the proved contracts.
Readers use the existing `Silmaril.Formats.Bytes` carrier, take a zero-based
offset, and return `Except Error (value × nextOffset)` with the first unread
offset on success. They can run on a bounded metadata region supplied as
`Bytes`.

| API | Use |
| --- | --- |
| `readFieldHeader` | Start each struct at previous ID zero. Supply the last successful field ID for the next header. Dispatch on `FieldType.payload` or take the boolean value from `FieldType.bool`. Stop on `.stop`. |
| `readSigned`, `encodeSigned?` | Read and write signed `.i16`, `.i32`, and `.i64` values. Use `.i32` for enum wire values. |
| `readI8`, `readBool`, `readDoubleBits`, `readUuid` | Read fixed-size scalar values. Doubles preserve all raw `UInt64` patterns, including NaN payloads. |
| `readBinary`, `readString` | Read a length-prefixed payload with a byte cap. |
| `readCollectionHeader`, `readMapHeader` | Read element or entry counts and wire types with a count cap. The returned offset starts the elements or entries. |
| `readVarint_ok_iff`, `readSigned_ok_iff` | Characterize successful reads by the wire relation, width, and exact consumed prefix. |
| `readSigned_encodeSigned?`, `readBinary_ok_iff` | Recover every encoded in-range signed value at an arbitrary offset, and characterize binary reads by the bounded length and exact source slice. |

Recursive collection and struct traversal, skipping unknown field payloads,
schema validation, and all writers except the signed integer encoder remain
outside this slice. RPC envelopes, Parquet file framing, compression, and
table APIs are outside this layer.

## Fixtures

`Examples.lean` includes the specification's unsigned 50399 example and a
struct fixture derived from the wire rules. The latter uses ascending and
descending field IDs, inline boolean values, a binary value containing
`00 ff 41`, minimum `i64`, a two-element `list<i16>`, and STOP. The pinned
Python writer independently emits the same bytes for that sequence. Lean's
fixture adds `a5` after STOP to check the first unread offset. Malformed
fixtures check truncation, terminal overflow, excess continuation,
nonminimal varints, bad types and booleans, invalid UTF-8, and length guards.
[Lean fixtures](../../Silmaril/Formats/ThriftCompact/Examples.lean) ·
[Pinned Python implementation][python]

```sh
lake build --wfail +Silmaril.Formats.ThriftCompact.Examples
```

[spec]: https://github.com/apache/thrift/blob/e4b684f5ff4f9c3a42cd7ec0a667c3d9bd7f6ac1/doc/specs/thrift-compact-protocol.md
[python]: https://github.com/apache/thrift/blob/e4b684f5ff4f9c3a42cd7ec0a667c3d9bd7f6ac1/lib/py/src/protocol/TCompactProtocol.py
