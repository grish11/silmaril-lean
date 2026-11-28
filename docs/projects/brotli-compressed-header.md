# Brotli compressed meta-block header

`Brotli.CompressedHeader.read` starts at `NBLTYPESL` in a compressed
meta-block. The caller supplies that cursor after interpreting the
stream and meta-block framing. The reader uses the standard Brotli
distance alphabet and returns at the first compressed payload bit.
[RFC 7932 §3.3](https://www.rfc-editor.org/rfc/rfc7932#section-3.3)
· [§9.2](https://www.rfc-editor.org/rfc/rfc7932#section-9.2)

The reader composes the checked block controls, NPOSTFIX, NDIRECT,
literal context modes, the complete literal map, and the complete
distance map. It then reads the three tree groups in order.

| Group | Count | Alphabet |
| --- | --- | --- |
| Literal | NTREESL from the literal map | 256 |
| Insert and copy | NBLTYPESI from the command block control | 704 |
| Distance | NTREESD from the distance map | `16 + NDIRECT + 48 * 2^NPOSTFIX` |

The standard distance alphabet ranges from 64 to 520. Each table uses
the existing checked simple or complex description grammar, including
zero-bit singleton codes. If a tree description fails, the error carries
its group and zero-based ordinal. Map errors identify the map. The
reader retains the RFC requirement that every declared tree occur in
its decoded context map. [Context map profile](brotli-context-maps.md)

The caller caps total committed header bits, combined expanded map
entries, and combined descriptions across the three groups. The map
entry cap is checked before reading either map. Each coded map symbol
emits at least one entry, so the combined cap also bounds coded map
symbol work. The three-group cap is checked before reading their first
description. Block-control tables are already bounded to at most two
per category. The RFC-derived extents limit both maps to 17,408 entries
in total and the tree groups to 768 descriptions. These are logical
bounds on the parsed header and its components.

`read_sound` relates success to the original bits from the first control
through the final tree, with an ordered witness, the exact cursor advance
and untouched suffix, and the caller caps. `Wire.groups` proves the
count and alphabet for every group. `GroupWire.valid` and `Wire.bounds`
give the underlying group and aggregate bounds. Stream framing,
the large-window extension, command execution, and Parquet dispatch
are outside the profile.

## Independent replay

The replay uses libbrotli **1.2.0** at
`028fb5a23661f123017c060daa546b55cf4bde29`, PyArrow **26.0.1** at
`9e5d6978e9acf372cc989aaaf94e863fe8582c90`, and Apache Thrift **0.25.0**
at `27e8a425ffb498e190df3a12e239326bf5ba9ed6`. It reuses two extracted
PyArrow payloads, two ordinary CLI streams with coded maps and multiple
trees in all groups, and four streams from the pinned writer API with
configured NPOSTFIX/NDIRECT pairs. The configured streams include the
520-symbol distance alphabet.

The trace observes the native controls and initial counts, context
fields, final map vectors, and every assigned code and width from the
installed control and payload Huffman tables. The traced and unmodified
native decoders return the same decoded bytes. Lean compares the full
header result and residual cursor at the native payload offset. Every
case checks exact acceptance and one-bit, one-entry and one-tree short
caps. Authored guards cover truncated interior fields, an unused map
tree, and an out-of-alphabet distance symbol.
[Manifest](../../scripts/brotli-compressed-header/fixtures.json)
· [Replay](../../scripts/brotli-compressed-header/check.py)

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.CompressedHeader.Tests
python -m pip install pyarrow==26.0.1 thrift==0.25.0
python -B -I scripts/brotli-compressed-header/check.py
```

Use `--brotli-source /path/to/brotli` to reuse a checkout at the pin.
