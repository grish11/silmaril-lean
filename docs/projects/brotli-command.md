# Brotli insert-and-copy command lengths

`Brotli.Command.spec` maps every ordinal in `Fin 704` to its insert
and copy length codes and its distance mode. It selects the row and
column of the RFC's 64-symbol cell, then uses bits 3–5 and 0–2 for the
insert and copy indices within that cell. Each length table gives a
base and an extra-bit width.
[RFC 7932 §5](https://www.rfc-editor.org/rfc/rfc7932#section-5)

`readExtras` reads the two little-endian extra fields in insert-then-copy
order. It returns the bases plus those extra values. `read` first
commits a symbol using the caller's checked 704-symbol command tree.
One cap covers the symbol and both extras. The command code uses at
most 15 bits and each extra field uses at most 24, so one successful
command consumes at most 63 bits. The Huffman error identifies a symbol
read failure. Extra-field errors identify the insert or copy field
and distinguish truncation from a caller cap.

`readSingle` selects the sole command tree in a parsed compressed header.
For a multi-type header, `read` accepts a tree selected by the caller.
Selecting or switching that type is outside this API.
[Compressed header](brotli-compressed-header.md)

Codes 0–127 imply distance **code** zero for a subsequent copy. Other
codes signal an explicit distance code in the later distance field.
The reader stops after the copy extras, before the literals and any
distance field. If insertion ends the meta-block, the enclosing decoder
can ignore the copy length and omit the distance as defined by §9.3.
Literal decoding, actual distance resolution, history windows, dictionary
handling and Parquet dispatch are outside this increment.
[RFC 7932 §9.3](https://www.rfc-editor.org/rfc/rfc7932#section-9.3)

`read_sound` witnesses the original Huffman code and both ordered fields,
with exact cursor advance, untouched suffix and the caller's cap.
`readExtras_sound` gives the corresponding known-symbol contract, and
`readSingle_sound` ties it to the exact tree selected from the header.
`spec_bounds`, `spec_implicit_iff`, `ExtrasWire.bounds` and `Wire.bounds`
establish the limits and distance selector. The two truncation laws
identify the first missing extra field under an adequate caller cap.

## Independent replay

The oracle compiles and compares all 704 rows of the pinned libbrotli
**1.2.0** command lookup table from
`028fb5a23661f123017c060daa546b55cf4bde29`. It also traces successful
command reads in two extracted PyArrow payloads and two ordinary
libbrotli CLI streams. PyArrow **26.0.1** is pinned at
`9e5d6978e9acf372cc989aaaf94e863fe8582c90` and Thrift **0.25.0** at
`27e8a425ffb498e190df3a12e239326bf5ba9ed6`.

The trace records native command boundaries, actual block type, symbol,
both lengths and distance mode. Lean parses each original header and
reads each command at the observed boundary, comparing the full residual
cursor. Later command starts and multi-type tree selections come from the
native trace. The traced decoder and the unmodified library agree on
the full decoded bytes. Every command uses its exact bit cap, and every
positive-width command checks one-bit-short rejection. Authored controls
cover zero-bit singletons, maximum-width extras, and typed truncation
or cap failure in either extra field.
[Manifest](../../scripts/brotli-command/fixtures.json)
· [Replay](../../scripts/brotli-command/check.py)

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.Command.Tests
python -m pip install pyarrow==26.0.1 thrift==0.25.0
python -B -I scripts/brotli-command/check.py
```

Use `--brotli-source /path/to/brotli` to reuse a checkout at the pin.
