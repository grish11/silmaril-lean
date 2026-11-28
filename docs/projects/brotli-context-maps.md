# Brotli context maps

`Brotli.ContextMap.read` takes the block category, its checked type count
and the bit cursor at the associated `NTREES` field. It supports literal
and distance maps with extents `64 * NBLTYPESL` and `4 * NBLTYPESD`.
For the first map, use the cursor returned by
`Brotli.ContextHeader.read`. Both categories use the existing §9.2
positive count reader.
[RFC 7932 §7.3](https://www.rfc-editor.org/rfc/rfc7932#section-7.3)
· [§9.2](https://www.rfc-editor.org/rfc/rfc7932#section-9.2)

A one-tree map consumes just its one-bit count. The result represents
the complete constant zero map by its extent. `implicitIndex?` returns
zero exactly for indices within that extent.

For two or more trees, the result carries the expected map extent,
tree count, `RLEMAX` and a checked Huffman description over
`NTREES + RLEMAX`. The cursor is at the first coded map symbol.
The reader checks block type and caller extent bounds before reading,
and rejects a declared tree count larger than the map extent. The
count, RLE field and Huffman description share one caller bit cap.

`read_sound` relates the original bits to `Wire`, with an exact
prefix extent and untouched suffix. `Wire.implicit_bits` identifies
the whole one-tree wire. `Prefix.implicitIndex_iff` proves exact
in-bounds zero entries, and `Wire.coded_bounds` establishes the tree
count, RLE parameter and alphabet ranges.

For a complete map, call `Brotli.ContextMap.Decode.read` at the same
cursor. The one-tree case consumes no symbols or IMTF bit. For a coded
map, symbol zero emits one zero, symbols 1 through RLEMAX consume that
many little-endian extra bits and emit a zero run of length
`2^symbol + extra`, and higher symbols emit `symbol - RLEMAX`. The reader
rejects a run that exceeds the exact map extent before materializing it.
After the last entry it reads one IMTF bit. If set, it selects each
position from the current order and moves the selected tree to the
front. It then verifies that every declared tree occurs in the final map,
as specified by §7.3. The pinned libbrotli decoder omits this coverage
check.

Caller limits for expanded entries, coded symbols and committed bits are
additional profile bounds. The bit cap includes NTREES through the IMTF
bit. Every coded symbol spends a work unit and emits at least one entry,
including a zero-bit singleton. Inverse MTF processes the expanded
vector with at most 256 tree indices in its working list. The final
coverage check scans only the bounded vector and the declared tree
range. The prefix check rejecting NTREES greater than the extent
follows from the RFC tree-use requirement.

`Decode.read_sound` witnesses the original count, description, symbols,
run extras and flag, the exact bit offset, the unchanged suffix and
the caller caps. `Decode.Wire.valid` proves exact output cardinality and
that membership in the final map is equivalent to being a declared
tree index. `Decode.MtfWire.fullTable` proves agreement with the RFC's
256-entry initial order. Both maps can be read in sequence using the
returned cursor. Compressed payload execution and Parquet dispatch are
outside this slice.

## Independent replay

The replay pins libbrotli **1.2.0** at
`028fb5a23661f123017c060daa546b55cf4bde29`, PyArrow **26.0.1** at
`9e5d6978e9acf372cc989aaaf94e863fe8582c90`, and Thrift **0.25.0** at
`27e8a425ffb498e190df3a12e239326bf5ba9ed6`. Two actual PyArrow payloads
exercise implicit literal and distance maps in sequence. Two ordinary
libbrotli CLI streams exercise coded prefixes with multiple trees and
nonzero RLEMAX in both categories. The coded distance tests start at
the position measured by the native decoder. The traced decoder also
matches the unmodified decoder's whole-stream output.

The trace independently locates the control, map and subsequent
symbol boundaries. Lean checks the literal start against the landed
header cursor, each prefix against the native stop and unchanged
suffix, and the exact cap and one-bit-short rejection. Authored RFC
guards cover RLE disabled and RLEMAX 16, the largest implicit literal
extent, invalid counts and caps, and typed truncation.
[Manifest](../../scripts/brotli-context-maps/fixtures.json)
· [Replay](../../scripts/brotli-context-maps/check.py)

The full replay compares native traces of eight final vectors, their
symbol counts and their end offsets. Lean starts at the checked header
cursor and reads the distance map from the literal map's returned cursor,
including for the two coded pairs. The full residual cursor is compared
at each boundary. Both CLI pairs exercise RLE and IMTF=1. IMTF=0,
zero-bit singleton termination, an oversized run, a missing tree and
truncated fields are authored RFC controls. Each native case checks an
exact and one-bit-short cap, and each coded case also checks a
one-symbol-short cap.
[Full manifest](../../scripts/brotli-context-maps/full-fixtures.json)

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.ContextMap.Tests +Silmaril.Formats.Compression.Brotli.ContextMap.Decode.Tests +Silmaril.Formats.Compression.Brotli.ContextHeader.Tests
python -m pip install pyarrow==26.0.1 thrift==0.25.0
python -B -I scripts/brotli-context-maps/check.py
python -B -I scripts/brotli-context-maps/check.py --full
```

Use `--brotli-source /path/to/brotli` to reuse a clean checkout at the pin.
