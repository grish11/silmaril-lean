# Brotli context-map prefixes

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
count, RLE parameter and alphabet ranges. Coded map symbols,
zero-run expansion, inverse move-to-front and final map coverage
validation are separate. A coded literal result stops before the
rest of that map, which must be consumed before reading the distance
map. Compressed payload execution and Parquet dispatch are outside
this slice.

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

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.ContextMap.Tests
python -m pip install pyarrow==26.0.1 thrift==0.25.0
python -B -I scripts/brotli-context-maps/check.py
```

Use `--brotli-source /path/to/brotli` to reuse a clean checkout at the pin.
