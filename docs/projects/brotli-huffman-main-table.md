# Brotli complex main Huffman table installation

`Brotli.Huffman.MainTable.read` takes an already checked code-length
table and the cursor at the main lengths of an RFC 7932 §3.5 complex
description. Use the applicable alphabet size from the surrounding
grammar. The reader wraps the bounded main-length expansion and
installs the shared `HuffmanTable.ofLengths` at depth 15. The result
carries the exact expanded vector, its canonical decoder and the
following bit cursor.
[RFC 7932 §§3.2–3.5](https://www.rfc-editor.org/rfc/rfc7932#section-3.2)
· [Main length expansion](brotli-huffman-main-lengths.md)

`read_sound` ties the installed decoder to the same length vector and
cursor as the expansion, including its complete Kraft mass, original
wire witness, and caller bounds. `read_after_lengths` proves that an
accepted expansion has a canonical installation at that exact cursor.

`Table.ordinal` proves that the decoder entry at each original ordinal
has the width from the expanded vector. A positive width gets its
canonical first code plus the rank of that width among earlier
ordinals. An implicit or explicit zero occupies its ordinal slot
without a code. An out-of-range ordinal has no entry or code.
The reader covers canonical installation for complex descriptions.
Simple-description admission, compressed meta-block command execution
and Parquet dispatch are separate.

## Independent replay

The replay pins libbrotli **1.2.0** at
`028fb5a23661f123017c060daa546b55cf4bde29`, PyArrow **26.0.1** at
`9e5d6978e9acf372cc989aaaf94e863fe8582c90`, and Thrift **0.25.0** at
`27e8a425ffb498e190df3a12e239326bf5ba9ed6`. It uses nine actual complex
tables from an independently produced PyArrow V1 Brotli body and
two ordinary libbrotli streams.

The diagnostic build calls libbrotli's own symbol lookup on each
15-bit scratch prefix of every installed native table. It extracts
code values and widths in original ordinal order. The diagnostic
build also matches whole-stream output with the unmodified
reference decoder. Lean compares all 3,072 ordinal slots and code
assignments, along with both description boundaries. It decodes
35 selected native codewords in synthetic non-byte-aligned cursors
with an unread sentinel suffix. The Lean guards additionally cover
sparse ordinals, a wrapped one-bit-short error, and 15-bit assignments.
[Manifest](../../scripts/brotli-huffman-main-table/fixtures.json)
· [Replay](../../scripts/brotli-huffman-main-table/check.py)

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.Huffman.MainTable.Tests
python -m pip install pyarrow==26.0.1 thrift==0.25.0
python -B -I scripts/brotli-huffman-main-table/check.py
```

The replay uses Git, CMake and a C compiler. Pass
`--brotli-source /path/to/brotli` to use a clean checkout at the pin.
