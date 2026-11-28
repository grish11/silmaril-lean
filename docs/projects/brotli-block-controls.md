# Brotli compressed meta-block block controls

`Brotli.BlockTypes.read` starts at `NBLTYPESL` in an already identified
compressed meta-block. It reads the literal, insert-and-copy and distance
controls in that order and leaves the cursor immediately before
`NPOSTFIX`. The caller supplies the total bit budget.
[RFC 7932 §6](https://www.rfc-editor.org/rfc/rfc7932#section-6)
· [RFC 7932 §9.2](https://www.rfc-editor.org/rfc/rfc7932#section-9.2)

Each variable-length type count occupies 1–11 bits and declares 1–256
types. A count of one has no control tables or initial count field.
A larger count carries the block type description, with alphabet
`NBLTYPES + 2`, then the block count description, with alphabet 26.
Both use the checked [Huffman description reader](brotli-huffman-descriptions.md).
The initial block's type is implicitly zero. Its count is the §6 base
for the decoded symbol plus its little-endian extra bits. A singleton
count code consumes zero symbol bits. The shared Huffman lookup uses
at most 15 bits of scratch lookahead and commits only the validated
code on the original cursor. All reads debit the same bit budget.

`BlockTypes.read_sound` connects the complete original prefix to three
ordered `ControlWire` witnesses and proves exact bit advancement,
suffix preservation and the caller cap. `CountWire.bounds` and
`ControlWire.bounds` give the type-count and first-block-count ranges.
This parser ends at the three controls. The surrounding meta-block
envelope, distance and context headers, later block switches, payload
execution and Parquet dispatch are outside its scope.

## Independent replay

The replay pins libbrotli **1.2.0** at
`028fb5a23661f123017c060daa546b55cf4bde29`, PyArrow **26.0.1** at
`9e5d6978e9acf372cc989aaaf94e863fe8582c90`, and Thrift **0.25.0** at
`27e8a425ffb498e190df3a12e239326bf5ba9ed6`. The PyArrow cases are
the original Thrift-extracted V1 compressed body and V2 compressed
value suffix. Three ordinary libbrotli CLI outputs supply observed
multi-type cases. One has multiple literal types alone, one has
multiple distance types alone, and one has multiple types in every
category.

A temporary native trace records the category boundaries, type counts
and initial counts. Its whole-stream output is compared with the
unmodified decoder. Lean compares these controls and exact bit
positions, the complete following cursor, the two multi-type table
alphabet sizes, and the one-bit-short rejection. Lean guards also
cover the maximum variable-length type count, the 24-bit extra
field, truncated reads and malformed nested table descriptions.
[Fixture manifest](../../scripts/brotli-block-controls/fixtures.json)
· [Oracle](../../scripts/brotli-block-controls/check.py)

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.BlockTypes.Tests
python -m pip install pyarrow==26.0.1 thrift==0.25.0
python -B -I scripts/brotli-block-controls/check.py
```

The oracle builds the pinned reference with Git and CMake. Pass
`--brotli-source /path/to/brotli` to use a clean checkout at the pin.
