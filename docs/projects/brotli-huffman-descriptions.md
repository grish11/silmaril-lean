# Bounded Brotli Huffman descriptions

`Brotli.Huffman.Description.read` reads one RFC 7932 §3.4 or §3.5
description at a supplied LSB cursor. The caller supplies the alphabet
size, alphabet cap and total bit cap. The output is a checked table
and the cursor at the first bit after the description. The library
previously exposed the complex stages separately and returned
`unsupportedSimple` from the complex secondary-table reader.
[RFC 7932 §§3.2–3.5](https://www.rfc-editor.org/rfc/rfc7932#section-3.2)
· [Complex table installation](brotli-huffman-main-table.md)

The first two bits choose the entry point. Selector 1 leads to the
simple body. It checks the smallest symbol-field width for the
alphabet, range and uniqueness in original symbol order, and the
tree-select bit for four symbols. Two- through four-symbol tables
use the shared canonical constructor with depths in the original
numeric ordinal slots. A one-symbol table uses an explicit singleton
with a zero-bit code. Its one-symbol reader succeeds even with an
empty cursor and leaves every cursor field identical.

Selectors 0, 2 and 3 lead to the checked complex pipeline. The
non-consuming selector inspection is within the shared cap. The
complex secondary reader receives the original cursor, so its
witness starts at the HSKIP field. The main reader receives the
remaining budget and returns the installed canonical table. The
simple reader instead starts after the selector with two bits
debited. The simple body has a 43-bit structural bound for the
admitted alphabet range. The combined description has a bound
of 74 plus eight times the alphabet size.

`Simple.read_sound` accounts for the original symbol fields and
optional tree bit. `Description.read_sound` relates the complete
description to its branch and preserves the exact bit suffix and
absolute cursor. `Wire.selector` identifies the original two-bit
selector, and `Table.singleton_read` and `Table.singleton_code`
give its zero-bit behavior. Compressed meta-block execution and
Parquet dispatch are outside this entry point.

## Independent replay

The replay pins libbrotli **1.2.0** at
`028fb5a23661f123017c060daa546b55cf4bde29`, PyArrow **26.0.1** at
`9e5d6978e9acf372cc989aaaf94e863fe8582c90`, and Thrift **0.25.0** at
`27e8a425ffb498e190df3a12e239326bf5ba9ed6`. It uses a Thrift-extracted
PyArrow V1 compressed body, a PyArrow V2 compressed value suffix,
and five ordinary libbrotli streams.

The diagnostic libbrotli build records selectors, original simple
symbol order, installed code maps and exact bit boundaries. Its
whole-stream output matches the unmodified native decoder.
The fixtures cover all four selector values and all five simple
shapes, including both four-symbol trees. The Lean driver compares
all code slots, the absolute cursor and every suffix field for 21
descriptions. Each comparison checks rejection at a one-bit-short
cap. Three pinned singleton tables also return their native symbol
on an empty cursor. Lean guards cover out-of-range and duplicate
simple symbols, truncated selectors and tree bits, and a complex
description with zero main bits.
[Manifest](../../scripts/brotli-huffman-description/fixtures.json)
· [Replay](../../scripts/brotli-huffman-description/check.py)

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.Huffman.Description.Tests
python -m pip install pyarrow==26.0.1 thrift==0.25.0
python -B -I scripts/brotli-huffman-description/check.py
```

The replay builds the pinned native source with Git and CMake. Pass
`--brotli-source /path/to/brotli` to use a clean checkout at the pin.
