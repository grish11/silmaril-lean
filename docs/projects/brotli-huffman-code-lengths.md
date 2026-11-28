# Brotli complex code-length prefix tables

`Brotli.Huffman.CodeLengths.read` reads the first phase of a complex
Huffman description at a supplied LSB bit cursor. It returns the checked
table for the 18 code-length symbols and the cursor at the first unread
bit. The caller supplies a bit budget. The reader debits each fixed
field before reading it, within a maximum of two selector bits and
18 four-bit fields.

The reader admits HSKIP values 0, 2 and 3. It places the fixed codes for
lengths 0 through 5 in the RFC's transmission order, then exposes the
result in numeric symbol order. It stops at Kraft mass 32 immediately
and supplies implicit trailing zeros. The singleton path reaches the
end of all 18 slots with exactly one nonzero described length. The
table exposes that symbol with code width zero. Complete tables use
the existing canonical Huffman construction with a depth cap of five.

`read_sound` relates the original prefix to the explicit `LengthsWire`
grammar, proves both bit bounds and preserves the exact unread suffix
and cursor. `LengthsWire.exhausts_slots` proves that positive residual
mass requires consuming every transmitted slot. `Table.singleton_code`
and `Table.canonical_code` characterize the checked code assignments
and canonical positive widths.

Simple descriptions return `unsupportedSimple`. Bit limits,
truncation, oversubscription and incomplete tables have distinct
errors. Main code-length expansion, entropy-coded payloads and
Parquet dispatch are outside this reader's scope.
[RFC 7932 §3.2](https://www.rfc-editor.org/rfc/rfc7932#section-3.2)
· [§3.5](https://www.rfc-editor.org/rfc/rfc7932#section-3.5)

## Independent replay

libbrotli **1.2.0** at `028fb5a23661f123017c060daa546b55cf4bde29`
writes the two text streams. PyArrow **26.0.1** at
`9e5d6978e9acf372cc989aaaf94e863fe8582c90` writes the V1 and V2
Parquet fixtures. Thrift **0.25.0** at
`27e8a425ffb498e190df3a12e239326bf5ba9ed6` locates the exact compressed
V1 body and V2 value suffix through the existing Parquet harness.

The replay builds a temporary copy of libbrotli with diagnostics at the
selector and secondary-table boundary. The traced decoder produces the
same output bytes as an unmodified reference decoder. It supplies nine
complex table records covering all three skip selectors and three simple
description controls. The Lean run compares all 18 lengths and the
residual cursor with these records. An independent canonical assignment
over the recorded lengths supplies the expected codes. Each comparison uses an exactly sufficient budget and checks the one-bit-short
rejection. A standalone description written by the unmodified native
encoder covers the complex singleton. It ends at bit 36 and maps symbol
3 to a zero-bit code. The Lean guards also exercise malformed tables and
truncation inside a field.
[Fixture manifest](../../scripts/brotli-huffman-code-lengths/fixtures.json)
· [Replay](../../scripts/brotli-huffman-code-lengths/check.py)
· [Native reference](https://github.com/google/brotli/tree/028fb5a23661f123017c060daa546b55cf4bde29)

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.Huffman.CodeLengths.Tests
python -m pip install pyarrow==26.0.1 thrift==0.25.0
python -B -I scripts/brotli-huffman-code-lengths/check.py
```

The replay uses Git, CMake and a C compiler. Pass
`--brotli-source /path/to/brotli` to reuse a checkout at the exact pin.
