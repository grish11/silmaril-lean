# Brotli complex main code-length expansion

`Brotli.Huffman.MainLengths.read` takes the checked 18-symbol table
returned by the first phase of RFC 7932 §3.5 and a bit cursor. It returns
all lengths in numeric order for the caller's alphabet, including
implicit trailing zeros, and the cursor at the next unread bit. The
input alphabet must fit both the caller limit and the standard maximum
of 704. The caller's bit cap includes both code symbols and repeat
extra bits.
[RFC 7932 §§3.3–3.5](https://www.rfc-editor.org/rfc/rfc7932#section-3.3)
· [Code-length table reader](brotli-huffman-code-lengths.md)

The `CodeLengthSymbol` component uses the shared canonical Huffman
reader on at most five bits of scratch lookahead within the caller
budget. It checks the reported code at the original cursor and commits
only the code's actual width. A checked singleton returns its symbol
with the same cursor.

The expansion starts with previous nonzero length 8. A direct length
resets the repeat chain, and a zero length preserves the previous
nonzero length. Symbols 16 and 17 start runs of `3 + extra`. The same
symbol extends its current total by the RFC recurrence, using radix
4 for 16 and 8 for 17. Only the increment is emitted. Switching
symbols starts a new run. Every token decreases the remaining
alphabet extent, including a token represented by zero bits. The
recursion is fueled by the alphabet size, and the reader checks the
run extent and Kraft debit before materializing the run. The read
stops at Kraft exhaustion and pads the remaining alphabet with
implicit zeros. Exhausting the alphabet first is an incomplete table.

`CodeLengthSymbol.read_sound` proves the checked symbol and exact
cursor delta. `MainLengths.read_sound` binds a successful read to the
ordered `RunsWire` relation and proves the unchanged suffix and exact
bit consumption. `RunsWire.bounds` gives exact alphabet size, Kraft
mass 32768 for a top-level read, maximum depth 15 and at most eight
bits per alphabet slot. `Token.repeat_run` proves a repeat's positive
increment, the new accumulated total and preservation of valid
history. The companion laws cover unchanged and switched tags,
literal resets and the prior length of 8 at initialization.

This slice returns the main length vector. Simple prefix descriptions,
main table installation, compressed payload decoding and Parquet
dispatch are outside its scope.

## Independent replay

The replay pins libbrotli **1.2.0** at
`028fb5a23661f123017c060daa546b55cf4bde29`, PyArrow **26.0.1** at
`9e5d6978e9acf372cc989aaaf94e863fe8582c90`, and Thrift **0.25.0** at
`27e8a425ffb498e190df3a12e239326bf5ba9ed6`. It uses the actual
Thrift-extracted PyArrow V1 Brotli body and two ordinary libbrotli
text streams at qualities 4 and 6.

A temporary trace records the native vector and exact cursor when
libbrotli builds each canonical table. The traced decoder matches
the unmodified decoder's output on every whole stream. Lean compares
the full length vectors of all nine complex descriptions, plus the
cursor and suffix. The unmodified native encoder supplies two
standalone descriptions with a zero-bit code-length symbol. One emits
eight copies of length 3 with no main bits. The other uses repeat
symbol 16 with the default prior and consumes eight extra bits to
emit 256 copies of length 8. Each bit-bearing comparison also checks
a one-bit-short cap. The Lean guards cover repeat transitions and
malformed, truncated, and limited inputs, including a zero-bit
singleton that exhausts its alphabet without filling Kraft space.
[Manifest](../../scripts/brotli-huffman-main-lengths/fixtures.json)
· [Replay](../../scripts/brotli-huffman-main-lengths/check.py)

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.Huffman.MainLengths.Tests
python -m pip install pyarrow==26.0.1 thrift==0.25.0
python -B -I scripts/brotli-huffman-main-lengths/check.py
```

The replay uses Git, CMake and a C compiler. Pass
`--brotli-source /path/to/brotli` to use a clean pinned checkout.
