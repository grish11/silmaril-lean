# Brotli literal insertion

`Brotli.Literal.read` reads the literal insertion of one command in a
compressed meta-block with one literal block type. It takes the checked
compressed header and command, advertised MLEN, the meta-block's
produced byte count, the last two output bytes, and the cursor after
the command's length fields. The caller supplies MLEN from the framing
and carries output history across meta-block boundaries.
[Compressed header](brotli-compressed-header.md) · [Command lengths](brotli-command.md)

The reader uses the sole literal context mode and the original checked
context map and tree group. Each byte selects a tree from the current
history, then becomes the most recent byte. The old most recent byte
becomes second most recent. Stream-start history is two zeros. The
LSB6 and MSB6 formulas and the three UTF-8/Signed tables follow RFC
7932 §7.1, including the published table CRC-32 values.
[RFC 7932 §7.1](https://www.rfc-editor.org/rfc/rfc7932#section-7.1)

Before reading literal codes, the reader checks that the insertion
fits MLEN and the caller's total output cap for the current meta-block.
The insertion length is also the symbol fuel, including for zero-bit
singleton trees. Each code uses the residual bit cap. On success the
reader returns exactly the inserted bytes and the updated history and
produced count. `endOfMetaBlock` means the insertion reaches MLEN. In
that case the advertised copy length is ignored by the enclosing decoder
and no distance field follows, even for a command with explicit distance
mode. `copyPending` means the caller still has a copy to process.
[RFC 7932 §9.3](https://www.rfc-editor.org/rfc/rfc7932#section-9.3)

`Literal.read_sound` ties each original code to the history-selected
tree from the header and proves exact bit advance, untouched suffix,
history update, output limits and both continuation cases.
`Wire.history`, `Wire.bit_bound` and `History.advance_append` give the
history and code extent laws. Framing, block switching, distance and copy
execution, dictionary handling and Parquet dispatch are outside this
increment.

## Independent replay

The replay compares every pair of prior bytes for all four modes
(262,144 context IDs) with compiled libbrotli **1.2.0** at
`028fb5a23661f123017c060daa546b55cf4bde29`. It compares 474 inserted
bytes from first commands in five ordinary compressed streams. The
fixtures include two extracted payloads from PyArrow **26.0.1** at
`9e5d6978e9acf372cc989aaaf94e863fe8582c90`, using Thrift **0.25.0** at
`27e8a425ffb498e190df3a12e239326bf5ba9ed6`, and three streams from the
pinned libbrotli CLI.

Lean locates the first compressed header and MLEN from the fixture
framing, parses the header and first command, then decodes the
insertion. Native offsets and tree selections are comparison outputs.
The UTF-8 and Signed cases exercise respectively two and four selected
trees; the native trace compares the prior bytes, context ID, tree
ordinal, byte and bit offsets for each of those literals. The native
one-tree fast path is compared by its full inserted bytes and insertion
boundaries. The literal-only case reaches MLEN with an explicit-distance
command and returns at the end of its literal bits. Every case checks
exact caps and one-bit and one-byte short caps. Authored controls cover
nonzero incoming history, zero-bit trees, truncation and typed profile
errors.
[Manifest](../../scripts/brotli-literal/fixtures.json)
· [Replay](../../scripts/brotli-literal/check.py)

```sh
lake build --wfail +Silmaril.Formats.Compression.Brotli.Literal.Tests
python -m pip install pyarrow==26.0.1 thrift==0.25.0
python -B -I scripts/brotli-literal/check.py
```

Use `--brotli-source /path/to/brotli` to reuse a checkout at the pin.
