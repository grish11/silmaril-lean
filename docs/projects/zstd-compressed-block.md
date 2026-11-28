# Bounded Zstandard compressed block payloads

`CompressedBlock.decode` takes the exact type-2 block body, the
declared compressed size and the state from previously accepted
blocks. It checks the caller's input and output caps against the
RFC block maximum, `min(Window_Size, 131072)`. The number of sequences
is also limited to the smaller of the caller's command limit and
one third of the output capacity. Each sequence emits at least
three match bytes. [RFC 8878 §§3.1.1.2.4–3.1.1.5][rfc] · [Definitions][defs]

The decoder reads raw or RLE literals, resolves predefined, RLE,
transmitted and Repeat sequence tables, parses the entire reverse
stream, then executes the commands within the remaining output
budget and appends the unused literal suffix. The literal size is
checked before an RLE run expands. The executor checks repeat
offsets and actual history, including the existing strict
`distance < Window_Size` policy. The bounded objects include
wire bytes, command count, output and retained history.
[Literal parser][literals] · [Repeat tables][tables] · [Reverse reader][reverse] · [Window policy][window]

Only the successful block result contains the successor tables,
repeat offsets and retained history. The roll keeps the last
window of prior history plus this block's output. An unsequenced
compressed block emits its expanded literals and preserves the
tables and repeat offsets. A caller handling physical raw and RLE
blocks can pass their already checked output to `State.advancePlain`,
which preserves those same states while rotating history. Frame
dispatch, checksums, dictionaries, Huffman literals and Parquet
activation are outside this standalone entry point.

`initial_valid` gives the initial invariant and
`advancePlain_sound` gives the exact suffix and state handoff
for plain output. `decode_sound` connects the exact declared
extent to the literal, table and reverse-stream relations, and
proves bounded execution and successor validity.
`decode_sequence_failure` and `decode_execution_failure` show
that a successful table selection publishes no successor when
a later stage fails. [Theorem header][thms]

## Pinned differential

The oracle builds libzstd v1.5.7 at
`f8745da6ff1ad1e7bab384bd1f9d742439278e99`. It compares each Lean
block result to authored output and passes the full frame to
libzstd for an independent end-to-end check. The first five
sequence sections come from the [Repeat-table fixture][tables].
The nine-block frame also includes physical raw and RLE blocks,
a sequenced RLE literal section, and overlapping cross-block
matches using zero-literal repeat-offset rules. Its SHA-256 is
`19ee42fd68fee802f5df505b2449c033b9b58aa5769da54bbcfb61b0bb2b3ad4`.

Two replacement-table prefixes are followed by a bad end marker
or a decoded command that requires absent literals. Both decoders
reject each malformed frame. The Lean driver then decodes a
valid Repeat block against the last accepted state. Lean
regressions also cover exact extents, caller caps, unsupported
literal modes, and strict window equality. [Pinned source][zstd] · [Oracle runner][oracle] · [Lean regressions][tests]

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.CompressedBlock.Thms +Silmaril.Formats.Compression.Zstd.CompressedBlock.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-compressed-block-oracle/check.py
```

[rfc]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1.2.4
[defs]: ../../Silmaril/Formats/Compression/Zstd/CompressedBlock/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/CompressedBlock/Thms.lean
[literals]: zstd-literal-block.md
[tables]: zstd-repeat-tables.md
[reverse]: zstd-sequence-decode.md
[window]: zstd-rle-frame.md
[tests]: ../../Silmaril/Formats/Compression/Zstd/CompressedBlock/Tests.lean
[oracle]: ../../scripts/zstd-compressed-block-oracle/check.py
[zstd]: https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99
