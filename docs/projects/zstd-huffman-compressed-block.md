# Exact Zstandard compressed bodies with stateful Huffman literals

`CompressedBlock.Huffman.decode` accepts the exact body of a type-2 block
with caller-supplied window, input, output and sequence limits. It uses
the checked raw, RLE, new-tree and treeless literal reader and the
existing predefined, RLE, transmitted FSE and Repeat sequence path.
The literal prefix supplies the entire sequence section, including the
reverse stream and its end marker. [RFC 8878 block format][rfc]

`State.initial` uses empty literal and sequence tables and the standard
dictionary-free repeat offsets. The successor carries the checked
Huffman table, sequence tables, rolling history and repeat offsets.
`decode_sound` connects the exact input extent, output bound, literal
count and suffix, table transitions, and sequence execution.
`decode_suffix_failure` propagates a typed suffix error after a
successful literal parse. The result contains a successor only after
sequence decoding and execution succeed. [Proof interface][proof]

The earlier raw/RLE-literal decoder keeps its public contract. This
entry point leaves frame parsing, raw/RLE frame-block dispatch,
checksums, dictionaries and Parquet codec dispatch outside its scope.
The existing strict match-distance policy `distance < window` applies.
Pinned libzstd also accepts a window-equal distance in the earlier
[window-boundary differential][window]. The output bound counts decoded
bytes and makes no peak-memory guarantee.

## Verification

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.CompressedBlock.Huffman.Tests
python3 -I scripts/zstd-huffman-compressed-block-oracle/check.py
```

The oracle regenerates the [pinned literal-state fixture][fixture]
with libzstd v1.5.7 at `f8745da6ff1ad1e7bab384bd1f9d742439278e99`.
The first compressed body has a direct new tree and four streams.
The second has one treeless stream and copy references into the
previous block. Both carry transmitted sequence tables. Lean accepts
the two exact bodies in order and matches the 131,072 and 4,096 bytes
of output observed at libzstd's bufferless block boundaries, with an
independent full libzstd decode as a cross-check. The fixture's frame
SHA-256 is `6fb53d7c3100b6c9c30c275f3c7bb02fba4fd5ebb8dd96bcc4078ade9f24d73e`.

The differential zeros the first block's sequence marker. Native
decoding rejects it, Lean returns `badEndMarker`, and the original
first block and its treeless successor still pass. Additional controls
cover cold treeless state, short declared size, truncation, and input,
command and output caps. Small Lean regressions also exercise
sequence-table Repeat and rejection at the strict window boundary.

[rfc]: https://www.rfc-editor.org/rfc/rfc8878.html#section-3.1.1.2.4
[proof]: ../../Silmaril/Formats/Compression/Zstd/CompressedBlock/Huffman/Thms.lean
[window]: zstd-sequence-frame.md#window-boundary
[fixture]: ../../scripts/zstd-huffman-literal-state-oracle/fixture.json
