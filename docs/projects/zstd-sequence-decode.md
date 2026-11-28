# Standalone Zstandard sequence decoding

`SequenceDecode.decode` takes the exact bytes of a sequences section.
It applies the sequence-table resolver's input and count caps, resolves
predefined, RLE and transmitted FSE tables, and opens the remaining bytes
at the highest set bit of the last byte. The zero-sequence case consumes
its entire count field and returns an empty command list.
[RFC 8878 §3.1.1.3.2.1.2][rfc] · [Table resolution][prefix]

| Operation | Wire order |
| --- | --- |
| Initial states | Literal length, offset, match length |
| Command extra bits | Offset, match length, literal length |
| Updates between commands | Literal length, match length, offset |

FSE initialization reads the table's accuracy log. A transition adds its
field to the selected row's baseline. RLE uses one state and zero-bit
fields. On the final command the decoder consumes only the extra bits
and requires exact exhaustion. Commands retain the raw `Offset_Value`
for later execution. Repeat table mode is rejected. Frame dispatch,
Huffman and Parquet activation are outside this profile. Existing
execution profiles require match distance strictly below the RFC window
size. [Definitions][defs] · [Frame profile][profile]

`readResolved_sound` connects a checked prefix and successful suffix
decode to `PayloadWire`. The relation accounts for the marker, ordered
fields, looked-up symbols, alphabet and accuracy limits, and valid
initial, accessed and next states. The last rule leaves zero bits.
`decode_sound` includes the exact prefix boundary, both caller caps
and equality of the returned length with the declared sequence count.
[Theorem header][thms]

## Pinned differential

The test constructs four complete frames with pinned libzstd v1.5.7
at `f8745da6ff1ad1e7bab384bd1f9d742439278e99`. It writes normalized
counts with `FSE_writeNCount` and uses native decoding tables to choose
states and transition fields that reach the second command's symbols.
Each frame has two commands. Each FSE table reads a nonzero-width
transition field. Lean must return the exact authored triples
`(Literal_Length, Offset_Value, Match_Length)`. A separate Python
executor applies the expected commands to the fixture literals, including
overlapping matches and trailing literals. The full native decoder must
produce those same bytes. [Pinned source][zstd] · [Oracle runner][oracle]

| LL, OF, ML modes | Raw commands | Frame SHA-256 |
| --- | --- | --- |
| Predefined, RLE, transmitted | (17, 13, 35), (18, 10, 38) | `a087d5c2109be8bbe14602dd0edbce287ac9f88135bebc3be85958566415590c` |
| Transmitted, predefined, RLE | (17, 13, 35), (18, 6, 36) | `2875993ede6ff0f54831d4f64b69a7c25bea3e35355f77d914265d03b0b9e4f8` |
| RLE, transmitted, predefined | (17, 13, 35), (16, 6, 38) | `78d2ca45684d350cfbee604a7c15271129e5bb719b390e6eed375d96660914be` |
| Predefined, transmitted, transmitted | (17, 13, 35), (18, 6, 38) | `0ae5f21fceacb5783633248d49c892db33e9793c132a44533b507f3d193653d3` |

Both decoders reject absent and zero markers, underflow during
initialization, extra-field reads, transitions and the last command,
and an extra bit after the final command. Lean also checks both caller
caps, the zero count and zero-width RLE fields. [Lean regressions][tests]

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.SequenceDecode.Thms +Silmaril.Formats.Compression.Zstd.SequenceDecode.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-sequence-decode-oracle/check.py
```

[rfc]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1.3.2.1.2
[prefix]: zstd-sequence-tables.md
[profile]: zstd-rle-frame.md
[defs]: ../../Silmaril/Formats/Compression/Zstd/SequenceDecode/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/SequenceDecode/Thms.lean
[tests]: ../../Silmaril/Formats/Compression/Zstd/SequenceDecode/Tests.lean
[oracle]: ../../scripts/zstd-sequence-decode-oracle/check.py
[zstd]: https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99
