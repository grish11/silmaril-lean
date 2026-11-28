# Bounded Zstandard RLE sequence sections

`ReverseBits.start` takes an exact byte slice. The highest set bit
of the last byte is the end marker. The reader discards that bit
and the zero padding above it. It reads preceding bytes in reverse
wire order. Within a field, the first bit read is its most
significant bit. The cursor retains a count and a list of prior
bytes. Reads take bits as needed, including across byte boundaries.
Empty input and a zero last byte cannot open a stream.
[RFC 8878 reverse decoding][bits] · [Reader definitions][reader]

`RleSequences.decode` reuses the variable-size sequence count. A
zero-count section ends after that count. Every nonzero section
must have mode byte `0x54`, followed by one symbol each for literal
length, offset, and match length. The RFC length tables and offset
powers yield the bases and widths. Every command reads extra bits
in the order offset, match length, literal length and returns the
decoded offset value before repeat resolution. For offset symbols,
this profile admits 0 through 31.
[RFC 8878 modes][modes] · [RFC 8878 code tables][codes] · [Section definitions][defs]

Compressed-section bytes fit both the caller limit and 128 KiB.
A separate caller cap bounds the command count, including when
all fields have width zero. A successful nonzero section consumes
the exact bitstream through its first wire byte. Bad end markers,
bit underflow, and surplus bits have distinct errors. Nonzero
reserved bits are malformed. Predefined, compressed FSE, repeat,
and mixed-mode tables return `unsupportedModes`.
No frame or Parquet dispatch uses this decoder. The independent
sequence executor retains its strict window rule.
[Sequence execution profile][execution]

`ReverseBits.start_sound` identifies the highest set bit of the actual
last byte. `read_sound` proves exact cursor progression, remaining
width, field value and range. `isEmpty_iff` relates the end check to
empty abstract bits. `RleSequences.readCommand_sound` gives the
three fields and their bases in wire order. `payloadWidth` relates
the total width to the fixed widths of the decoded symbols, and
`decode_sound` proves the whole-section relation, exact exhaustion,
and both caps. [Reader theorems][reader-thms] · [Section theorems][thms]

## Independent fixtures

The oracle builds libzstd v1.5.7 at
`f8745da6ff1ad1e7bab384bd1f9d742439278e99`. libzstd's raw literal
writer supplies each literal section. The fixture writer adds the
declared RLE symbols, extra fields, end marker, and enclosing frame.
The Lean driver checks decoded commands against the authored tuples
and compares execution output with libzstd's frame decoder.
[libzstd source][zstd] · [Oracle runner][oracle]

| Accepted frame | Frame SHA-256 |
| --- | --- |
| zero-count | `4a3077cf8428145dedbf7445d9dc8004082fdd6f1519fab82604d918362fc1fa` |
| overlap | `e1a825f977ec922f34e754de2958b3b09df0aa1b7ba4e2560a9771e432997fbe` |
| cross-byte-fields | `dfe5f5cb82ac6e361769124d0b3739c93ebbd2e8ea64b09a20898741f83c4185` |
| two-commands | `42938b349dec8f4f14661e57ddc830e94ab5983bfe069f6b03b602a3ae8dca10` |
| two-byte-count | `8c648d9a64d6e3f7cb01b6039fcccfcfbd6a9d82b311acb45471537f51145827` |

The accepted cases cover zero sequences, overlap, nonzero extra
fields across bytes, two commands sharing symbols, and a two-byte
sequence count. The controls include reserved mode bits, missing
or zero end-marker bytes, underflow, surplus bits, and invalid
symbols for all three tables. A native predefined-mode frame
decodes in libzstd and returns `unsupportedModes` in Lean. The
suite also checks caller command limiting.
[Lean regressions][tests]

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.ReverseBits.Thms +Silmaril.Formats.Compression.Zstd.RleSequences.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-literal-oracle/check_rle.py
```

[bits]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1.3.2.1.2
[modes]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1.3.2.1
[codes]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1.3.2.1.1
[reader]: ../../Silmaril/Formats/Compression/Zstd/ReverseBits/Defs.lean
[reader-thms]: ../../Silmaril/Formats/Compression/Zstd/ReverseBits/Thms.lean
[defs]: ../../Silmaril/Formats/Compression/Zstd/RleSequences/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/RleSequences/Thms.lean
[execution]: zstd-sequence-execution.md
[zstd]: https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99
[oracle]: ../../scripts/zstd-literal-oracle/check_rle.py
[tests]: ../../Silmaril/Formats/Compression/Zstd/RleSequences/Tests.lean
