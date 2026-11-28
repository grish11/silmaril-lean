# Zstandard sequence table prefixes

`SequenceTables.resolve` takes the caller-supplied exact extent of a
sequences section and checks byte and sequence-count limits before
constructing any tables. For a positive count it checks the reserved
bits and resolves the tables in literal length, offset, match length
order. Predefined mode consumes zero description bytes. RLE consumes
one symbol byte. Transmitted mode reads and builds one normalized-count
prefix per alphabet. The maximum symbol counts are 36, 32 and 53, and
the maximum accuracy logs are 9, 8 and 9, respectively. Repeat mode is
rejected. [RFC 8878 §3.1.1.3.2.1 and §4.1.1][rfc] · [Definitions][defs]

A zero count must exhaust the section. The two-byte encoding of zero
is accepted under the count equation and agrees with libzstd. A
positive count requires at least one reverse-stream byte. The result
preserves every reverse-stream byte for a later state decoder.
End-marker validation, state initialization and transitions, extra
bits and command count are obligations of that decoder. Frame
dispatch, Huffman literals and Parquet activation are outside this
increment. The existing frame profiles retain the strict RFC
distance bound, including their documented differential at equality.
[Existing frame profile][frame]

`resolveTable_sound` identifies the exact description and remainder
for each mode. `resolve_sound` establishes both caller caps and the
ordered split into the count, mode byte, three descriptions and
reverse stream. `suffix_exact` recovers the latter by dropping
exactly the preceding bytes. `fse_state_bounds` gives the alphabet
and accuracy bounds and ensures an in-width transition field stays
in range. [Theorem header][thms]

The differential builds pinned libzstd v1.5.7 at
`f8745da6ff1ad1e7bab384bd1f9d742439278e99`. It compares Lean's count,
prefix end, untouched suffix and all decoding rows with the native
`ZSTD_decodeSeqHeaders` tables. The fixture generator uses native
`FSE_writeNCount` and independently built native tables to construct
six complete single-command frames, including all three cyclic
permutations of the supported modes. The native full decoder must
produce `abcdabc`. The differential also covers the maximum accuracy
logs of all three alphabets, the three count widths, malformed and
truncated descriptions, Repeat mode, absent reverse stream and both
caller caps. [Pinned source][zstd] · [Oracle runner][oracle]

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.SequenceTables.Thms +Silmaril.Formats.Compression.Zstd.SequenceTables.Tests +Silmaril.Formats.Compression.Zstd.RleSequences.Defs
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-sequence-table-oracle/check.py
```

[rfc]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1.3.2.1
[defs]: ../../Silmaril/Formats/Compression/Zstd/SequenceTables/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/SequenceTables/Thms.lean
[frame]: zstd-rle-frame.md
[oracle]: ../../scripts/zstd-sequence-table-oracle/check.py
[zstd]: https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99
