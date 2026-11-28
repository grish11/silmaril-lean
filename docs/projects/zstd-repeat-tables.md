# Stateful Zstandard Repeat table resolution

`SequenceTables.Repeat.resolve` takes the exact sequences-section extent
and the prior table state. Start a dictionary-free frame with
`State.empty`. A Repeat mode field uses the table from the same alphabet
in the last accepted positive-count section. It consumes zero table
description bytes and fails if that alphabet has no prior table.
Predefined, RLE and transmitted modes select fresh tables even if other
alphabets repeat. A zero count must exhaust the section and preserves
the entire prior state. [RFC 8878 §3.1.1.3.2.1][rfc] · [Definitions][defs]

Successful resolution returns the exact reverse-stream suffix and a
proposed successor. The caller uses that successor for the next block
after accepting this block's payload. A parse error returns no
successor. The state constructor is private and this profile starts
without a dictionary. The existing stateless resolver continues to
reject Repeat mode. Dictionary seeding, reverse-payload integration,
Huffman and Parquet activation are outside this slice.
[Stateless table resolver][stateless]

`resolveTable_repeat` states when a Repeat consumes zero description
bytes and when it fails. `resolveTable_sound` and `resolve_sound`
establish the exact wire partition, caller limits, and which fresh or
retained tables become the successor. `suffix_exact` gives the exact
unread suffix. `empty_valid` and `resolve_preserves_valid` establish
that every table carried forward can be traced to a checked description
for its own alphabet. [Theorem header][thms]

## Pinned differential

The test carries one context through five sections using libzstd v1.5.7
at `f8745da6ff1ad1e7bab384bd1f9d742439278e99`. It compares Lean's
boundaries and every selected table row with `ZSTD_decodeSeqHeaders`.
It also checks the exact reverse suffix against the fixture. The
public libzstd decoder accepts the same five sections in one full
frame and agrees with independently computed output. [Pinned source][zstd] · [Oracle runner][oracle]

| Block | Literal length mode | Offset mode | Match length mode | Sequences section hex |
| --- | --- | --- | --- | --- |
| 1 | Predefined | RLE | Transmitted | `011802103f0322` |
| 2 | Empty section | | | `00` |
| 3 | Repeat | Repeat | Repeat | `01fc0322` |
| 4 | RLE | Transmitted | Repeat | `016c05108a1f0023` |
| 5 | Repeat | Repeat | Repeat | `01fc1823` |

Block 3 reuses all three tables from block 1. Block 4 replaces two
tables, which block 5 uses while retaining the match-length table
from block 1. The frame SHA-256 is
`2a981ed36448af6a2958586fc9be859976a1b86c2e32b09d2d9f041cf4d97b06`.
Both implementations reject each unseeded Repeat mode, including
after a leading empty section. [Lean regressions][tests]

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.SequenceTables.Repeat.Tests +Silmaril.Formats.Compression.Zstd.SequenceTables.Tests +Silmaril.Formats.Compression.Zstd.SequenceDecode.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-repeat-table-oracle/check.py
```

[rfc]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1.3.2.1
[defs]: ../../Silmaril/Formats/Compression/Zstd/SequenceTables/Repeat/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/SequenceTables/Repeat/Thms.lean
[stateless]: zstd-sequence-tables.md
[tests]: ../../Silmaril/Formats/Compression/Zstd/SequenceTables/Repeat/Tests.lean
[oracle]: ../../scripts/zstd-repeat-table-oracle/check.py
[zstd]: https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99
