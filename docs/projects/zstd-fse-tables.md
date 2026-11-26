# Bounded Zstandard FSE table construction

`FseTable.build` accepts a distribution of already normalized
signed weights in symbol order and its accuracy log. It checks
the log and alphabet caps, rejects weights below −1, requires
at least two active symbols, and checks that the total allocated
slots equal the power-of-two table size. The profile permits
accuracy logs 5 through 9 and up to 256 symbols. Callers can
lower the upper bounds for their table context.
[RFC 8878 FSE][fse] · [Definitions][defs]

A weight of −1 reserves one state at the high end, with reserved
states assigned in reverse symbol order. The ordinary symbols
follow the RFC modular walk from state zero, skipping reserved
states. For each symbol, the row ordinal starts at its allocated
slot count and advances in state order. A row reads
`log - floor(log₂ ordinal)` bits. Its baseline is the ordinal
scaled by that field's size, minus the table size. Construction
checks full state coverage, symbol multiplicities, and the width
and destination interval of every row. The largest table is 512
rows. [RFC 8878 table construction][construct]

`build_sound` proves that successful construction validates the
distribution, covers the state range, follows the placement
relation and yields the normalized multiplicities. `row_agrees`
relates a looked-up row to the placed symbol and row formula.
`state_bounds` proves that the source state, decoded symbol,
field width and all possible destination states are in range.
`selectPredefined_sound` proves the zero-byte consumption rule
for predefined mode. `table_size_le` bounds the table by
the capped accuracy log.
[Theorem header][thms] · [RFC 8878 Appendix A][appendix]

The mode selector takes the already extracted per-alphabet mode
and preserves the incoming byte suffix. It supplies all three
predefined sequence alphabets for mode zero and returns an
explicit error for other modes. Transmitted normalized-count
bits, symbol-state decoding, table reuse, and sequence/frame
integration are outside this slice. The strict window rule and
its libzstd differential remain part of the existing RLE frame
profile. Parquet ZSTD remains unsupported.
[Predefined distributions][defaults] · [RLE frame profile][rle-frame]

## Independent table differential

The oracle builds libzstd v1.5.7 at
`f8745da6ff1ad1e7bab384bd1f9d742439278e99`. The reference driver
uses the pinned library's own predefined distributions and calls
`FSE_buildDTable_wksp`. For authored distributions it sends the
same normalized weights to both builders. It compares every
state's symbol, field width and baseline, plus the accuracy log.
The hashes cover the log on the first line and one
`symbol width baseline` line per state in state order.
[Reference source][zstd] · [Oracle runner][oracle]

| Fixture | States | Table SHA-256 |
| --- | ---: | --- |
| predefined-literal | 64 | `a06da99b2748e7ba0147b6376b2329f41786fabbea470a91f0562ebedc3332c2` |
| predefined-offset | 32 | `46f1871a6e3f26348a1be159f36a6bc5a09815e5d8346eba63d909ca3ee9eb28` |
| predefined-match | 64 | `4700814ba7889242969d33a4122071ebe505d8061fa19ce00e14c7216e13d53c` |
| even | 32 | `fbcd5bd54f3793c1406fa33c2d07915d58e96c8578a966fc3c976f9ccfa1a5ff` |
| skew | 32 | `9ca16ed257ec21d9bb31c0781908d0e6a74f42083e2379b37c86073fd1f339a1` |
| sparse | 32 | `80833891c24f4f97d81f90f23afaea0fc251868651b6a6e4971d2cfa0edd27e2` |
| all-low | 32 | `cc1f26073494b1dbcf897e11700346f0065ce9506c0ef9573c14ecc7c431a451` |
| largest-table | 512 | `115e8fb2735ff9b4b03f8cf05e8b0cd7a67edef4536a38802e6c7a80b485ece7` |
| symbol-255 | 32 | `8a4e8bf8ebe78a2b05c465000cfbe5307ac6bc0ab895573cf7a3321f034c2c1e` |

The controls check log and alphabet caps, illegal negative
weights, one active symbol, and normalized mass below or above
the table size. The differential only passes validated normalized
inputs to the native table builder. The Lean tests also check
caller-specific caps, reserved state placement for −1 weights, and
predefined suffix preservation.
[Lean regressions][tests]

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.FseTable.Thms +Silmaril.Formats.Compression.Zstd.FseTable.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-fse-oracle/check.py
```

[fse]: https://www.rfc-editor.org/rfc/rfc8878#section-4.1
[construct]: https://www.rfc-editor.org/rfc/rfc8878#section-4.1.1
[appendix]: https://www.rfc-editor.org/rfc/rfc8878#appendix-A
[defaults]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1.3.2.2
[rle-frame]: zstd-sequence-execution.md
[defs]: ../../Silmaril/Formats/Compression/Zstd/FseTable/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/FseTable/Thms.lean
[tests]: ../../Silmaril/Formats/Compression/Zstd/FseTable/Tests.lean
[oracle]: ../../scripts/zstd-fse-oracle/check.py
[zstd]: https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99
