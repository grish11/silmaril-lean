# Bounded Zstandard sequence execution

`Compression.Zstd.Sequence.execute` takes decoded literals, an array of
available preceding frame bytes, the incoming repeat offsets, and a
list of `Command`s. Each command carries a literal length, the decoded
`Offset_Value` before repeat resolution, and a match length. It emits
the command's literals followed by the match. Each matched byte
extends the working history before the next read, so matches can
overlap. The executor appends the exact final literal suffix and
returns the resulting block and repeat state.
[Sequences section][sequences] · [Sequence execution][execute] · [Lean definitions][defs]

`Offset_Value > 3` resolves to the value minus three and inserts the
distance at the front of the repeat list. Values 1 through 3 select
the first, second, and third registers when the literal length is
positive. With zero literals they select register two, register three,
or register one minus one. The special subtraction inserts its result
and rejects zero. The other repeat codes move the selected register to
the front. The dictionary-free initial state is `(1, 4, 8)`. The caller
passes the ending state of the preceding compressed block across
intervening raw or RLE blocks.
[Repeat offsets][offsets] · [Verified Table 18 correction][erratum]

The history array may contain at most the configured window. Every
distance must be positive, strictly below the window as stated in
§3.1.1.4, and no greater than the available history after that command's
literals. Every copy uses a proof-carrying index into the current
array. The regenerated block cap is the minimum of the caller's
budget, the window, and 128 KiB. The executor checks the remaining
budget before writing a command and before appending the final
suffix. These are logical byte bounds.

`resolve_sound` proves the repeat-offset transitions. `copy_sound`
proves that each byte is read at the requested distance from the
then-current history and that the array grows by exactly the match
length. `execute_sound` proves command denotation, exact final
literal suffix and literal-length accounting, the size and bound
of the result, and validity of the outgoing repeat offsets.
[Theorem header][thms]

Frame integration, dictionary history, FSE tables and bitstreams,
and literal decoding are outside this API. The checked-frame profile
still rejects nonzero sequences, and Parquet ZSTD remains unsupported.
[Parquet coverage][matrix]

## Independent fixtures

The oracle builds libzstd v1.5.7 at
`f8745da6ff1ad1e7bab384bd1f9d742439278e99`. The fixture writer
assembles standard 1 KiB-window frames with raw literal sections,
nonzero sequence counts, and three RLE-mode symbol tables. It writes
the offset extra bits and end marker directly in the backward
sequence bitstream. When there are two commands in one block their
RLE symbols agree, while their offset extra bits differ. Lean runs
the separately supplied decoded commands and preserves repeat state
across fixture blocks. The native decoder parses the frame and
supplies the output bytes used for comparison.
[Pinned libzstd source][zstd] · [Fixture writer][oracle]

| Accepted frame | Frame SHA-256 |
| --- | --- |
| overlap-and-final-literal | `e1a825f977ec922f34e754de2958b3b09df0aa1b7ba4e2560a9771e432997fbe` |
| all-repeat-transitions | `47045af5f18b2c0f0d35abae46e9f52f11c02f5fd3d813e560d7ed189c404e7c` |
| two-commands-in-one-block | `a76b8f6086be78356e03a114af7bab12c7750e403eaac0dd145c3d9e92f16d0b` |
| distance-one-below-window | `06cb2e1828b53cdda26b73e1c1178b0988d24075921498a548bb10216685f2a4` |

The rejection fixtures cover missing history or literals, a special
repeat that resolves to zero, and a budget that fits the commands
but excludes the final literal suffix. A boundary fixture at distance
exactly equal to the window decodes in libzstd and is rejected by
the strict RFC profile. The distance one below the window succeeds
in both. [Lean regressions][tests]

```sh
lake build --wfail +Silmaril.Formats.Compression.Zstd.Sequence.Thms +Silmaril.Formats.Compression.Zstd.Sequence.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -I scripts/zstd-literal-oracle/check_sequences.py
```

[sequences]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1.3.2
[execute]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1.4
[offsets]: https://www.rfc-editor.org/rfc/rfc8878#section-3.1.1.5
[erratum]: https://www.rfc-editor.org/eid6442
[defs]: ../../Silmaril/Formats/Compression/Zstd/Sequence/Defs.lean
[thms]: ../../Silmaril/Formats/Compression/Zstd/Sequence/Thms.lean
[matrix]: arrow-parquet-coverage.md
[zstd]: https://github.com/facebook/zstd/tree/f8745da6ff1ad1e7bab384bd1f9d742439278e99
[oracle]: ../../scripts/zstd-literal-oracle/check_sequences.py
[tests]: ../../Silmaril/Formats/Compression/Zstd/Sequence/Tests.lean
