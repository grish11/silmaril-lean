# Checked indexed Arrow DATE IPC files

`Arrow.DateFile.readIndex` admits a finite immutable Arrow IPC V5 file with
one flat little-endian DATE field. It supports signed Date32 days and
Date64 milliseconds that represent exact whole days. The footer and
embedded Schema must agree on the complete normalized Schema, including
field name, nullability, and DateUnit. An omitted MILLISECOND unit and an
explicit MILLISECOND unit normalize to the same value.
[File profile and framing](arrow-ipc-file.md)
· [DATE stream profile](arrow-date-stream.md)
· [Pinned File.fbs](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/File.fbs)
· [Pinned Schema.fbs](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs)

Index admission checks the footer extent, normalized Schema agreement,
contiguous aligned blocks, and the exact modern EOS before the footer.
It leaves each block's Message and contents for selected validation.
`Index.readAt` returns `.ok none` for an absent entry. For a present
entry it checks the original envelope and Message lengths against the
footer before taking the body window. It then uses the DATE batch value
decoder. Errors carry the zero-based block index and the stage. A bad
value in one block leaves earlier or later selected reads independent.
[Executable API](../../Silmaril/Formats/Arrow/DateFile/Defs.lean)

`readIndex_exact` ties the footer and embedded Schema to the retained
field. On selected success, `Index.readAt_exact` gives the original
padded metadata octets after the eight-byte envelope, the original
body octets, and the same DATE observation from standalone
`DateBatch.decode`. `readAt_absent_iff` and `readAt_error_iff` distinguish
absence from the selected record's typed failure.
[Theorem header](../../Silmaril/Formats/Arrow/DateFile/Thms.lean)

`Index.readAt_sequential` agrees with a successful traversal of the same
checked footer entries in order. `Index.readAt_stream` requires successful
file and stream observations, the same normalized field, and
`BatchesCorrespond` in order. Correspondence pairs the framed batches
by equal parsed record Message metadata and equal body octets. This
permits different backing byte trees and checks the relation on batch
inputs rather than assuming their decoded DATE values agree.

## Independent fixtures

CPython 3.13.5 and PyArrow 26.0.1 generate four real files. PyArrow
independently reads the raw signed words in reverse index order and
checks the same observations from the embedded sequential stream. The
Date32 and Date64 files include signed endpoints, negative epoch dates,
nulls, a UTF-8 label, and an empty middle batch. The third file carries
only a required Date32 Schema. The fourth carries a late −1 ms Date64
word. Lean admits that file's index and reports
`.batch 2 (.values (.nonWholeDay 1))` only when that batch is selected.
The existing stream reader reports the same indexed value failure,
and the first two indexed reads still match the original slots.

One separate mutation changes only the footer's explicit DAY unit to
MILLISECOND. Lean rejects the mismatch at admission. Two derived
controls change the last batch's framed metadata size and Message body
length independently. The index admits both files and selected read
rejects the differing length, preserving the neighboring observations.
[Fixture manifest](../../scripts/arrow-date-file-oracle/fixtures.json)
· [Independent producer and checker](../../scripts/arrow-date-file-oracle/check.py)
· [Lean regressions](../../Silmaril/Formats/Arrow/DateFile/Tests.lean)

```sh
targets='+Silmaril.Formats.Arrow.DateFile.Thms +Silmaril.Formats.Arrow.DateFile.Tests +Silmaril.Formats.Arrow.DateStream.Tests +Silmaril.Formats.Arrow.MixedFlat.File.Examples +Silmaril.Formats.Arrow.TimestampBatch.Thms arrow_ipc_metadata_tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/arrow-date-file/Axioms.lean
python3 -I scripts/arrow-date-file-oracle/check.py
```

Use `--pyarrow-path` for a separately unpacked pinned wheel.
