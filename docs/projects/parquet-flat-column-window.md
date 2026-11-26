# Full-column reads with an OffsetIndex window diagnostic

`FlatColumn.Window.read binding limits policy decode indexLimits group first stop`
reads one selected column from the immutable checked Snapshot carried by
`binding`. The group ordinal and requested row bounds are zero-based.
The outer result is `Except (FlatColumn.Error ε) (Window.Result α)`.

The complete `FlatColumn.readColumn` runs first with its original policy,
bounds, and decoder. Its first error is the outer error for every window,
including empty, reversed, and partial windows. Only after success are
the rows sliced and the index checked. The returned rows are
`(slots.drop first).take (stop - first)`. This clips to the selected
group, with empty output when the requested interval has no rows.

The second field, `Result.indexPlan`, is a diagnostic on a successful
read. Its `Except OffsetIndex.Error (Option (List OffsetIndex.Window.Clip))`
type distinguishes a present plan, an absent index and a typed index
failure. These outcomes preserve the successful slice. A checked index
with an empty window yields `ok (some [])`. When a full read fails,
there is no success result or diagnostic. The checked Snapshot supplies
all underlying footer admission.

The diagnostic uses the same Snapshot, group and `binding.columnOrdinal`.
It replaces `indexLimits.page` with `limits.framing` so both checks use
the same original page frames and the same framing limits. Remaining
index validation caps come from `indexLimits`. File bounds and footer
validation belong to the caller's Snapshot opening step.

The operation is bounded by the complete column reader, including its
chunk, page, and row caps, and by the separate index limits. It
materializes the complete admitted column and may frame the chunk again
for the diagnostic. It checks every admitted page under the full reader's
existing order and error rules.
[Full column contract](parquet-flat-column.md) · [Index window contract](parquet-offset-index-row-window.md) · [Binder coordination](https://github.com/hiloopai/silmaril-lean/pull/4780#issuecomment-7199769304)

## Lean contracts

- `read_error_iff` equates the exact outer error to the original typed
  full-column error for arbitrary bounds and diagnostic limits.
- `read_rows` projects the outer observation to the original full read
  followed by the exact positional slice. `read_ok_iff` additionally
  specifies the diagnostic after success.
- `read_length` gives the admitted slice length from the selected
  group's footer count as `min stop groupRows - first`.
- `read_plan_sound` connects a present diagnostic to same-file
  `OffsetIndex.Evidence` for that selection and framing limit. Every
  original callback result follows that same frame list in wire order.
  The plan clips those entries and the rows slice the flattened full
  callback results.
[Lean theorem header](../../Silmaril/Formats/Parquet/FlatColumn/Window/Thms.lean)

## Independent fixture and error controls

The pinned optional PLAIN INT32 V1 uncompressed files come from the
existing OffsetIndex fixture family. PyArrow **26.0.1**, commit
`9e5d6978e9acf372cc989aaaf94e863fe8582c90`, produced them. Apache Thrift
**0.25.0**, commit `27e8a425ffb498e190df3a12e239326bf5ba9ed6`, independently
reads the original index and page extents. In zero-based row group 1, the
window `[3, 10)` crosses all three pages. PyArrow returns
`[null, 29, 32, 35, 38, null, 44]`. The no-index file and an in-bounds
index mutation yield those same rows with distinct diagnostics.

Changing byte 200 from `0x02` to `0xff` corrupts the definition-section
length in page 2, whose header starts at byte 183. Thrift confirms the
same frame header and PyArrow rejects that row group. The Lean examples
check the identical typed error for the full, earlier partial, and empty
windows, and repeat the empty case with both the late corruption and an
invalid index. Reader and index cap controls exercise the same precedence.
[Producer and dependency pins](parquet-offset-index.md#independent-files) · [Fixture and mutation hashes](../../scripts/parquet-flat-column-window/observations.txt) · [Lean examples](../../Silmaril/Formats/Parquet/FlatColumn/Window/Examples.lean)

Run from the repository root with the pinned Python dependencies on
`PYTHONPATH`.

```sh
set -o pipefail
python3 scripts/parquet-flat-column-window/Oracle.py |
  diff -u scripts/parquet-flat-column-window/observations.txt -
lake build --wfail +Silmaril.Formats.Parquet.FlatColumn.Window.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.FlatColumn.Window.Examples
```
