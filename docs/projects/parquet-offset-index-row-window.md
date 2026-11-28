# Parquet row windows over a checked OffsetIndex

`OffsetIndex.Window.plan first stop index` takes an already validated
index and returns its intersecting pages in file order. The request is
half-open and relative to one row group. Each clip retains the original
indexed entry and its framed header and payload spans. Its group-relative
bounds are the maximum of the two starts and the minimum of the two
stops. `Clip.localBounds` subtracts the original page's first row.

For a group of `groupRows` rows the admitted interval is
`[first, min stop groupRows)`. Empty and reversed requests produce an
empty plan. A request starting at or beyond the group end likewise
produces an empty plan. A larger stop clips at the group end.

`Window.planChecked limits snapshot group column first stop` first calls
the existing OffsetIndex validator on the selected column of the checked
immutable snapshot. A valid index with an empty plan returns `ok (some [])`.
A missing index returns `ok none`. The selected index is validated even
for an empty request, so all index errors propagate with their original
types. Plans contain row bounds and frame metadata only. Payload decoding,
skipping payload errors, and Hive partition pruning belong to their own
contracts.
[OffsetIndex entry point and profile](parquet-offset-index.md)

## Lean contracts

- `clip_some_iff` specifies the exact nonempty intersection and its
  original entry. `clip_localBounds` bounds the rebased interval by
  the original page's row extent.
- `plan_entries_sublist` proves the plan keeps an ordered subsequence
  of the original entries. `plan_frameOrder` and `plan_frames_nodup`
  use the checked file's actual frame sequence to prove strictly ordered
  byte offsets and unique frames.
- `plan_rowOrder` proves the group-relative row clips are ordered and
  disjoint. `plan_rowMultiplicity` proves every row in the admitted
  interval occurs in exactly one clip and all others in zero clips.
  `plan_empty_iff` specifies all empty results on a checked index.
- `planChecked_present` supplies the same-file `OffsetIndex.Evidence`
  for the result. `planChecked_absent_iff` and `planChecked_error_iff`
  specify what the caller observes at either boundary.
[Lean theorem header](../../Silmaril/Formats/Parquet/OffsetIndex/Window/Thms.lean)

The reusable physical column binder retains the original
`Page.readChunk limits source chunk = .ok frames` equation. The index
evidence supplies that same equation over the same snapshot, page limits
and selected chunk. A caller with a validated index can use `Window.plan`
directly. A caller starting at a checked snapshot can use
`Window.planChecked`.
[Physical column binder handoff](https://github.com/hiloopai/silmaril-lean/pull/4745#issuecomment-7198948669)

## Pinned independent fixture

The V2 Snappy and V1 no-index files are reused from #4745. PyArrow
**26.0.1** at Arrow commit `9e5d6978e9acf372cc989aaaf94e863fe8582c90`
wrote them. Apache Thrift **0.25.0** at commit
`27e8a425ffb498e190df3a12e239326bf5ba9ed6` reads the raw footer, index
locations, and frame headers independently. PyArrow reads the full
group and slices its resulting rows. Group 1 of the V2 file contains
twelve optional INT32 values across three pages. The test checks
windows spanning page boundaries, exactly one page, the clipped
end of the group, empty and reversed bounds, and starts at and
past EOF of the group. Lean compares the resulting original frame
offsets, header-inclusive sizes and page-local bounds, checks the
absence boundary on the V1 file, and propagates a tampered V2 index's
offset mismatch even for an empty request.

The V2 Snappy fixture hash is
`4433b34caef2f7c53c1b6cd0a94c5f6e3b748c4b830df633b96b40855e46f401`.
The V1 no-index fixture hash is
`7b1053e77957f849fd6c72fbfb9e8260037ae20dfa2d0d550b3b97f7014ba915`.
[Producer and dependency pins](parquet-offset-index.md#independent-files) · [Independent observations](../../scripts/parquet-offset-index-row-window/observations.txt) · [Lean fixtures](../../Silmaril/Formats/Parquet/OffsetIndex/Window/Examples.lean)

From the repository root with the pinned packages on `PYTHONPATH`, run

```sh
set -o pipefail
python3 scripts/parquet-offset-index-row-window/Oracle.py |
  diff -u scripts/parquet-offset-index-row-window/observations.txt -
lake build --wfail +Silmaril.Formats.Parquet.OffsetIndex.Window.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.OffsetIndex.Window.Examples
```
