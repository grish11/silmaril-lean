# Checked ordered mixed Parquet row groups

`Silmaril.Formats.Parquet.MixedV1Writer.Multi.emit limits input`
writes one flat Parquet file with a fixed INT32 then opaque BYTE_ARRAY
schema. The caller declares exact names and required/optional layouts
and supplies the two typed page inputs for each row group in order.
Each group's two slot lists must align, and each page input must agree
with the shared layout. The writer uses the same uncompressed PLAIN V1
page encoders as the [single-group writer][single]. Each group gets two
consecutive chunks and a real footer entry. The footer comes after
the final group and records all absolute offsets and counts.

The writer checks its group count, the footer collection cap and the
aggregate row count before measuring pages. Measurement bounds each
page and the total data area before encoding page bodies. The footer
serializer receives the space remaining after the data and trailer,
within the separate footer budget. Each page and the existing mixed
reader remain subject to their own limits. A reader refusal retains
the original cause and ordinal. After assembly the writer checks
exact metadata, contiguous group windows and each page body, then
reads back each original group before returning a file.

`emit_checked` exposes bounds, alignment, footer and page checks.
`emit_indexed` proves that footer ordinal `i` reads exactly the
input's paired slots at `i`, through the existing [mixed reader][reader].
`emit_empty` applies at any valid zero-row ordinal, including an interior
group. Such groups have real page headers and in-file offsets. An
empty list of groups is rejected by this profile. [Theorems][theorems]

The [oracle][oracle] pins three complete Lean files with row-group
shapes `[2, 1]`, `[1, 0, 2]`, and a 16-entry footer list with an
empty interior group. Thrift 0.25.0 checks absolute offsets, exact
headers and nullable bodies. PyArrow 26.0.1 reads every group at its
original ordinal, including empty groups and null versus present
empty octets. The existing single-group oracle checks its five prior
hashes, and the same singleton input through the multi-group API
produces exactly the pinned single-group bytes. Lean also checks
exact aggregate caps, out-of-range reads, and eight typed refusals,
including a reader refusal after an empty group.

```sh
lake build --wfail +Silmaril.Formats.Parquet.MixedV1Writer.Multi.Checks
python3.13 scripts/parquet-mixed-v1-multi-writer-oracle/check.py --out /tmp/parquet-mixed-v1-multi
```

[single]: parquet-mixed-v1-writer.md
[reader]: ../../Silmaril/Formats/Parquet/Int32ByteArrayGroup/Thms.lean
[theorems]: ../../Silmaril/Formats/Parquet/MixedV1Writer/Multi/Thms.lean
[oracle]: ../../scripts/parquet-mixed-v1-multi-writer-oracle/check.py
