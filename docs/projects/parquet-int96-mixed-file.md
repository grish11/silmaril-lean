# Mixed-encoding INT96 in a selected Parquet leaf

`Silmaril.Formats.Parquet.Int96.Mixed.File.openFile` binds one flat
required or optional INT96 leaf in a checked, immutable Parquet source.
It applies the existing byte and total-row budgets and verifies that the
selected footer chunk intervals are disjoint. The caller supplies the UTC
or local proleptic interpretation. Successful reads retain exact
mathematical nanoseconds, including values beyond signed Int64.

[Checked selected-leaf binding](parquet-int96-dictionary-file.md) ·
[Mixed INT96 chunk profile](parquet-int96-mixed.md)

Each indexed read resolves the original group and chunk from the retained
snapshot and passes their metadata, the original source and the chunk limits
to `Int96.Mixed.read`. Each selected chunk must start with one leading
PLAIN dictionary. Subsequent V1 or V2 data frames may use encoding 0
(PLAIN) or encoding 8 (RLE_DICTIONARY). A PLAIN-only chunk without a
dictionary is outside this adapter's admission. The standalone PLAIN and
dictionary file readers retain their entry points and admission contracts.

`Checked.readAll` collects one ordered nullable slot list per footer row
group. It stops at the first failing group and returns precisely the
previous complete groups. The read error retains the group and column
ordinals, field name and original chunk error. When the chunk error
contains an original frame offset, entry index or logical slot, those
coordinates pass through unchanged. Each chunk still applies its framing
and admission checks before dispatching data bodies. Rebasing and Arrow
narrowing are separate profiles.

## Contracts

- `openFile_binding` relates an opened reader to the existing checked
  selection. `openFile_snapshot` and `openFile_disjoint` establish original
  source, leaf and selected spans, with the checked file and row budgets.
- `readGroup_of_selected` gives the original chunk call and error wrapper.
  `readGroup_wire` ties the original leaf and footer chunk to its bounded
  same-source frame walk. The ordered data frames flatten to the original
  group count.
- `readAll_sound` describes the complete groups in footer order or the
  completed prefix and original failed group read.

[Theorem header](../../Silmaril/Formats/Parquet/Int96/Mixed/File/Thms.lean)

## Independent fixtures

Pinned PyArrow 26.0.1 produces a V1 nanosecond file and a V2 microsecond
file. Each has an INT32 decoy before the selected optional INT96 leaf and
three groups of 24 rows. Each group has its own dictionary and genuine
writer fallback after two RLE_DICTIONARY data pages. Thrift 0.25.0
independently checks the original leading dictionary, the data tags
`8, 8, 0, 0`, exact frame extents, masks, references and PLAIN words.
PyArrow reads all selected groups. The V2 wire includes coordinates on
both sides of the signed Int64 nanosecond range.

The pinned controls corrupt a PLAIN word and a dictionary reference,
respectively, in the second group after a null. Lean checks the exact
nested error and the single complete preceding group. Additional controls
damage only the unselected column, alias two selected intervals and
reorder the first two footer groups while keeping their original page
bytes. The guards exercise selection, independent indexed reads, file and
chunk limits, and both explicit interpretations.

[Fixture generator and SHA-256 pins](../../scripts/parquet-int96-mixed-file/check-fixtures.py) ·
[Lean guards](../../Silmaril/Formats/Parquet/Int96/Mixed/File/Tests.lean) ·
[Pinned wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Int96.Mixed.File.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Int96.Mixed.File.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-int96-mixed-file/Axioms.lean
python3 -m venv /tmp/parquet-int96-mixed-file
/tmp/parquet-int96-mixed-file/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-int96-mixed-file/bin/python -I scripts/parquet-int96-mixed-file/check-fixtures.py
```
