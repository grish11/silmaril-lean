# Dictionary-to-PLAIN Parquet TIMESTAMP fallback

`Timestamp.Leaf.Fallback.convert` explicitly selects the fallback profile
for one flat required or optional INT64 TIMESTAMP leaf. It uses the
selected serialized leaf ordinal, with the root at zero. The existing
annotation profile determines admission, unit and UTC versus local
interpretation. The IPC output preserves signed ticks, nullability and
footer-order groups under that descriptor.

Every selected chunk must be uncompressed and have this wire sequence.

1. One leading PLAIN dictionary page at the footer's dictionary offset.
2. One or more RLE_DICTIONARY data pages, starting at the footer's data
   offset.
3. One or more PLAIN data pages through the end of the chunk.

The data pages may use V1 or V2. A PLAIN first data page, a missing PLAIN
suffix, or a return to dictionary encoding after PLAIN fails admission.
This profile requires the transition in each selected chunk. Dictionary-only
chunks use the existing dictionary reader. The regular converter keeps its
PLAIN profile and Snappy opt-in. Compressed dictionaries are refused here.

[Dictionary-only profile](parquet-timestamp-dictionary.md) ·
[PLAIN Snappy profile](parquet-timestamp-snappy.md) ·
[Parquet encodings](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md)

## Wire and error contracts

The fallback reader uses the dictionary reader's checked snapshot, chunk
selection, offsets, framing, limits and bounded PLAIN dictionary decode.
Planning checks the full page sequence and declared slot total before
decoding bodies. Each data header selects the existing decoder for its
original payload. RLE_DICTIONARY resolves the exact references against
that chunk's dictionary. PLAIN reads exact signed words and reconstructs
the nullable slots from the checked level mask.

`checkGroup_wire` records the contiguous frames, original offsets and
the nonempty dictionary and PLAIN segments. `readGroup_wire` identifies
the decoder and nullable slot list for every data frame. Its concatenation
preserves order across the transition. `readBound_reference` and
`convert_readback` tie those group results to the original footer order and
the native IPC stream through EOS.

After planning, a failed data decode preserves the original wire ordinal,
absolute header offset and typed cause. Events retain the preceding complete
groups. IPC conversion returns the original group error before sink admission.

[Theorem header](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Fallback/Thms.lean)

## Independent readback

The pinned oracle reproduces the genuine local micros V2 fallback file from
the dictionary-only regression and adds two-group UTC micros V1 and V2
files from the same PyArrow writer. The latter include nulls, negative
counts and both signed Int64 endpoints. Thrift checks the original offsets,
encoding sequence, definition masks, packed references and PLAIN words.
PyArrow independently reads the ordered signed slots from the Parquet files
and the actual Lean-emitted Arrow V5 streams.

A late control truncates one byte from the last PLAIN word in group 1,
page 6 of the V2 file, with matching header and footer extents. PyArrow
rejects that group. Lean retains the first group and returns the PLAIN
truncation at the original header offset. Other controls exercise default
refusals, dictionary-only input, a PLAIN first data page, dictionary
reentry and compressed dictionary input.

[Oracle](../../scripts/parquet-timestamp-fallback-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-fallback-oracle/fixtures.json) ·
[Pinned wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Timestamp.Leaf.Fallback.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-fallback-oracle/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-fallback
/tmp/parquet-timestamp-fallback/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-fallback/bin/python -I scripts/parquet-timestamp-fallback-oracle/check.py
```
