# Opt-in CRC verification for flat Parquet scans

`Parquet.Snapshot.FlatInt32Dictionary.readAllWithCRC checksumLimit limits
schema bytes` reads flat required and optional uncompressed INT32 columns.
It accepts pages with no CRC and checks any declared CRC. The caller passes
the full physical schema in wire order. `bindWithCRC` supplies the same
policy to the checked Snapshot cursor for callers with an explicit input
byte cap. The lower-level `FlatScan.scanColumnWithCRC` and
`DictionaryChunk.scanColumnWithCRC` apply the policy to one column.
[Snapshot reader][snapshot] · [Standalone page verifier][verifier]

## Check before decoding

Column admission keeps the existing schema, count, codec, framing, and
materialization limits. After `Page.readChunk`, the prepass visits the
original frames in wire order. It passes each frame and the same immutable
source to `Page.Checksum.verify`. It checks the full serialized payload
extent, including V2 levels, and uses the smaller of the requested
checksum byte cap and the column reader's compressed payload cap for
that kind of page. Dictionary pages use the dictionary body cap.

The entire reached column passes the prepass before the scanner decodes
any of its bodies. PLAIN, dictionary, and dictionary-coded data pages use
the existing physical decoders. The legacy entry points still reject
CRC-bearing pages. The opt-in path accepts codec 0 and keeps the same
physical types and encodings as the respective column readers.

A prepass failure keeps the original page ordinal and absolute header
offset. Its typed cause distinguishes the payload byte cap, invalid
extent, and mismatch. A mismatch carries both the declared and computed
CRC bits. Snapshot also reports the original group and column ordinals
and the field name. It retains earlier complete batches, and the failed
group contributes no batch.

`verifyFrames_ok` characterizes successful verification of every frame.
`verifyFrames_errorFrame` ties the failure index, offset and reason to the
original list member. `readChunkWithCRC_ok` retains the exact successful
`Page.readChunk` equation on the same immutable source and the verifier
result for every returned frame. [Theorem header][thms]

## Independent fixtures

The new uncompressed mixed V1 file and the reused V2 files come from
PyArrow **26.0.1** at `9e5d6978e9acf372cc989aaaf94e863fe8582c90`.
The [oracle][oracle] reads the complete files with checksum verification,
locates exact wire fields with Apache Thrift **0.25.0**, and checks CRCs
with Python `zlib.crc32`. The verifier pins Parquet Format **2.14.0**.

Four independent V2 mutations target a PLAIN payload, a dictionary body,
and the definition and index sections of a dictionary-coded page. Each
retains the eight rows of group 0 and rejects group 1. Lean checks the
exact original page, column and group location and CRC bit patterns for
all four mutations. The regression also covers absent CRC, legacy CRC
rejection in both branches, Snappy rejection, invalid extent and byte cap
errors, and checksum failure before an earlier page's scalar callback.
[Lean regressions][checks] · [Reused fixtures][snapshot]

| New fixture | SHA-256 |
| --- | --- |
| `crc-mixed-v1.parquet` | `08af89eeee408df4360543f08be6d4ab37c22717c7415264737f530b076d4cd8` |
| `mutations.tsv` | `b9604c0526f6b8cc8d07894138e264b014e798f1c0c316741aa0072f34485e6a` |

From the repository root with the [PyArrow and Thrift pins][pins] available.

```sh
fixture_tmp=$(mktemp -d)
python3 scripts/parquet-crc-scan/Oracle.py "$fixture_tmp" --write > "$fixture_tmp/mutations.tsv"
diff -r data/parquet-crc-scan "$fixture_tmp"
lake build --wfail +Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.CRCChecks
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.CRCChecks +Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.Checks +Silmaril.Formats.Parquet.DictionaryChunk.Examples +Silmaril.Formats.Parquet.Page.Checksum.Examples +Silmaril.Formats.Parquet.FlatInt32Writer.Readback.Arrow.Thms parquet-flat-scan-regression parquet-page-regression'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-crc-scan/Axioms.lean
```

[snapshot]: parquet-dictionary-snapshot.md
[verifier]: parquet-page-crc32.md
[pins]: parquet-flat-page.md#independent-page-fixtures
[thms]: ../../Silmaril/Formats/Parquet/Page/Checksum/Scan/Thms.lean
[oracle]: ../../scripts/parquet-crc-scan/Oracle.py
[checks]: ../../Silmaril/Formats/Parquet/Snapshot/FlatInt32Dictionary/CRCChecks.lean
