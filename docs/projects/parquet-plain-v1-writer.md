# Bounded flat Parquet PLAIN INT32 V1 writer

`Silmaril.Formats.Parquet.PlainV1Writer.emit` writes one uncompressed V1
`PageHeader` and its body. Required input is a list of `Int32`. Optional
input is a list of nullable slots. Required leaves have no level section.
Optional leaves carry the V1 four-byte definition-length word and one
width-one Hybrid RLE run per slot. Present values use the existing PLAIN
INT32 writer in slot order. An empty optional page has a zero-length
definition section with the four-byte length word. The profile uses flat
leaves, UNCOMPRESSED, PLAIN, and the two V1 RLE encoding IDs. Output includes
the separate header and body and their concatenation. File framing, column
chunks, checksums, statistics, dictionaries, and V2 are outside the profile.

The caller supplies maximum header bytes, Compact traversal limits, slot and
definition-section limits, and the two body-byte limits. The body size and
slot count must fit nonnegative signed i32. The writer checks these bounds
before assembling the body. It emits the header through Compact signed
integer encoding and checks its exact typed recovery and stop offset with
`Page.readHeaderPrefix`. The body round trip is proved without running the
scalar decoder in the writer.

`body_length` gives the exact body size, `decode_body` recovers the original
slots under the declared bounds, and `emit_exact` identifies the parsed
header, consumed prefix, body and total wire sizes. `emit_roundTrip` gives
exact ordered slot recovery through `ScalarPage.decode` on emitted bytes.
[Public theorems](../../Silmaril/Formats/Parquet/PlainV1Writer/Thms.lean)

The format pins are Parquet format 2.14.0 at
`04d56f291ff963e98bc37ab8100e2fc133ff583c` and Apache Thrift 0.25.0 at
`27e8a425ffb498e190df3a12e239326bf5ba9ed6`.
[Coverage and specifications](arrow-parquet-coverage.md)

The independent oracle uses the pinned Thrift reader to check all five
emitted Compact headers. For the required, mixed and all-null cases, it
places each exact emitted page into a PyArrow-generated single-column V1
fixture, adjusts the enclosing size fields, and checks row readback through
PyArrow 26.0.1. The required scalar bytes also match PyArrow's own PLAIN
bytes. The two standalone empty pages are checked by Compact and the Lean
scalar reader because the oracle does not ask PyArrow to materialize a
zero-row data page. Reuse the PyArrow and NumPy wheel hashes and the exact
Thrift source archive from the existing reader fixtures.
[Wheel hashes](../../tests/formats/arrow-ipc/requirements.txt) ·
[Thrift archive hash and setup](parquet-flat-page.md#independent-page-fixtures)

```sh
lake build --wfail +Silmaril.Formats.Parquet.PlainV1Writer.Thms +Silmaril.Formats.Parquet.PlainV1Writer.Examples
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.PlainV1Writer.Examples'
lake env lean -DautoImplicit=false -DwarningAsError=true --run scripts/parquet-plain-v1-writer/Write.lean /tmp/plain-v1-pages
python3 scripts/parquet-plain-v1-writer/PyArrowOracle.py /tmp/plain-v1-pages
```
