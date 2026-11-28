# Nested Parquet definition-level presence

`NestedPresence.decodeV1` checks one caller-paired, uncompressed, CRC-free
PLAIN Data Page V1 body. Its definition-level profile is one optional
unannotated struct with a required or optional direct physical leaf.
`childOf` obtains the leaf's repetition from the checked footer selection.
The caller supplies the original paired header and body and checks the
column codec. This entry point leaves the value bytes available to a
physical decoder.

Parquet definition levels count defined optional fields along the path.
There are no repeated nodes in this profile. For a required child,
one-bit levels 0 and 1 indicate absent parent and present value. For an
optional child, two-bit levels 0, 1, and 2 indicate absent parent, present
parent with a null child, and present value. The unused level 3 is rejected.
The V1 profile requires RLE header tags and starts with the four-byte
little-endian definition-section length. The delimited section uses the
existing bounded Hybrid reader, including its final bit-packed padding
rules. Value-section consumption is the caller's responsibility.
[Pinned nested encoding](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/README.md#nested-encoding) · [Pinned Hybrid wire framing](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#run-length-encoding--bit-packing-hybrid-rle--3)

`classify_contract` proves each state exactly characterizes the relevant
schema and level. `decode_wire` witnesses the length word, exact Hybrid
section, original untouched suffix, range-checked ordered levels, and
one state per declared slot. `decodeV1_wire` ties these to the checked
header tags and both advertised sizes. This slice is page-local and does
not reconcile sibling page boundaries, assemble structs across pages, or
interpret value encodings. The flat readers and scanner admission remain
on their existing contracts.
[Public theorems](../../Silmaril/Formats/Parquet/NestedPresence/Thms.lean)

## Producer evidence

The pinned PyArrow 26.0.1 optional `point` fixture contains a required
INT32 leaf and an optional INT64 leaf. The independent Thrift probe
locates both original pages, checks their exact headers and decodes the
observed packed groups directly. The required leaf emits `[1, 0, 1]`
and the optional leaf emits `[2, 0, 1]`. PyArrow independently reads the
three struct rows. Lean exercises both checked footer bindings and the
original frames, then passes the untouched PLAIN bytes through the
existing INT32 and INT64 readers in the example. Additional controls
cover impossible level 3, truncated and surplus section bytes, body
caps and size mismatches, unsupported level tags, and CRC.
[Fixture and producer pins](parquet-nested-footer-leaf.md#independent-fixtures) · [Independent probe](../../scripts/parquet-nested-presence/Oracle.py) · [Observed bytes](../../scripts/parquet-nested-presence/observations.txt)

```sh
set -o pipefail
python3 scripts/parquet-nested-presence/Oracle.py |
  diff -u scripts/parquet-nested-presence/observations.txt -
lake build --wfail +Silmaril.Formats.Parquet.NestedPresence.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.NestedPresence.Examples
```
