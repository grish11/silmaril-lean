# Checked Parquet page CRC-32

Parquet Format 2.14.0 uses the standard IEEE CRC-32 on the exact bytes
of the page body as serialized to disk. Its optional `PageHeader.crc`
field has Thrift type `i32`. The header parser projects the signed
integer with `UInt32.ofInt`, so a negative field value carries its
unsigned modulo-`2^32` bit pattern. The input starts after the
serialized header and ends at the advertised compressed size. In V1 it
is the stored whole body. In V2 it includes the raw level sections
followed by the stored value section. Verification precedes any
decompression. The wire specification is pinned at
`04d56f291ff963e98bc37ab8100e2fc133ff583c`. The raw IDL SHA-256 is
`d1d9a663d5543789b63d7168179d9849db06958b02c70ba96ba46ffde9278f61`.
[Parquet checksum field][spec] · [Header projection][header]

## Verifier contract

Call `Page.Checksum.verify maxPayloadBytes source frame` with a frame
from `Page.readPage` or `Page.readChunk` on the same immutable
snapshot. The verifier checks the byte cap, header progress, adjacency,
exact compressed extent, and snapshot bound before using the body.
It computes the existing `Compression.Checksum.crc32` digest over
that slice for a present checksum. The frame's decoded header retains
its association with the snapshot through the caller's framing step.

| Result | Meaning |
| --- | --- |
| `.ok .absent` | The checked frame has no checksum field. |
| `.ok (.valid declared)` | The IEEE digest of the checked body equals the declared bits. |
| `.error (.mismatch declared computed)` | A checksum is present and the two bit patterns differ. |
| `.error .byteLimit` | The advertised on-disk byte count exceeds the supplied cap. |
| `.error .invalidExtent` | The capped frame fails the source geometry or length checks. |

This is a standalone check for already framed payloads. Format-specific
page admission and the policy for a missing checksum belong to its
caller. The existing PLAIN and dictionary scan profiles remain no-CRC.
Any future scanner adoption is a separate change to agree with the
scanner owner. [Existing IEEE CRC model][crc]

## Lean laws

- `signed_bits` relates the header's conversion to modulo-`2^32`.
- `payloadWithin_of_frameWithin` and `payloadWithin_of_readPage` connect
  the verifier's extent checks to the public framing contracts.
  `payload_exact` identifies the body with the exact bounded source slice
  and its advertised byte length.
- `verify_absent_iff`, `verify_valid_iff`, and `verify_mismatch_iff`
  characterize the three checksum outcomes, including equality or
  inequality against the existing polynomial model for a present CRC.

## Independent writer fixtures

PyArrow **26.0.1** at Arrow commit
`9e5d6978e9acf372cc989aaaf94e863fe8582c90` writes one 512-slot optional
INT32 Snappy page per case. Apache Thrift **v0.25.0** independently
extracts each header and its exact body. Python `zlib.crc32` supplies
the expected digest. The pins and environment are the same as the
flat page fixtures. [Arrow source][arrow] · [Pinned environment][recipe]

The V1 body has 99 stored bytes and checksum `c70eb149`, encoded as
signed `-955338423`. V2 stores 153 bytes, starting with 66 raw definition
bytes, and has checksum `3e64dc5b`. A third fixture omits the CRC field
and retains the V2 body. The oracle checks readback for all three. The
checksummed V2 fixture rejects independent one-bit changes in the first
definition byte and the first compressed value byte. Their exact digests
are `82927994` and `9399e02f`. The oracle also distinguishes the intended
digest from the header-inclusive and decompressed digests and from the
V2 values-only digest. Lean parses the real headers and checks both
valid digests, both mismatch digests, checksum absence, the byte limit,
and malformed extents. [Oracle][oracle] · [Fixtures][vectors] · [Lean examples][examples]

Manifest columns are page version, uncompressed body size, stored
body size, raw definition byte count (zero for V1), signed CRC field,
body CRC, V2 definition and value mutation CRCs, serialized header hex,
and serialized body hex. A dash marks an absent field or mutation.
The manifest SHA-256 is
`ec7ccfa867ab411b4f345856f67350f1e0208a3c8cf59c2f17dc341a7a205876`.

```sh
set -o pipefail
python3 scripts/parquet-page-crc32/PyArrowOracle.py |
  diff -u tests/formats/parquet-page-crc32/pyarrow-26.0.1.tsv -
lake build --wfail +Silmaril.Formats.Parquet.Page.Checksum.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.Page.Checksum.Examples
```

[spec]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L840-L857
[header]: ../../Silmaril/Formats/Parquet/Page/Header/Defs.lean
[crc]: ../../Silmaril/Formats/Compression/Checksum/Thms.lean
[arrow]: https://github.com/apache/arrow/tree/9e5d6978e9acf372cc989aaaf94e863fe8582c90
[recipe]: parquet-flat-page.md#independent-page-fixtures
[oracle]: ../../scripts/parquet-page-crc32/PyArrowOracle.py
[vectors]: ../../tests/formats/parquet-page-crc32/pyarrow-26.0.1.tsv
[examples]: ../../Silmaril/Formats/Parquet/Page/Checksum/Examples.lean
