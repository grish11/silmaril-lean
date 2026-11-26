# Checked Parquet RLE BOOLEAN row groups

`Silmaril.Formats.Parquet.RleBoolean.readGroup limits source name ordinal`
reads one selected group of a plaintext file with one named optional
flat BOOLEAN leaf. It returns ordered `List (Option Bool)` and uses a
zero-based group ordinal. The column must be uncompressed, advertise
RLE (3), and use actual value tag 3 on every page. The reader rejects
CRC-bearing pages, dictionary and index pages, and other value
encodings and codecs.

## V1 and V2 admission

The pinned Parquet Format **2.14.0** encoding table gives BOOLEAN
values a four-byte little-endian RLE length in both Data Page V1 and
V2. This is separate from the definition level extent. Pinned
PyArrow **26.0.1** writes and reads the optional tag-3 profile in
both versions. The independent fixtures exercise V1 RLE level tags
and V2 raw level extents. The bounded scalar preparation supplies
the checked definition mask and the entire value suffix to the
existing width-one hybrid decoder. Its inherited run and final
padding contracts apply.
[Format table][spec] · [Pinned Arrow writer][writer] · [Page decoder](parquet-rle-boolean-page.md)

The reader opens the immutable footer with `Snapshot.check`, matches
the chosen leaf and local chunk, and uses the checked page framer for
the original frame order and extents. The file, chunk, row and page
budgets bound the work. It checks both declared page sizes and the
sum of declared page slots before extracting any body. It then calls
`RleBooleanPage.decode` on each original body and checks the final row
count. Header-framing errors carry the group ordinal. Errors after
framing carry the group and page ordinals and the absolute header offset.

## Proof

`RleBoolean.readGroup_wire` witnesses the original snapshot, indexed
group, named leaf, matched chunk, and exact `Page.readChunk` result.
Its `List.Forall₂` relation gives one `PageWire` witness per frame in
frame order. That witness exposes the exact V1/V2 page decomposition,
the original definition mask, and an exact length-prefixed width-one
hybrid stream for the in-order present Boolean values. The returned
nullable slots concatenate those page lists and have exactly the
advertised group row count.
[Theorem header][thms] · [Existing scalar laws][page-thms]

## Pinned fixtures

Parquet Format is pinned at `04d56f291ff963e98bc37ab8100e2fc133ff583c`.
The encoding document SHA-256 is
`b6b980c67acc14d3e9e4b592c582523b5dc2cc09ad9f90bc2b1912df461e5c88`.
PyArrow **26.0.1** comes from Arrow commit
`9e5d6978e9acf372cc989aaaf94e863fe8582c90`, and the independent Compact
header reader uses Thrift **v0.25.0** at
`27e8a425ffb498e190df3a12e239326bf5ba9ed6`.
[Producer package pins][pins]

Each clean file has three groups of 16 slots and two pages per group.
They cover repeated true and false runs, packed mixed runs, and an
all-null final page. Thrift checks the exact tag, extent and level
fields of every page and the boundary of its Boolean run stream.
PyArrow and Lean verify the ordered slots. The all-null page has an
empty run stream with a four-byte zero length word.

| Fixture | SHA-256 |
| --- | --- |
| `boolean-rle-v1.parquet` | `1947ec77a0ec69a70e435963529cd5cf25397e36cb7b9db5763028d8681b9f4f` |
| `boolean-rle-v2.parquet` | `a2b291cff09d4267bf4c4d1cca766488daa84a474fd0c540e3f52f7db5ae913f` |
| `boolean-rle-v2-bad-length.parquet` | `9fe629ec924c94805e3e13a413f6f0e87bf6af4c0d821c1b48b1c61d316056c1` |

The damaged file changes the value length at byte 126 from two to
three. PyArrow rejects group 1 and reads groups 0 and 2. Lean rejects
the same group at page 1, header byte 100, with `lengthMismatch` and
reads groups 0 and 2 independently. Further controls exercise wrong
value tag, wrong codec, and a bad declared slot total that takes
precedence over a malformed first-page value length.
[Regressions][tests] · [Oracle][oracle]

```sh
fixture_tmp=$(mktemp -d)
python3 scripts/parquet-rle-boolean/Oracle.py "$fixture_tmp"
diff -r data/parquet-rle-boolean "$fixture_tmp"
lake build --wfail +Silmaril.Formats.Parquet.RleBoolean.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.RleBoolean.Tests +Silmaril.Formats.Parquet.RleBooleanPage.Examples parquet-footer-regression parquet-page-regression'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-rle-boolean/Axioms.lean
```

[spec]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#L149-L169
[writer]: https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/cpp/src/parquet/encoder.cc#L1739-L1759
[thms]: ../../Silmaril/Formats/Parquet/RleBoolean/Thms.lean
[page-thms]: ../../Silmaril/Formats/Parquet/RleBooleanPage/Thms.lean
[tests]: ../../Silmaril/Formats/Parquet/RleBoolean/Tests.lean
[oracle]: ../../scripts/parquet-rle-boolean/Oracle.py
[pins]: parquet-flat-page.md#independent-page-fixtures
