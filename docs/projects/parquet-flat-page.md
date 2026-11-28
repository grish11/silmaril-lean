# Flat Parquet data pages

`Silmaril.Formats.Parquet.FlatPage.Defs` checks the definition section of
a flat scalar data page and reconstructs its nullable slots in order.
`Silmaril.Formats.Parquet.FlatPage.Thms` states the wire and reconstruction
contracts. The level decoder uses the [Parquet hybrid codec](parquet-hybrid.md).

The wire references are Apache Parquet Format **2.14.0**, commit
`04d56f291ff963e98bc37ab8100e2fc133ff583c`. The raw `parquet.thrift`
SHA-256 is `d1d9a663d5543789b63d7168179d9849db06958b02c70ba96ba46ffde9278f61`.
[Data page layout][pages] · [Pinned page header IDL][idl] · [Hybrid encoding][rle]

## Inputs and count checks

The accepted schema has maximum repetition level zero. Maximum definition
level zero means a required scalar and level one means an optional scalar.
An absent optional value occupies one slot and consumes no scalar. A present
value consumes one scalar. The caller gives the slot count and the expected
number of present scalars. For flat V2, the caller can check that `num_rows`
equals `num_values` and derive the present count from `num_values - num_nulls`
after checking the subtraction. A V1 caller with only a slot count can use
`split` and `readMask` to obtain the present count before decoding the
scalar slice.

- **V1.** Supply the complete, already decompressed body. A required page
  starts directly with scalars. An optional page starts with an unsigned
  four-byte little-endian definition length. Exactly that many bytes go
  to the width-one Hybrid decoder. The entire remaining suffix goes to the
  scalar decoder. The caller checks that the V1 definition encoding is RLE.
- **V2.** Supply separately bounded definition and scalar slices, with the
  advertised repetition and definition byte lengths. Repetition length
  must be zero. The definition length must fit nonnegative signed i32,
  equal the supplied slice length, and fit the byte budget. The definition
  slice contains raw Hybrid bytes without a V1 length prefix. A required
  page must have an empty definition slice.
- Both layouts enforce the slot and definition-byte budgets, exact level
  consumption, and the declared present count. Width-one level 0 means
  absent and 1 means present. The Hybrid decoder governs final group
  padding and rejects remaining definition bytes. The scalar callback
  receives the exact scalar slice and the present count. It owns scalar
  byte consumption and value semantics. This layer rejects a returned list
  with too few or too many scalars.

The V1 body or V2 slices come from a caller that establishes their bounds
within a source and applies any decompression. The API leaves actual Thrift
headers, page indexing, compression, physical value encodings, dictionary
lookup, logical annotations, and nested repetition to their respective
layers.

## Proofs

- `splitV1Optional_ok_iff` proves the exact decomposition into the
  four-octet length word, its definition bytes, and the scalar suffix.
  `splitV2_ok_iff` proves that the supplied separate slices match the
  advertised lengths and bounds.
- `readMask_ok_iff` characterizes exact Hybrid or required-empty wire
  acceptance. `readMask_length` counts one slot per row and `plan_sound`
  connects the mask and present count to the scalar slice.
- `reconstruct_ok_iff` proves that a successful output projects back to the
  original mask and ordered scalar list. `reconstruct_exists_iff` gives the
  exact condition for successful reconstruction.
- `decode_ok_iff` connects the checks and callback to the exact reconstruction.
  `decode_counts` proves both the slot count and the present scalar count.
  `decode_exists_iff` characterizes the exact callback result count needed
  for a checked page to reconstruct.

## Independent page fixtures

The [fixture manifest][vectors] was generated from actual PyArrow **26.0.1**
Parquet files at the Arrow release commit
`9e5d6978e9acf372cc989aaaf94e863fe8582c90`. Each fixture is one uncompressed
PLAIN INT32 data page in a one-column, one-row-group file without a dictionary.
For each page version the fixtures use required `[7, -4, 19]`, optional
`[7, null, -4, null, 19]`, and optional `[null, null, null]`.
The oracle verifies PyArrow read-back and uses Apache Thrift **v0.25.0**
to locate the physical slices from the page headers. The extractor is
fixture tooling. The Lean tests bind the bytes to the manifest and pass
an exact INT32 test callback to the page decoder. They also check
truncated or trailing definition bytes, unsupported levels, wrong lengths,
present-count mismatch, and mismatched scalar output.
[PyArrow oracle][oracle] · [Lean fixtures][lean]

The TSV columns are page version, fixture name, slot count, present count,
declared definition length, definition section bytes, and scalar bytes.
V1 optional section bytes include their length word. A dash denotes an
empty section. The manifest SHA-256 is
`0c68f3b188c0c70beb898d9725a81243f8ce6ca09daa443fdaabe10a110660de`.

The fixture recipe was checked with CPython 3.13 on Linux x86-64 using the
following public artifacts. The Arrow and Thrift producer sources use
Apache-2.0. NumPy is a fixture dependency under its BSD license.

| Artifact | SHA-256 |
| --- | --- |
| [PyArrow 26.0.1 CPython 3.13 manylinux x86-64 wheel][arrow-wheel] | `f71221bbc7707e3fad920d0478db9350791d4714ec445299ee0d56559fbc156c` |
| [NumPy 2.4.3 CPython 3.13 manylinux x86-64 wheel][numpy-wheel] | `d5f51900414fc9204a0e0da158ba2ac52b75656e7dce7e77fb9f84bfa343b4cc` |
| [Apache Thrift v0.25.0 source archive][thrift] | `7a4bca6e3857fac4e247b697bfc42659583739c47e6afea8809cfde9f3fca80c` |

Extract the wheel contents into a Python module directory. From the Thrift
archive, extract `lib/py/src` and expose it as the `thrift` package on
`PYTHONPATH`, alongside the wheels. With those packages on the import path,
run the following from the repository root.

```sh
set -o pipefail
python3 scripts/parquet-flat-page/PyArrowOracle.py |
  diff -u tests/formats/parquet-flat-page/pyarrow-26.0.1.tsv -
lake build --wfail +Silmaril.Formats.Parquet.FlatPage.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.FlatPage.Examples
```

[pages]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/README.md#data-pages
[idl]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift
[rle]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#RLE
[arrow-wheel]: https://pypi.org/project/pyarrow/26.0.1/#files
[numpy-wheel]: https://pypi.org/project/numpy/2.4.3/#files
[thrift]: https://codeload.github.com/apache/thrift/tar.gz/27e8a425ffb498e190df3a12e239326bf5ba9ed6
[oracle]: ../../scripts/parquet-flat-page/PyArrowOracle.py
[vectors]: ../../tests/formats/parquet-flat-page/pyarrow-26.0.1.tsv
[lean]: ../../Silmaril/Formats/Parquet/FlatPage/Examples.lean
