# Checked Parquet dictionary indices

`Silmaril.Formats.Parquet.DictionaryIndex.Defs` decodes flat dictionary data
pages over a typed, zero-based dictionary `Array α` in file entry order.
`Silmaril.Formats.Parquet.DictionaryIndex.Thms` gives the exact index stream
and ordered nullable-slot contracts.

The wire rules are pinned to Apache Parquet Format **2.14.0**, commit
`04d56f291ff963e98bc37ab8100e2fc133ff583c`. The raw `Encodings.md` SHA-256 is
`b6b980c67acc14d3e9e4b592c582523b5dc2cc09ad9f90bc2b1912df461e5c88`.
[Dictionary encoding][dictionary] · [Hybrid encoding][hybrid] · [Data page headers][idl]

## Page callback

Call `DictionaryIndex.decode dictionary params pageLimits indexLimits body`.
Use the same `ScalarPage.Parameters`, page caps, and exact full on-disk body
as the [PLAIN callback][scalar]. The caller establishes the physical type
and supplies the dictionary for this column chunk, with entries preserved
in the order read from its dictionary page. Its size and typed parsing are
caller concerns. For example, a checked decompressed INT32 dictionary body
and declared entry count can go through `Plain.decodeInt32`; convert the
result to an array. The new callback returns `Except Error (List (Option α))`.

Dispatch data-page encoding `8` (`RLE_DICTIONARY`) or `2` (deprecated
`PLAIN_DICTIONARY`) here. Both use the width-prefixed index stream when a
matching typed dictionary is available. An actual PLAIN data page uses
`ScalarPage.decode`. The page wrappers share `ScalarPage.prepareFor` and
check the original encoding ID, exact payload extents, compression and
flat level sections. V1 derives the index count from the checked mask. V2
also validates the header-derived present count. The profile admits required
and optional scalar columns, with maximum repetition level zero and maximum
definition level zero or one. The [header mapping][scalar] works with an
explicit checked frame and has no dependency on the framing implementation.

## Index stream

- `readIndices indexLimits expected source` takes exactly the decompressed
  value suffix. Its first byte declares a width in `0..32`. The remaining
  bytes are one complete Hybrid stream without a length prefix. The
  byte cap includes the width octet, and the value cap applies to decoded
  indices. The width octet is required even when `expected = 0`, in which
  case the run suffix must be empty.
- The [Hybrid profile][hybrid-profile] rejects noncanonical run headers,
  count errors, truncation, and trailing bytes. It allows up to seven
  unused values at the end of the final bit-packed run; those values are
  padding and are never looked up in the dictionary. A width-zero run
  represents index zero. Dictionary capacity does not determine the
  width byte, so a page can use a narrower stream when its indices fit.
- `select dictionary indices` checks each decoded index against `dictionary.size`
  and preserves the order and duplicates. Null slots consume no indices.
  An empty dictionary can serve an all-null page with an empty index list.

Dictionary-page parsing and decompression, selecting a dictionary for a
column chunk, frame traversal, CRC, logical annotations, and row-group
assembly stay at their caller seams.

## Public proofs

- `readIndices_ok_iff` characterizes the width octet and exact Hybrid suffix,
  including the width and byte/value limits.
- `select_ok_iff` gives one successful lookup per index in the original
  order. `select_indices_lt` gives the dictionary bound at each used index.
- `decode_ok_iff` characterizes successful page reconstruction by the
  checked mask and the ordered dictionary lookup results. `decode_counts`
  proves the slot count and, for V2, the header-derived present count.
- `ScalarPage.prepareFor_sound` and `ScalarPage.preparedFor_counts` expose
  the shared payload and level contracts to other physical decoders.

## Independent writer fixtures

The [manifest][vectors] records six uncompressed dictionary and data page
pairs from PyArrow **26.0.1**. Each consists of one PLAIN INT32 dictionary
page and one RLE_DICTIONARY data page. The Arrow release commit is
`9e5d6978e9acf372cc989aaaf94e863fe8582c90`. The [oracle][oracle] verifies
PyArrow read-back and dictionary order, checks the offsets and extents from
Apache Thrift **v0.25.0** headers, and records the actual on-disk bodies.
For both V1 and V2, the manifest includes mixed slots with bit-packed indices,
repeated indices encoded as RLE, and all-null slots with an empty dictionary.
The [Lean examples][examples] also cover the deprecated tag with a typed
dictionary, width zero and 32, out-of-range indices, malformed or extra
index bytes, invalid counts, and limit errors.

The TSV records version, case, slot count, null count, raw definition bytes
as a count, data encoding ID, dictionary entry count, dictionary body,
data body, and index suffix. The three bodies or suffixes are in hex and
`-` marks an empty slice. Its SHA-256 is
`eeced0459738c485c29e81141103f84506b58dbbdd9b0a1bfde40bde762a616f`.

Use the public Python and Thrift pins from the [flat-page fixture
recipe][flat]. With those packages on the import path, run from the repo root.

```sh
set -o pipefail
python3 scripts/parquet-dictionary-index/PyArrowOracle.py |
  diff -u tests/formats/parquet-dictionary-index/pyarrow-26.0.1.tsv -
lake build --wfail +Silmaril.Formats.Parquet.DictionaryIndex.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.DictionaryIndex.Examples
```

[dictionary]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#dictionary-encoding-plain_dictionary--2-and-rle_dictionary--8
[hybrid]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#RLE
[idl]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift
[scalar]: parquet-scalar-page.md#header-and-body-adapter
[hybrid-profile]: parquet-hybrid.md
[flat]: parquet-flat-page.md#independent-page-fixtures
[vectors]: ../../tests/formats/parquet-dictionary-index/pyarrow-26.0.1.tsv
[oracle]: ../../scripts/parquet-dictionary-index/PyArrowOracle.py
[examples]: ../../Silmaril/Formats/Parquet/DictionaryIndex/Examples.lean
