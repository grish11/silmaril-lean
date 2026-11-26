# Hive partition directory paths

Import
[`Silmaril.Formats.Hive.PartitionPath.Defs`](../../Silmaril/Formats/Hive/PartitionPath/Defs.lean)
for the executable API. It consumes a relative directory string and returns an
ordered list of decoded keys with text or null values. Pass the directory
relative to the dataset root before calling the parser. The caller handles
discovery, filenames, filesystem semantics and typed partition schemas.
Table materialization and partition pruning are future integrations.
[Coverage matrix](arrow-parquet-coverage.md)

## Directory profile

| Behavior | Policy |
| --- | --- |
| Directory and assignment delimiters | Split at literal `/` before decoding. Split each segment at its first literal `=`. The empty path means the dataset root. Reject empty segments, leading and trailing slashes, missing `=` and empty decoded keys. A later literal `=` belongs to the value. |
| Percent decoding | Decode one layer of `%HH` in both keys and values. Accept either hex case and validate the resulting UTF-8. A plus sign stays a plus sign. Invalid escapes and invalid UTF-8 have distinct errors. |
| Canonical rendering | Emit URI-unreserved ASCII inside components and uppercase percent escapes for every other UTF-8 byte. Insert literal separators only between decoded components or entries. Preserve supplied order and key case. This is a lexical path policy. The caller controls whether and how to open a path. |
| Nulls and collisions | Compare the decoded value with `Options.nullMarker`, which defaults to `__HIVE_DEFAULT_PARTITION__`. Any escaped spelling of that value also means null. Reject empty markers in both directions. Render null as the encoded marker and reject a literal value equal to the marker. Preserve empty text as `key=`. |
| Keys and errors | Compare decoded keys case-sensitively and reject all duplicates, including repeated identical assignments. Keep additional keys. Missing keys are allowed unless listed in `Options.requiredKeys`. Present null satisfies a required key. Parsing checks the segment syntax before the key policy. Rendering checks the key policy before value collisions. |

The rendering alphabet follows [RFC 3986 §2.1 and §2.3](https://www.rfc-editor.org/rfc/rfc3986).
PyArrow's partition API takes a path whose final component can be a filename.
The fixture adapter appends a slash to tell PyArrow to parse every component as
a directory. PyArrow may ignore nonpartition directories and unrecognized
schema fields or leave some malformed escapes literal. Hive's
`FileUtils.makePartName` lowercases keys, leaves some characters unescaped and
maps empty text to its default marker on write. The fixture suite records these
producer differences within the admitted profile.
[Arrow 26.0.1 path implementation](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/cpp/src/arrow/dataset/partition.cc#L689-L765) ·
[Hive 4.1.0 path implementation](https://github.com/apache/hive/blob/75e40b7537c91a70ccaa31c397d21823c7528eeb/common/src/java/org/apache/hadoop/hive/common/FileUtils.java)

## Proofs

[`PartitionPath.Thms`](../../Silmaril/Formats/Hive/PartitionPath/Thms.lean)
exports `Percent.unescape_escape` for byte round-trip, `Percent.escape_safe`
for ASCII and delimiter exclusion, and `Percent.decode_encode` for UTF-8
component round-trip. For a successful path parse, `parse_lookup` establishes
uniqueness and presence for every required key, and `lookup_eq_some_iff`
identifies lookup with exact entry membership under uniqueness. Lookup's outer
option distinguishes an absent key from a present null. The test suite
exercises complete path rendering and parsing on the fixture inputs. The
round-trip theorems quantify over components.

## Reproduce checks

Run from the repository root with the pinned Lean toolchain.

```sh
lake build --wfail +Silmaril.Formats.Hive.PartitionPath.Checks
make check CHECK_TARGETS=+Silmaril.Formats.Hive.PartitionPath.Checks
lake env lean -DautoImplicit=false -DwarningAsError=true --run tests/formats/hive-partition/Regression.lean
```

`Checks` runs closed policy regressions and prints the public theorems' axiom
dependencies. The standalone Lean regression reads
[`fixtures.json`](../../tests/formats/hive-partition/fixtures.json)
(SHA-256 `59333475020684ae6d7cab9321cf089ad0f72394d6353ca88e688c3de3f1d5ae`).
It parses the PyArrow and Hive paths and tests rendering and reparsing the
PyArrow entries.

For the independent checks, install PyArrow 26.0.1 and use Java 21 with the
three Maven artifacts below in one directory. The oracle checks the PyArrow
version and JAR hashes. The fixed Linux x86-64 CPython 3.13 wheel SHA-256 is
`f71221bbc7707e3fad920d0478db9350791d4714ec445299ee0d56559fbc156c`.
[PyArrow release and wheels](https://pypi.org/project/pyarrow/26.0.1/#files)

| Java artifact | SHA-256 |
| --- | --- |
| [hive-common-4.1.0.jar](https://repo.maven.apache.org/maven2/org/apache/hive/hive-common/4.1.0/hive-common-4.1.0.jar) | `8e62f91679455f2dcb4810ea4d29910968bfbf819dc64e1900afd0322b0f18f5` |
| [hadoop-client-api-3.4.1.jar](https://repo.maven.apache.org/maven2/org/apache/hadoop/hadoop-client-api/3.4.1/hadoop-client-api-3.4.1.jar) | `a964d4daa054c9615bbafb4553efbb140fa7fb9ac6f358a24393f183a5703438` |
| [slf4j-api-1.7.36.jar](https://repo.maven.apache.org/maven2/org/slf4j/slf4j-api/1.7.36/slf4j-api-1.7.36.jar) | `d3ef575e3e4979678dc01bf1dcce51021493b4d11fb7f1be8ad982877c16a1c0` |

```sh
python3 tests/formats/hive-partition/oracles.py --hive-jars /path/to/jars
```

This runs PyArrow parse and selected format cases, and the Hive release's
`FileUtils.makePartName` against the same fixture manifest. These oracles are
standalone checks and require no changes to the root build configuration.
