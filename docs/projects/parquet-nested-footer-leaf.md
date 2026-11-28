# Parquet nested footer leaf positions

`Footer.NestedLeaf.select limits snapshot column` resolves a physical
leaf in a checked snapshot. This profile admits a root with one optional,
unannotated struct containing exactly two direct physical leaves. Either
leaf can be required or optional. Physical ordinals 0 and 1 correspond
to original schema ordinals 2 and 3. The returned path consists of the
struct name and leaf name, in that order. The root name is omitted.
[Public API](../../Silmaril/Formats/Parquet/Footer/NestedLeaf/Defs.lean) · [Pinned depth-first schema](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L518-L554) · [Pinned column path and group order](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L905-L917)

The existing footer validator internally checks the depth-first leaf
paths and types against every row group's column list. This accessor
exposes the positions for the admitted shape. It reuses the checked
Snapshot and the bounded Compact struct-list reader. It retains the
original schema container and both selected struct spans through their
own STOP octets. The proof witnesses the complete serialized list and
its exact end, as well as the matching typed leaf in the same snapshot.

`selectChunk selection group` resolves the original physical column in
the selected row group and checks its full path and physical type. The
selection is indexed by its snapshot. The accessor returns metadata and
performs no page parsing or value decoding. It refuses other shapes,
including flat roots, required or repeated parent groups, repeated
leaves, and converted or logical annotations on the parent. The cap
and ordinal failures are typed. Leaf logical annotations remain opaque.
The existing flat selector and scanner entry points keep their contracts.
[Proof header](../../Silmaril/Formats/Parquet/Footer/NestedLeaf/Thms.lean)

## Independent fixtures

PyArrow 26.0.1 wrote the optional struct `point` containing required
INT32 `signed` and optional INT64 `wide`, including a null struct and a
present struct with a null leaf. The required-parent negative comes from
the same producer. Apache Thrift 0.25.0 independently reads the exact
footer, physical chunk paths, original schema ordinals, and item spans.
A byte mutation adds a legacy LIST annotation to the parent while
retaining the same represented schema. Lean checks that refusal along
with the required parent, flat input, wrong ordinals, and footer cap.
[Producer pins](parquet-column-index.md#pinned-independent-fixture) · [Fixture hashes and wire observations](../../scripts/parquet-nested-footer/observations.txt) · [Lean controls](../../Silmaril/Formats/Parquet/Footer/NestedLeaf/Examples.lean)

```sh
set -o pipefail
replay=$(mktemp -d)
python3 scripts/parquet-nested-footer/Oracle.py "$replay/optional-point.parquet" |
  diff -u scripts/parquet-nested-footer/observations.txt -
cmp data/parquet-nested-footer/optional-point.parquet "$replay/optional-point.parquet"
cmp data/parquet-nested-footer/required-parent.parquet "$replay/required-parent.parquet"
lake build --wfail +Silmaril.Formats.Parquet.Footer.NestedLeaf.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.Footer.NestedLeaf.Examples
```
