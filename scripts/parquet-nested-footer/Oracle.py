"""Verify original nested leaf positions with a PyArrow producer and Thrift."""

from hashlib import sha256
from io import BytesIO
from pathlib import Path
import runpy
import struct
import sys

oracle = runpy.run_path(
    str(Path(__file__).resolve().parents[1] / "parquet-column-index" / "Oracle.py"))
column_order = runpy.run_path(
    str(Path(__file__).resolve().parents[1] / "parquet-footer-column-order" / "Oracle.py"))
pa, pq = oracle["pa"], oracle["pq"]
parse, items, record = oracle["parse"], oracle["items"], oracle["record"]
i32, binary = oracle["I32"], oracle["BINARY"]
schema = {1: i32, 3: i32, 4: binary, 5: i32, 6: i32, 10: record({})}
column = record({3: record({1: i32, 3: items(binary)})})
footer_schema = {2: items(record(schema)), 4: items(record({1: items(column)}))}


def check(source, expected_schema, expected_columns):
    footer_size = struct.unpack("<I", source[-8:-4])[0]
    start = len(source) - 8 - footer_size
    footer = source[start:-8]
    decoded, consumed = parse(footer, footer_schema)
    assert consumed == footer_size
    observed_schema = [(node[4].decode(), node.get(1), node.get(3), node.get(5))
                       for node in decoded[2]]
    assert observed_schema == expected_schema
    [group] = decoded[4]
    observed_columns = [(tuple(part.decode() for part in chunk[3][3]), chunk[3][1])
                        for chunk in group[1]]
    assert observed_columns == expected_columns
    for ordinal, chunk in enumerate(pq.ParquetFile(BytesIO(source)).schema):
        assert chunk.path == ".".join(expected_columns[ordinal][0])
    schema_span = column_order["item_extents"](footer)[0]
    print(f"SHA-256 {sha256(source).hexdigest()} footer [{start}, {start + footer_size})")
    print(f"schema {observed_schema}, physical columns {observed_columns}, schema extent {schema_span}")
    return start, footer, schema_span


def write(path):
    signed = pa.field("signed", pa.int32(), nullable=False)
    wide = pa.field("wide", pa.int64())
    parent = pa.struct([signed, wide])
    rows = [{"signed": -7, "wide": 1 << 42}, None, {"signed": 0, "wide": None}]
    table = pa.table({"point": pa.array(rows, type=parent)})
    pq.write_table(table, path, compression="NONE", use_dictionary=False,
                   data_page_version="1.0", write_statistics=True, write_page_index=True)
    source = path.read_bytes()
    assert pq.ParquetFile(BytesIO(source)).read(use_threads=False).to_pydict() == table.to_pydict()
    expected = [("schema", None, 0, 1), ("point", None, 1, 2),
                ("signed", 1, 0, None), ("wide", 2, 1, None)]
    columns = [(("point", "signed"), 1), (("point", "wide"), 2)]
    print(f"PyArrow {pa.__version__} optional struct")
    start, footer, schema_span = check(source, expected, columns)

    # The parent's last byte is its STOP. Insert a legacy LIST annotation
    # with the same physical shape, so the dedicated accessor must refuse it.
    parent_stop = schema_span[3][1][1]
    assert footer[parent_stop - 1] == 0
    altered = footer[:parent_stop - 1] + bytes.fromhex("15 06") + footer[parent_stop - 1:]
    decoded, consumed = parse(altered, footer_schema)
    assert consumed == len(altered) and decoded[2][1][6] == 3
    assert all(6 not in item and 10 not in item for item in decoded[2][2:])
    modified = source[:start] + altered + struct.pack("<I", len(altered)) + b"PAR1"
    print(f"annotated parent: {sha256(modified).hexdigest()}, insertion at file byte {start + parent_stop - 1}")

    required = pa.Table.from_arrays([pa.array([rows[0], rows[2]], type=parent)],
                                    schema=pa.schema([pa.field("point", parent, nullable=False)]))
    sink = BytesIO()
    pq.write_table(required, sink, compression="NONE", use_dictionary=False,
                   data_page_version="1.0", write_statistics=True, write_page_index=True)
    expected[1] = ("point", None, 0, 2)
    print("required parent control")
    check(sink.getvalue(), expected, columns)
    path.with_name("required-parent.parquet").write_bytes(sink.getvalue())


if __name__ == "__main__":
    write(Path(sys.argv[1]))
