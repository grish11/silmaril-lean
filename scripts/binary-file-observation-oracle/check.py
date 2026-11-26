"""Pin a selected second Parquet column and a matching independent BinaryView stream."""

import argparse
from hashlib import sha256
import json
import os
import platform
import subprocess
from pathlib import Path
from runpy import run_path
from struct import pack, unpack_from

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VALUES = [
    None, b"", b"\xff\x00", b"123456789012",
    b"1234567890123", None, b"\x00", b"long\x00opaque\xfevalue",
]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    out = parser.parse_args().out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1"
    schema = pa.schema([pa.field("row_id", pa.int32(), nullable=False), pa.field("blob", pa.binary())])
    table = pa.Table.from_arrays([pa.array(range(8), pa.int32()), pa.array(VALUES, pa.binary())], schema=schema)
    sink = pa.BufferOutputStream()
    pq.write_table(table, sink, version="2.6", data_page_version="2.0", compression="NONE",
                   use_dictionary=False, column_encoding="PLAIN", write_statistics=False,
                   write_page_checksum=False, row_group_size=4, store_schema=False)
    file_bytes = sink.getvalue().to_pybytes()
    source = pq.ParquetFile(pa.BufferReader(file_bytes))
    assert source.schema_arrow == schema
    assert [
        source.read_row_group(i, columns=["blob"]).column(0).to_pylist()
        for i in range(source.num_row_groups)
    ] == [VALUES[:4], VALUES[4:]]
    leaf = source.schema.column(1)
    assert (leaf.name, leaf.physical_type, leaf.max_definition_level, leaf.max_repetition_level) == (
        "blob", "BYTE_ARRAY", 1, 0
    )

    header_fields = run_path(str(ROOT / "scripts/parquet-scalar-page/PyArrowOracle.py"))["header_fields"]
    for index in range(source.num_row_groups):
        chunk = source.metadata.row_group(index).column(1)
        assert chunk.path_in_schema == "blob" and chunk.compression == "UNCOMPRESSED"
        assert not chunk.has_dictionary_page
        header_offset = chunk.data_page_offset
        transport = TMemoryBuffer(file_bytes[header_offset : header_offset + chunk.total_compressed_size])
        header = header_fields(TCompactProtocol(transport), (8,))
        header_length = transport.cstringio_buf.tell()
        assert header[1] == 3 and 4 not in header and header[2] == header[3]
        assert header_length + header[3] == chunk.total_compressed_size
        assert header[8][4] == 0 and header[8][6] == 0 and header[8][1] == 4
    late_header = header_offset
    late_length = late_header + header_length + header[8][5]
    assert unpack_from("<I", file_bytes, late_length)[0] == len(VALUES[4])
    damaged = file_bytes[:late_length] + pack("<I", 2**31) + file_bytes[late_length + 4:]
    with pq.ParquetFile(pa.BufferReader(damaged)) as bad:
        assert bad.read_row_group(0, columns=["blob"]).column(0).to_pylist() == VALUES[:4]
        try:
            bad.read_row_group(1, columns=["blob"])
        except (OSError, pa.ArrowInvalid):
            pass
        else:
            raise AssertionError("PyArrow admitted a negative second-group BYTE_ARRAY length")

    arrow_schema = pa.schema([pa.field("blob", pa.binary_view())])
    parts = [VALUES[:2], [], VALUES[2:]]
    sink = pa.BufferOutputStream()
    options = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5, compression=None)
    with pa.ipc.new_stream(sink, arrow_schema, options=options) as writer:
        for batch in parts:
            writer.write_batch(pa.record_batch([pa.array(batch, type=pa.binary_view())], schema=arrow_schema))
    arrow = sink.getvalue().to_pybytes()
    with pa.ipc.open_stream(arrow) as reader:
        assert reader.schema == arrow_schema
        assert [batch.column(0).to_pylist() for batch in reader] == parts

    entries = dict(zip(("selected.parquet", "late-length-error.parquet", "reference.arrows"),
                       (file_bytes, damaged, arrow), strict=True))
    pins = {name: sha256(wire).hexdigest() for name, wire in entries.items()}
    manifest = HERE / "sha256.json"
    assert json.loads(manifest.read_text(encoding="utf-8")) == pins, pins
    for name, wire in entries.items():
        (out / name).write_bytes(wire)
        print(f"{pins[name]}  {name}")
    print(f"PyArrow 26.0.1: Parquet selected column 1, groups [4, 4], IPC batches [2, 0, 6]")
    print(f"Thrift: PLAIN tag 0, Data Page V2, codec 0, no CRC. Late header {late_header}, length word {late_length}")
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Check.lean"),
         *[str(out / name) for name in entries]],
        cwd=ROOT, check=True,
    )


if __name__ == "__main__":
    main()
