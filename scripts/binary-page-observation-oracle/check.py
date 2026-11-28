"""Produce paired BinaryView IPC and flat Parquet BYTE_ARRAY pages with PyArrow."""

from hashlib import sha256
import json
from pathlib import Path
import platform
import os
from runpy import run_path
import subprocess
from tempfile import TemporaryDirectory

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
VALUES = [
    None, b"", b"\xff\x00", b"123456789012", b"1234567890123", None, b"\x00", b"long\x00opaque\xfevalue",
]
FIELD = "blob"


def produce():
    schema = pa.schema([pa.field(FIELD, pa.binary(), nullable=True)])
    sink = pa.BufferOutputStream()
    pq.write_table(
        pa.Table.from_arrays([pa.array(VALUES, type=pa.binary())], schema=schema),
        sink,
        version="2.6",
        data_page_version="2.0",
        compression="NONE",
        use_dictionary=False,
        column_encoding="PLAIN",
        write_statistics=False,
        write_page_checksum=False,
        row_group_size=4,
        store_schema=False,
    )
    parquet = sink.getvalue().to_pybytes()
    parsed = pq.ParquetFile(pa.BufferReader(parquet))
    leaf = parsed.schema.column(0)
    assert (leaf.name, leaf.physical_type, leaf.max_definition_level, leaf.max_repetition_level) == (
        FIELD, "BYTE_ARRAY", 1, 0,
    )
    assert parsed.schema_arrow == schema
    assert [parsed.read_row_group(i).column(0).to_pylist() for i in range(parsed.num_row_groups)] == [
        VALUES[:4], VALUES[4:],
    ]

    header_fields = run_path(str(ROOT / "scripts/parquet-scalar-page/PyArrowOracle.py"))["header_fields"]
    pages = []
    for index in range(parsed.num_row_groups):
        chunk = parsed.metadata.row_group(index).column(0)
        assert chunk.compression == "UNCOMPRESSED" and not chunk.has_dictionary_page
        start = chunk.data_page_offset
        transport = TMemoryBuffer(parquet[start : start + chunk.total_compressed_size])
        header = header_fields(TCompactProtocol(transport), (8,))
        header_size = transport.cstringio_buf.tell()
        body = transport.readAll(header[3])
        assert header[1] == 3 and 4 not in header and header[2] == header[3]
        assert header_size + len(body) == chunk.total_compressed_size
        detail = header[8]
        assert detail[4] == 0 and detail[6] == 0
        pages.append((start, parquet[start : start + header_size], body, detail))

    parts = [VALUES[:2], [], VALUES[2:]]
    schema = pa.schema([pa.field(FIELD, pa.binary_view(), nullable=True)])
    sink = pa.BufferOutputStream()
    options = pa.ipc.IpcWriteOptions(metadata_version=pa.ipc.MetadataVersion.V5, compression=None)
    with pa.ipc.new_stream(sink, schema, options=options) as writer:
        for part in parts:
            batch = pa.array(part, type=pa.binary_view())
            writer.write_batch(pa.record_batch([batch], schema=schema))
    ipc = sink.getvalue().to_pybytes()
    assert ipc.endswith(bytes.fromhex("ffffffff00000000"))
    with pa.ipc.open_stream(ipc) as reader:
        assert reader.schema == schema
        assert [batch.column(0).to_pylist() for batch in reader] == parts
    truncated = ipc[:-9]
    with pa.ipc.open_stream(truncated) as reader:
        assert reader.read_next_batch().column(0).to_pylist() == VALUES[:2]
        assert reader.read_next_batch().num_rows == 0
        try:
            reader.read_next_batch()
        except (pa.ArrowInvalid, OSError):
            pass
        else:
            raise AssertionError("PyArrow admitted a truncated IPC body")
    return parquet, pages, ipc, truncated



def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1"
    parquet, pages, ipc, truncated = produce()
    fixtures = {
        "paired.parquet": parquet,
        "paired.arrows": ipc,
        "truncated-batch.arrows": truncated,
        "group-0-header.bin": pages[0][1],
        "group-0-page.bin": pages[0][2],
        "group-1-header.bin": pages[1][1],
        "group-1-page.bin": pages[1][2],
        "truncated-group-1-page.bin": pages[1][2][:-1],
    }
    manifest = {name: sha256(data).hexdigest() for name, data in fixtures.items()}
    assert json.loads((HERE / "sha256.json").read_text(encoding="utf-8")) == manifest, manifest
    for name, digest in manifest.items():
        print(f"{digest}  {name}")
    print(f"PyArrow {pa.__version__}: Parquet groups [4, 4] and IPC batches [2, 0, 6] cover {VALUES!r}")
    for index, (start, header, body, detail) in enumerate(pages):
        print(f"Parquet group {index}: page offset {start}, header {len(header)}, body {len(body)}, V2 {detail}")

    with TemporaryDirectory(prefix="silmaril-binary-observation-") as temporary:
        directory = Path(temporary)
        paths = []
        for name, data in fixtures.items():
            if name != "paired.parquet":
                path = directory / name
                path.write_bytes(data)
                paths.append(str(path))
        subprocess.run(
            [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
             "-DwarningAsError=true", "--run", str(HERE / "Check.lean"), *paths],
            cwd=ROOT, check=True,
        )


if __name__ == "__main__":
    main()
