"""Pin converted-only INT64 footers over PyArrow pages and read native IPC."""

from hashlib import sha256
from importlib.metadata import version
import json
import os
from pathlib import Path
import platform
import runpy
import struct
import subprocess
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
EVENTS = runpy.run_path(str(ROOT / "tests/formats/parquet-timestamp-events/check-fixtures.py"))
THRIFT = EVENTS["THRIFT"]
MIN, MAX = -(2**63), 2**63 - 1
MICROS_GROUPS = [[MIN, -1001], [], [0, MAX]]
EOS = struct.pack("<II", 0xFFFFFFFF, 0)


def footer_start(wire):
    size, = struct.unpack_from("<I", wire, len(wire) - 8)
    return len(wire) - 8 - size


def schema_leaf(wire, ordinal):
    memory = TMemoryBuffer(wire[footer_start(wire):-8])
    footer = THRIFT["read_struct"](TCompactProtocol(memory))
    assert memory.cstringio_buf.tell() == len(wire) - 8 - footer_start(wire)
    return THRIFT["list_field"](footer, 2)[ordinal]


def annotate(wire, ordinal, code, modern):
    def edit(metadata):
        leaf = THRIFT["list_field"](metadata, 2)[ordinal]
        assert leaf[1] == (TType.I32, 2) and 10 in leaf
        leaf.pop(6, None)
        if code is not None:
            leaf[6] = TType.I32, code
        if modern == "absent":
            del leaf[10]
        elif modern == "wrong_union":
            leaf[10] = TType.STRUCT, {6: (TType.STRUCT, {})}

    updated = THRIFT["rewrite_footer"](wire, edit)
    assert updated[:footer_start(updated)] == wire[:footer_start(wire)]
    return updated


def fixtures():
    v1, expected = THRIFT["producer"]("1.0")
    v2 = EVENTS["frame_empty_group"](EVENTS["produce"](
        "micros", "us", True, False, MICROS_GROUPS))
    micros = annotate(v2, 1, 10, "absent")
    files = {
        "millis_v1": annotate(v1, 3, 9, "absent"),
        "micros_v2": micros,
        "modern_local": annotate(v1, 2, 9, "present"),
        "conflicting_dual": annotate(v1, 2, 10, "present"),
        "bad_modern": annotate(v2, 1, 10, "wrong_union"),
        "unrelated_code": annotate(v2, 1, 11, "absent"),
        "unannotated_int64": annotate(v2, 1, None, "absent"),
        "late_page": EVENTS["damage_last_page"](micros, pq.ParquetFile(pa.BufferReader(micros))),
    }
    assert schema_leaf(files["millis_v1"], 3)[6] == (TType.I32, 9)
    assert schema_leaf(micros, 1)[6] == (TType.I32, 10)
    assert 10 not in schema_leaf(files["millis_v1"], 3) and 10 not in schema_leaf(micros, 1)
    assert schema_leaf(files["modern_local"], 2)[10][1][8][1][1] == (TType.BOOL, False)
    check_frames(files["millis_v1"], 3, 0)
    check_frames(micros, 1, 3)

    def v1_gold(index):
        name, unit, adjusted, nullable, ticks = expected[index]
        return name, unit, adjusted, nullable, [ticks[:6], ticks[6:]]

    return files, {
        "millis_v1": (3, *v1_gold(1)),
        "micros_v2": (1, "micros", "us", True, False, MICROS_GROUPS),
        "modern_local": (2, *v1_gold(0)),
    }


def check_frames(wire, ordinal, page_type):
    parquet = pq.ParquetFile(pa.BufferReader(wire))
    for index in range(parquet.metadata.num_row_groups):
        group = parquet.metadata.row_group(index)
        column = group.column(ordinal - 1)
        assert column.compression == "UNCOMPRESSED" and column.total_compressed_size > 0
        start = column.data_page_offset
        size = column.total_compressed_size
        memory = TMemoryBuffer(wire[start:start + size])
        slots = 0
        while memory.cstringio_buf.tell() < size:
            header = THRIFT["read_struct"](TCompactProtocol(memory))
            assert header[1][1] == page_type and header[2][1] == header[3][1]
            data = header[5 if page_type == 0 else 8][1]
            assert data[2 if page_type == 0 else 4][1] == 0
            slots += data[1][1]
            memory.readAll(header[3][1])
        assert memory.cstringio_buf.tell() == size and slots == group.num_rows


def check_ipc(source, output, golden):
    ordinal, name, unit, adjusted, nullable, expected = golden
    parquet = pq.ParquetFile(pa.BufferReader(source))
    field = pa.field(name, pa.timestamp(unit, "UTC" if adjusted else None), nullable=nullable)
    assert parquet.schema.column(ordinal - 1).physical_type == "INT64"
    assert parquet.schema_arrow.field(ordinal - 1).equals(field)
    groups = [
        parquet.read_row_group(i, columns=[name], use_threads=False).column(0).cast(pa.int64()).to_pylist()
        for i in range(parquet.metadata.num_row_groups)
    ]
    assert groups == expected
    reader_source = pa.BufferReader(output)
    with pa.ipc.open_stream(reader_source) as stream:
        assert stream.schema.equals(pa.schema([field]), check_metadata=True)
        assert [batch.column(0).cast(pa.int64()).to_pylist() for batch in stream] == expected
    assert reader_source.tell() == len(output) and output.endswith(EOS)
    messages = list(pa.ipc.MessageReader.open_stream(output))
    assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(expected)
    assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in messages)
    print(f"{name}: {field.type}, batch sizes {list(map(len, expected))}, IPC SHA-256 {sha256(output).hexdigest()}")


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    files, admitted = fixtures()
    hashes = {name: sha256(wire).hexdigest() for name, wire in files.items()}
    assert hashes == json.loads((HERE / "fixtures.json").read_text()), hashes
    with tempfile.TemporaryDirectory(prefix="parquet-converted-timestamp-") as temporary:
        directory = Path(temporary)
        for name, wire in files.items():
            (directory / (name + ".parquet")).write_bytes(wire)
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(HERE / "Emit.lean"), str(directory)],
                       cwd=ROOT, check=True)
        assert {file.stem for file in directory.glob("*.arrows")} == set(admitted)
        for name, golden in admitted.items():
            check_ipc(files[name], (directory / (name + ".arrows")).read_bytes(), golden)


if __name__ == "__main__":
    main()
