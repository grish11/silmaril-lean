"""Convert pinned modern Parquet TIMESTAMPs and read the native IPC with PyArrow."""

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

ROOT = Path(__file__).resolve().parents[2]
UPSTREAM_PATH = ROOT / "tests/formats/parquet-timestamp-events"
UPSTREAM = runpy.run_path(str(UPSTREAM_PATH / "check-fixtures.py"))
EOS = struct.pack("<II", 0xFFFFFFFF, 0)
V1_SHA256 = "2d66cce6a35ab9da7a073314a1c22de0191f68e269ce0993d6e41e83fa3934c8"
DAMAGED_TWICE = "318b78c863e09bd37c15f4ef36531e5138029d8b118be0673a26ef244889a1a4"


def damage_first_page(wire):
    # The existing pin has a corrupt last group. Change the original group
    # zero page header independently without moving any offsets.
    parquet = pq.ParquetFile(pa.BufferReader(wire))
    start = parquet.metadata.row_group(0).column(0).data_page_offset
    memory = TMemoryBuffer(wire[start:])
    thrift = UPSTREAM["THRIFT"]
    header = thrift["read_struct"](TCompactProtocol(memory))
    old_size = memory.cstringio_buf.tell()
    data = header[8][1]
    assert data[4] == (TType.I32, 0)
    data[4] = TType.I32, 5
    changed = thrift["encode"](header)
    assert len(changed) == old_size
    return wire[:start] + changed + wire[start + old_size:]


def verify_output(label, name, column, group_sizes, source, wire):
    parquet = pq.ParquetFile(pa.BufferReader(source))
    leaf = parquet.schema.column(column)
    logical = json.loads(leaf.logical_type.to_json())
    field = parquet.schema_arrow.field(column)
    unit, policy = name.split("_")
    assert field.name == name and leaf.physical_type == "INT64"
    assert logical["Type"] == "Timestamp" and logical["isAdjustedToUTC"] == (policy == "utc")
    assert field.type == pa.timestamp(unit, "UTC" if policy == "utc" else None)
    expected = [parquet.read_row_group(index, columns=[name], use_threads=False).column(0).cast(
        pa.int64()).to_pylist() for index in range(parquet.metadata.num_row_groups)]
    assert list(map(len, expected)) == group_sizes
    present = [tick for batch in expected for tick in batch if tick is not None]
    assert (min(present), max(present)) == (-(2**63), 2**63 - 1)
    assert wire.endswith(EOS)
    ipc_source = pa.BufferReader(wire)
    with pa.ipc.open_stream(ipc_source) as reader:
        assert reader.schema.equals(pa.schema([field]), check_metadata=True)
        observed = [batch.column(0).cast(pa.int64()).to_pylist() for batch in reader]
    assert observed == expected and ipc_source.tell() == len(wire)
    messages = list(pa.ipc.MessageReader.open_stream(wire))
    assert [message.type for message in messages] == ["schema"] + ["record batch"] * len(group_sizes)
    assert all(message.metadata_version == pa.ipc.MetadataVersion.V5 for message in messages)
    print(f"{label}: exact descriptor and signed nullable counts, batches {group_sizes}, "
          f"IPC SHA-256 {sha256(wire).hexdigest()}")


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1" and version("thrift") == "0.25.0"
    with tempfile.TemporaryDirectory(prefix="parquet-timestamp-to-ipc-") as temporary:
        directory = Path(temporary)
        files, _ = UPSTREAM["fixtures"](directory)
        pins = json.loads((UPSTREAM_PATH / "fixtures.json").read_text(encoding="utf-8"))
        assert {name: sha256(wire).hexdigest() for name, wire in files.items()} == pins
        two = damage_first_page(files["damaged"])
        digest = sha256(two).hexdigest()
        assert digest == DAMAGED_TWICE, f"unexpected double-corrupt SHA-256 {digest}"
        v1, expected_fields = UPSTREAM["THRIFT"]["producer"]("1.0")
        assert sha256(v1).hexdigest() == V1_SHA256
        assert expected_fields[3][0] == "us_utc"
        v1_file = pq.ParquetFile(pa.BufferReader(v1))
        for index in range(v1_file.metadata.num_row_groups):
            UPSTREAM["THRIFT"]["check_pages"](v1, v1_file.metadata.row_group(index).column(4), 0)
        print(f"V1 multi-column Parquet SHA-256 {V1_SHA256}")
        print(f"Double-corrupt Parquet SHA-256 {digest}", flush=True)
        for name, wire in {**files, "damaged_twice": two, "v1-selected": v1}.items():
            (directory / (name + ".parquet")).write_bytes(wire)
        emitter = ROOT / "scripts/parquet-timestamp-to-ipc-oracle/Emit.lean"
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", "--run", str(emitter), str(directory)], cwd=ROOT, check=True)
        admitted = {name for name in pins if name != "damaged"}
        assert {path.stem for path in directory.glob("*.arrows")} == admitted | {"v1-selected"}
        for name in sorted(admitted):
            verify_output(name, name, 0, [3, 0, 3], files[name], (directory / (name + ".arrows")).read_bytes())
        verify_output("V1 ordinal 5", "us_utc", 4, [6, 6], v1, (directory / "v1-selected.arrows").read_bytes())


if __name__ == "__main__":
    main()
