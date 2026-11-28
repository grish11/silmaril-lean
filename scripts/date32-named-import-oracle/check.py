"""Generate independent Date32 fixtures and run the checked named imports."""

from hashlib import sha256
from pathlib import Path
import platform
from runpy import run_path
import subprocess
from tempfile import TemporaryDirectory

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.Thrift import TType
from thrift.transport.TTransport import TMemoryBuffer


ROOT = Path(__file__).resolve().parents[2]
DAYS = [-(2**31), -719528, -1, None, 0, 11016, 2**31 - 1]
PINS = {
    "paired.parquet": "8e1c92b870297e6eea1f94e736b3926daa056691805dd05acd34b4a024cd4c4d",
    "paired.arrows": "473c40ef4c5d8f9027f92015f3d6e682b202d0e696d8f6404ac4db0baa9f28c1",
    "late-group-error.parquet": "61b9814b5d8b27e85ecaf0a7830aadc0f33bfd308fea52e3697ae9bb0e7fb5b0",
    "late-batch-error.arrows": "a4e637587fe354b69855b1e11ced1bf616625c0131966fb60c451e54094b1ca2",
    "date64.arrows": "818f1130c70e112077fff3c35ee22a2a1e74da805b8864d968f5e88d0f47371b",
}


def ipc_stream(arrow_type, batches):
    schema = pa.schema([pa.field("date", arrow_type, nullable=True)])
    sink = pa.BufferOutputStream()
    with pa.ipc.new_stream(sink, schema) as writer:
        for batch in batches:
            writer.write_batch(pa.record_batch([batch], schema=schema))
    return schema, sink.getvalue().to_pybytes()


def fixtures():
    oracle = run_path(
        str(ROOT / "scripts/parquet-date-oracle/check.py"),
        init_globals={
            "pa": pa, "pq": pq, "TCompactProtocol": TCompactProtocol,
            "TMemoryBuffer": TMemoryBuffer, "TType": TType,
        },
    )
    parquet = oracle["producer"](DAYS, pa.date32(), True, group_size=4)
    corrupt, offset = oracle["damage_second_group"](parquet)
    source = pq.ParquetFile(pa.BufferReader(parquet))
    assert source.schema_arrow.field(0) == pa.field("date", pa.date32(), nullable=True)
    observed = [
        source.read_row_group(i).column(0).combine_chunks().view(pa.int32()).to_pylist()
        for i in range(source.num_row_groups)
    ]
    assert observed == [DAYS[:4], DAYS[4:]]

    parts = [DAYS[:4], [], DAYS[4:]]
    schema, ipc = ipc_stream(
        pa.date32(), [pa.array(values, type=pa.int32()).view(pa.date32()) for values in parts]
    )
    assert ipc.endswith(bytes.fromhex("ffffffff00000000"))
    with pa.ipc.open_stream(ipc) as stream:
        assert stream.schema == schema
        assert [batch.column(0).view(pa.int32()).to_pylist() for batch in stream] == parts

    truncated = ipc[:-9]
    with pa.ipc.open_stream(truncated) as stream:
        assert stream.read_next_batch().column(0).view(pa.int32()).to_pylist() == DAYS[:4]
        assert stream.read_next_batch().num_rows == 0
        try:
            stream.read_next_batch()
        except (pa.ArrowInvalid, OSError):
            pass
        else:
            raise AssertionError("PyArrow read a truncated third record")

    _, date64 = ipc_stream(pa.date64(), [pa.array([0], pa.int64()).view(pa.date64())])
    with pa.ipc.open_stream(date64) as stream:
        assert stream.schema.field(0).type == pa.date64()
        assert stream.read_next_batch().column(0).view(pa.int64()).to_pylist() == [0]
    print(f"PyArrow {pa.__version__}: Parquet groups [4, 3] and IPC batches [4, 0, 3] cover {DAYS}")
    print(f"PyArrow rejected Parquet group 1 (header byte {offset}) and truncated IPC batch 2")
    return {
        "paired.parquet": parquet,
        "paired.arrows": ipc,
        "late-group-error.parquet": corrupt,
        "late-batch-error.arrows": truncated,
        "date64.arrows": date64,
    }


def main():
    assert platform.python_implementation() == "CPython" and platform.python_version() == "3.13.5"
    assert pa.__version__ == "26.0.1"
    with TemporaryDirectory(prefix="silmaril-date32-") as temporary:
        paths = []
        for name, data in fixtures().items():
            digest = sha256(data).hexdigest()
            assert digest == PINS[name], f"{name} SHA-256 {digest}"
            print(f"{digest}  {name}", flush=True)
            path = Path(temporary) / name
            path.write_bytes(data)
            paths.append(str(path))
        subprocess.run(
            ["lake", "env", "lean", "-DautoImplicit=false", "-DwarningAsError=true", "--run",
             str(Path(__file__).with_name("Check.lean")), *paths],
            cwd=ROOT, check=True,
        )


if __name__ == "__main__":
    main()
