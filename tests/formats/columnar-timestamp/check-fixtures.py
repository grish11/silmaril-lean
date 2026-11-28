"""Compare Lean's logical timestamp adapters with pinned PyArrow IPC and Parquet fixtures."""

import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

import pyarrow as pa
import pyarrow.ipc as ipc
import pyarrow.parquet as pq


ARROW_UNITS = {"s": "second", "ms": "millisecond", "us": "microsecond", "ns": "nanosecond"}
PARQUET_UNITS = {"milliseconds": "millis", "microseconds": "micros", "nanoseconds": "nanos"}
FIXTURE_DIGEST = "0b84200b5a04f8abe4391b74d892eeb478e0a2a98c2e5bb7674172f30d160395"


def lean_zone(zone):
    return "none" if zone is None else f"some {json.dumps(zone)}"


def main():
    assert pa.__version__ == "26.0.1", pa.__version__
    digest = hashlib.sha256()
    checks = [
        "module",
        "import Silmaril.Formats.ColumnarTimestamp.Defs",
        "meta import Silmaril.Formats.ColumnarTimestamp.Defs",
        "meta import Silmaril.Numeric.Timestamp.Defs",
        "open Silmaril.Formats.ColumnarTimestamp",
    ]
    ipc_options = ipc.IpcWriteOptions(metadata_version=ipc.MetadataVersion.V5)
    for unit in ARROW_UNITS:
        for zone in (None, "Europe/Paris"):
            ticks = [-2, 0, 4] if unit == "s" else [-(2**63), -2, 0, 4, 2**63 - 1]
            table = pa.table({"time": pa.array(ticks, type=pa.int64()).cast(pa.timestamp(unit, zone))})
            stream = pa.BufferOutputStream()
            with ipc.new_stream(stream, table.schema, options=ipc_options) as writer:
                writer.write_table(table)
            arrow_bytes = stream.getvalue()
            arrow = ipc.open_stream(arrow_bytes).read_all().column(0)
            assert (arrow.type.unit, arrow.type.tz, arrow.cast(pa.int64()).to_pylist()) == (unit, zone, ticks)

            output = pa.BufferOutputStream()
            pq.write_table(table, output, version="2.6", compression="NONE", use_dictionary=False,
                           store_schema=False, write_statistics=False)
            parquet_bytes = output.getvalue()
            parquet = pq.ParquetFile(pa.BufferReader(parquet_bytes))
            column = parquet.schema.column(0)
            logical = json.loads(column.logical_type.to_json())
            assert (column.physical_type, logical["Type"]) == ("INT64", "Timestamp")
            parquet_unit = PARQUET_UNITS[logical["timeUnit"]]
            adjusted = str(logical["isAdjustedToUTC"]).lower()
            values = parquet.read().column(0)
            counts = values.cast(pa.int64()).to_pylist()
            back = values.cast(pa.timestamp(unit, values.type.tz)).cast(pa.int64()).to_pylist()

            for data in (arrow_bytes, parquet_bytes):
                digest.update(len(data).to_bytes(8, "little"))
                digest.update(data)

            arrow_unit = ARROW_UNITS[arrow.type.unit]
            metadata = f"(⟨.{arrow_unit}, {lean_zone(arrow.type.tz)}⟩ : Arrow.Metadata)"
            parquet_meta = f"(⟨.{parquet_unit}, {adjusted}⟩ : Parquet.Metadata)"
            checks.extend([
                f"#guard ({metadata}.parquet .{parquet_unit}).isAdjustedToUTC == {adjusted}",
                f"#guard ({parquet_meta}.arrow .{arrow_unit}).timezoneAnnotation = {lean_zone(values.type.tz)}",
            ])
            for original, converted, recovered in zip(ticks, counts, back, strict=True):
                checks.extend([
                    f"#guard ({metadata}.toParquet .{parquet_unit} ({original})).toOption = some ({converted})",
                    f"#guard ({parquet_meta}.toArrow .{arrow_unit} ({converted})).toOption = some ({recovered})",
                ])

    assert digest.hexdigest() == FIXTURE_DIGEST, f"fixture bytes SHA-256 {digest.hexdigest()}"
    root = Path(__file__).resolve().parents[3]
    with tempfile.TemporaryDirectory() as tmp:
        lean = Path(tmp) / "Fixture.lean"
        lean.write_text("\n".join(checks) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(lean)], cwd=root, check=True)
    print(f"PyArrow {pa.__version__}: {len(checks) - 5} Lean checks on eight IPC/Parquet fixture pairs")
    print(f"Fixture bytes SHA-256 {FIXTURE_DIGEST}")


if __name__ == "__main__":
    main()
