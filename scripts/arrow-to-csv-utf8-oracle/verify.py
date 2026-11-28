"""Read the pinned Arrow fixture in PyArrow and compare canonical CPython CSV bytes."""
import argparse
import csv
import hashlib
import io
import json
from pathlib import Path

import numpy as np
import pyarrow as pa


ROOT = Path(__file__).resolve().parents[2]
FIXTURES = ROOT / "tests" / "formats" / "arrow-ipc"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="Silmaril-produced UTF-8 CSV")
    parser.add_argument("round_trip", type=Path, help="Silmaril-produced Arrow IPC")
    args = parser.parse_args()
    fixture = json.loads((FIXTURES / "fixture.json").read_text(encoding="utf-8"))
    producer = fixture["producer"]
    assert pa.__version__ == pa.cpp_build_info.version == producer["version"]
    assert np.__version__ == producer["numpy_version"]
    ipc = (FIXTURES / fixture["path"]).read_bytes()
    assert hashlib.sha256(ipc).hexdigest() == fixture["sha256"]
    with pa.ipc.open_stream(ipc) as reader:
        schema = reader.schema
        assert schema == pa.schema([pa.field("n", pa.int32()), pa.field("téxt", pa.string())])
        names = schema.names
        batches = [batch.to_pylist() for batch in reader]
    assert batches == fixture["batches"]
    records = [names] + [
        ["N" if row[name] is None else "T" + str(row[name]) for name in names]
        for batch in batches for row in batch
    ]
    buffer = io.StringIO(newline="")
    csv.writer(buffer, quoting=csv.QUOTE_ALL, lineterminator="\r\n").writerows(records)
    expected = buffer.getvalue().encode("utf-8")
    assert args.output.read_bytes() == expected
    assert list(csv.reader(io.StringIO(expected.decode("utf-8"), newline=""))) == records
    emitted = args.round_trip.read_bytes()
    with pa.ipc.open_stream(emitted) as reader:
        assert reader.schema == schema
        (batch,) = list(reader)
        batch.validate(full=True)
        assert batch.num_rows == len(records) - 1
        assert batch.to_pylist() == [row for group in batches for row in group]
    print(f"batch rows {[len(batch) for batch in batches]}, {len(expected)} exact UTF-8 CSV bytes, "
          f"SHA-256 {hashlib.sha256(expected).hexdigest()}")
    print(f"round trip: {batch.num_rows} rows in one batch, {len(emitted)} IPC bytes, "
          f"SHA-256 {hashlib.sha256(emitted).hexdigest()}")


if __name__ == "__main__":
    main()
