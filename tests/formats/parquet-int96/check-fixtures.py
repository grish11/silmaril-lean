"""Check INT96 against a pinned Spark file and PyArrow's legacy writer."""

from datetime import date
import hashlib
import os
from pathlib import Path
import struct
import subprocess
import sys
import tempfile

import pyarrow as pa
import pyarrow.parquet as pq


SPARK_SHA256 = "e769aaa996dee57f1104470dcce16d6871cd720d314c13361db16bf9e49f5c97"
GENERATED_SHA256 = "a79306aece11396ec428364865286309d0fb32f45b2d626cd4aa468cf264bdbd"
NANOSECONDS_PER_DAY = 86_400_000_000_000


def add_checks(checks, data, expected_nanos):
    nanos, julian = struct.unpack("<qi", data)
    wire = str(list(data))
    if expected_nanos is None:
        assert nanos < 0
        checks.append(f"#guard Payload.decode? {wire} = none")
        return
    epoch_day = expected_nanos // NANOSECONDS_PER_DAY
    civil = date.fromordinal(date(1970, 1, 1).toordinal() + epoch_day)
    checks.extend([
        f"#guard (Payload.decode? {wire}).map (fun p => (p.julianDay.toInt, p.nanosecondOfDay.val))"
        f" = some (({julian}), {nanos})",
        f"#guard (Payload.decode? {wire}).map (·.toGregorian.date)"
        f" = some ⟨{civil.year}, {civil.month}, {civil.day}⟩",
    ])
    for policy, kind in (("prolepticUtc", "utcInstant"), ("prolepticLocal", "localReading")):
        checks.extend([
            f"#guard (Payload.decode? {wire}).map (fun p => (p.toTicks .{policy}).ticks)"
            f" = some ({expected_nanos})",
            f"#guard (Payload.ofTicks? .{policy} (⟨{expected_nanos}⟩ : Ticks .{kind} .nanosecond))"
            f".map Payload.encode = some {wire}",
        ])


def spark_checks(path, checks):
    data = path.read_bytes()
    assert hashlib.sha256(data).hexdigest() == SPARK_SHA256
    parquet = pq.ParquetFile(pa.BufferReader(data), coerce_int96_timestamp_unit="us")
    column = parquet.metadata.row_group(0).column(0)
    assert (column.physical_type, column.compression) == ("INT96", "SNAPPY")
    assert (column.dictionary_page_offset, column.data_page_offset) == (4, 81)
    assert parquet.metadata.metadata[b"org.apache.spark.version"] == b"3.4.3"
    # The pinned file's dictionary PageHeader is exactly bytes [4, 23).
    raw = pa.Codec("snappy").decompress(data[23:81], 60).to_pybytes()
    oracle = parquet.read().column(0).cast(pa.int64()).to_pylist()
    assert len(oracle) == 6 and oracle[4] is None
    for index, micros in enumerate(oracle[:4]):
        add_checks(checks, raw[index * 12:(index + 1) * 12], micros * 1000)
    # The fifth dictionary word contains a negative nanos-of-day field.
    add_checks(checks, raw[48:60], None)


def writer_checks(checks):
    checksum = hashlib.sha256()
    old_day = (date(1500, 3, 1) - date(1970, 1, 1)).days
    cases = [
        ("ns", [-(2**63), -NANOSECONDS_PER_DAY - 1, -NANOSECONDS_PER_DAY, -1, 0, 1, 2**63 - 1]),
        ("us", [old_day * 86_400_000_000 + 1, -1, 0, 1]),
    ]
    for unit, counts in cases:
        field = pa.field("ts", pa.timestamp(unit), nullable=False)
        array = pa.array(counts, type=pa.int64()).cast(field.type)
        table = pa.Table.from_arrays([array], schema=pa.schema([field]))
        buffer = pa.BufferOutputStream()
        pq.write_table(table, buffer, use_deprecated_int96_timestamps=True, compression="NONE",
                       use_dictionary=False, write_statistics=False, store_schema=False,
                       data_page_version="1.0")
        data = buffer.getvalue().to_pybytes()
        checksum.update(len(data).to_bytes(8, "little"))
        checksum.update(data)
        parquet = pq.ParquetFile(pa.BufferReader(data), coerce_int96_timestamp_unit=unit)
        column = parquet.metadata.row_group(0).column(0)
        assert (column.physical_type, column.compression) == ("INT96", "UNCOMPRESSED")
        assert column.encodings == ("RLE", "PLAIN") and column.dictionary_page_offset is None
        assert parquet.metadata.num_row_groups == 1 and column.num_values == len(counts)
        oracle = parquet.read().column(0).cast(pa.int64()).to_pylist()
        assert oracle == counts
        # One small, uncompressed, required column page ends with its PLAIN values.
        end = column.data_page_offset + column.total_compressed_size
        raw = data[end - 12 * len(counts):end]
        for index, tick in enumerate(oracle):
            add_checks(checks, raw[index * 12:(index + 1) * 12], tick * (1000 if unit == "us" else 1))
    actual = checksum.hexdigest()
    assert actual == GENERATED_SHA256, f"generated Parquet bytes SHA-256 {actual}"


def main():
    assert pa.__version__ == "26.0.1", pa.__version__
    header = """module
import Silmaril.Formats.Parquet.Int96.Defs
meta import Silmaril.Formats.Parquet.Int96.Defs
meta import Silmaril.Numeric.Gregorian.Defs
meta import Silmaril.Numeric.Timestamp.Defs
open Silmaril.Formats.Parquet.Int96 Silmaril.Numeric.Timestamp
"""
    checks = []
    spark_checks(Path(sys.argv[1]), checks)
    writer_checks(checks)
    root = Path(__file__).resolve().parents[3]
    with tempfile.TemporaryDirectory() as directory:
        lean = Path(directory) / "Fixture.lean"
        lean.write_text(header + "\n".join(checks) + "\n", encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(lean)], cwd=root, check=True)
    print(f"PyArrow {pa.__version__}: {len(checks)} Lean checks on 16 INT96 writer payloads")
    print(f"Spark file SHA-256 {SPARK_SHA256}")
    print(f"Generated Parquet bytes SHA-256 {GENERATED_SHA256}")


if __name__ == "__main__":
    main()
