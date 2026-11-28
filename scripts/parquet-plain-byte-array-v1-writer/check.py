"""Independently read Lean-emitted PLAIN BYTE_ARRAY V1 pages with Thrift and PyArrow."""

import argparse
from hashlib import sha256
from importlib.metadata import version
import os
from pathlib import Path
from runpy import run_path
import struct
import subprocess

import pyarrow as pa
import pyarrow.parquet as pq
from thrift.Thrift import TType
from thrift.protocol.TCompactProtocol import TCompactProtocol
from thrift.transport.TTransport import TMemoryBuffer


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OPAQUE = b"\xff\0\x80"
LONG = b"*" * 20
CASES = {
    "required": (False, [b"", OPAQUE, LONG]),
    "mixed": (True, [None, b"", OPAQUE, None, LONG]),
    "all-null": (True, [None, None, None]),
    "required-empty": (False, []),
    "optional-empty": (True, []),
}
PINS = {
    "all-null.page": "cacf37174ff606ddec8bc069a12d4de2a3b187feaeb2e27b85b3c92fb21ec7e4",
    "all-null.parquet": "3b1acedcbcc7f969272b9f4b247672d5e24c8ba3a11962fa36b381a030f32773",
    "mixed.page": "60530bfaf9c8ac9d86e72258bffd26931899c0f1d06fb728e59763e2327e3aac",
    "mixed.parquet": "d83557f5e35a2d64a26a81915b03e06be91865510f43df8c57e3a00416ba50b1",
    "optional-empty.page": "e9a2ec1ee8c14cd7f10df8f2c484faa78052503169a9c57c90ab9c6520e73e9a",
    "required-empty.page": "b46627d1c8750535ac29d1e4b1bc7a14d26291aecb57178f919c6a2553d99be4",
    "required.page": "60500651478ae3d7489476033ca949a07e34bc6e0a825f91087337ecc7fb3391",
    "required.parquet": "a434b78cf4e0db11ca7234ed13112a64da71d33cc2cae4529cd2a23d36994aa7",
}


def pin(path, wire):
    digest = sha256(wire).hexdigest()
    print(f"{digest}  {path.name}")
    assert digest == PINS[path.name], f"{path.name}: fixture hash changed"


def with_page(thrift, schema, slots, page, scalars):
    sink = pa.BufferOutputStream()
    pq.write_table(pa.Table.from_arrays([pa.array(slots, type=pa.binary())], schema=schema), sink,
                   compression="NONE", data_page_version="1.0", version="2.6",
                   row_group_size=len(slots), use_dictionary=False, column_encoding="PLAIN",
                   write_statistics=False, write_page_index=False, write_page_checksum=False,
                   store_schema=False)
    seed = sink.getvalue().to_pybytes()
    with pq.ParquetFile(pa.BufferReader(seed)) as source:
        assert source.read().column(0).to_pylist() == slots
        assert source.metadata.num_row_groups == 1
        column = source.metadata.row_group(0).column(0)
        assert column.data_page_offset == 4
        assert column.total_compressed_size == column.total_uncompressed_size
        old_page_size = column.total_compressed_size
    footer_start = len(seed) - 8 - struct.unpack_from("<I", seed, len(seed) - 8)[0]
    assert footer_start == 4 + old_page_size
    if not schema.field(0).nullable:
        assert seed[4:footer_start].endswith(scalars)

    def sizes(metadata):
        (group,) = thrift["list_field"](metadata, 4)
        column = thrift["column_metadata"](metadata, column=0)
        for fields, ids in ((group, (2, 6)), (column, (6, 7))):
            for index in ids:
                if index in fields:
                    assert fields[index] == (TType.I64, old_page_size)
                    fields[index] = (TType.I64, len(page))

    return thrift["rewrite_footer"](seed[:4] + page + seed[footer_start:], sizes)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    out = parser.parse_args().out.resolve()
    assert pa.__version__ == pa.cpp_build_info.version == "26.0.1"
    assert version("thrift") == "0.25.0"
    subprocess.run(
        [os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
         "-DwarningAsError=true", "--run", str(HERE / "Write.lean"), str(out)],
        cwd=ROOT, check=True,
    )
    thrift = run_path(str(ROOT / "tests/formats/parquet-timestamp-leaf/check-fixtures.py"))
    header_fields = run_path(str(ROOT / "scripts/parquet-scalar-page/PyArrowOracle.py"))["header_fields"]
    for name, (nullable, slots) in CASES.items():
        path = out / f"{name}.page"
        page = path.read_bytes()
        memory = TMemoryBuffer(page)
        header = header_fields(TCompactProtocol(memory), (5,))
        body = page[memory.cstringio_buf.tell():]
        assert header == {1: 0, 2: len(body), 3: len(body), 5: {1: len(slots), 2: 0, 3: 3, 4: 3}}
        levels = bytes(octet for slot in slots for octet in (2, int(slot is not None))) if nullable else b""
        scalars = b"".join(struct.pack("<i", len(slot)) + slot for slot in slots if slot is not None)
        assert body == (struct.pack("<I", len(levels)) + levels if nullable else b"") + scalars
        pin(path, page)
        if slots:
            schema = pa.schema([pa.field("raw", pa.binary(), nullable=nullable)])
            wire = with_page(thrift, schema, slots, page, scalars)
            path = out / f"{name}.parquet"
            with pq.ParquetFile(pa.BufferReader(wire)) as source:
                leaf = source.schema.column(0)
                column = source.metadata.row_group(0).column(0)
                assert leaf.physical_type == "BYTE_ARRAY" and leaf.logical_type.type == "NONE"
                assert leaf.max_repetition_level == 0 and leaf.max_definition_level == int(nullable)
                assert column.compression == "UNCOMPRESSED" and not column.has_dictionary_page
                assert column.total_compressed_size == column.total_uncompressed_size == len(page)
                assert source.schema_arrow.equals(schema) and source.read().column(0).to_pylist() == slots
            pin(path, wire)
            path.write_bytes(wire)
    print("Thrift and the byte oracle checked five headers and bodies. PyArrow read three re-framed files.")


if __name__ == "__main__":
    main()
