"""Pin zero-page PyArrow DATE metadata, controls, and native IPC readbacks."""

import argparse
from copy import deepcopy
from importlib.metadata import version
import json
import os
from pathlib import Path
import runpy
import struct
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/PageLess/Tests.lean"
CASES = {
    "optional_middle": ("日付", True, [[-1, None], [], [11016, 0]]),
    "required_empty": ("époque", False, [[]]),
    "required_schema_only": ("époque", False, []),
}


def codecs(types):
    scalar = {types.BOOL: "Bool", types.I16: "I16", types.I32: "I32",
              types.I64: "I64", types.STRING: "Binary"}

    def read(protocol, kind):
        if kind in scalar:
            return getattr(protocol, "read" + scalar[kind])()
        if kind == types.STRUCT:
            result = {}
            protocol.readStructBegin()
            while True:
                _, field_type, index = protocol.readFieldBegin()
                if field_type == types.STOP:
                    break
                assert index not in result
                result[index] = (field_type, read(protocol, field_type))
                protocol.readFieldEnd()
            protocol.readStructEnd()
            return result
        assert kind == types.LIST
        element, count = protocol.readListBegin()
        result = element, [read(protocol, element) for _ in range(count)]
        protocol.readListEnd()
        return result

    def write(protocol, kind, value):
        if kind in scalar:
            getattr(protocol, "write" + scalar[kind])(value)
        elif kind == types.STRUCT:
            protocol.writeStructBegin("")
            for index, (field_type, payload) in sorted(value.items()):
                protocol.writeFieldBegin("", field_type, index)
                write(protocol, field_type, payload)
                protocol.writeFieldEnd()
            protocol.writeFieldStop()
            protocol.writeStructEnd()
        else:
            assert kind == types.LIST
            element, values = value
            protocol.writeListBegin(element, len(values))
            for item in values:
                write(protocol, element, item)
            protocol.writeListEnd()

    return read, write


def digest_structure(groups):
    result = []
    for group in groups:
        _, (_, [chunk]) = group[1]
        _, column = chunk[3]
        result.append({
            "row_group_ids": list(group),
            "row_group_ordinal": group.get(7, (None, None))[1],
            "row_group_file_offset": group[5][1],
            "row_group_total_byte_size": group[2][1],
            "row_group_total_compressed_size": group[6][1],
            "num_rows": group[3][1],
            "column_chunk_ids": list(chunk),
            "column_chunk_file_offset": chunk[2][1],
            "column_metadata_ids": list(column),
            "physical_type": column[1][1],
            "encodings": column[2][1][1],
            "codec": column[4][1],
            "num_values": column[5][1],
            "total_uncompressed_size": column[6][1],
            "total_compressed_size": column[7][1],
            "data_page_offset": column[9][1],
            "encoding_stats_count": len(column[13][1][1]),
        })
    return result


def lean_slots(groups):
    return "[" + ", ".join("[" + ", ".join("none" if word is None else f"some ({word})"
                                           for word in batch) + "]" for batch in groups) + "]"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pyarrow-path", type=Path)
    parser.add_argument("--thrift-path", type=Path)
    parser.add_argument("--regenerate", action="store_true", help="Update exact fixture fingerprints")
    args = parser.parse_args()
    for path in (args.pyarrow_path, args.thrift_path):
        if path is not None:
            sys.path.insert(0, str(path.resolve()))
    import pyarrow as pa
    import pyarrow.parquet as pq
    from thrift.Thrift import TType
    from thrift.protocol.TCompactProtocol import TCompactProtocol
    from thrift.transport.TTransport import TMemoryBuffer

    sources = ROOT / "scripts/parquet-date-csv-roundtrip-oracle"
    producer = runpy.run_path(str(sources / "check.py"))
    ipc = runpy.run_path(str(ROOT / "scripts/arrow-date32-writer-oracle/check.py"))
    parquet = runpy.run_path(str(ROOT / "scripts/parquet-date-oracle/check.py"))
    read_struct, write_struct = codecs(TType)
    prior = json.loads((sources / "fixtures.json").read_text(encoding="utf-8"))
    pin = {key: prior[key] for key in
           ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift", "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == pin["pyarrow"]
    assert version("thrift") == pin["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == pin["lean_toolchain"]

    fingerprint = ipc["hash_bytes"]
    lean_file = parquet["lean_bytes"]
    pin["cases"] = {}
    with tempfile.TemporaryDirectory(prefix="parquet-date-pageless-") as temporary:
        folder = Path(temporary)
        commands = []
        inputs = {}
        for case, (name, nullable, groups) in CASES.items():
            schema = pa.schema([pa.field(name, pa.date32(), nullable=nullable)])
            wire = producer["source_file"](pa, pq, schema, groups)
            opened = pq.ParquetFile(pa.BufferReader(wire))
            assert opened.schema_arrow == schema and opened.num_row_groups == len(groups)
            for index, slots in enumerate(groups):
                assert opened.read_row_group(index).column(0).combine_chunks().view(pa.int32()).to_pylist() == slots
            start = len(wire) - 8 - struct.unpack("<I", wire[-8:-4])[0]
            raw = read_struct(TCompactProtocol(TMemoryBuffer(wire[start:-8])), TType.STRUCT)
            actual = digest_structure(raw[4][1][1])
            for group, rows in zip(actual, groups, strict=True):
                if not rows:
                    assert group == {
                        "row_group_ids": [1, 2, 3, 5, 6], "row_group_ordinal": None,
                        "row_group_file_offset": 0, "row_group_total_byte_size": 0,
                        "row_group_total_compressed_size": 0, "num_rows": 0,
                        "column_chunk_ids": [2, 3], "column_chunk_file_offset": 0,
                        "column_metadata_ids": [1, 2, 3, 4, 5, 6, 7, 9, 13],
                        "physical_type": 1, "encodings": [3], "codec": 0, "num_values": 0,
                        "total_uncompressed_size": 0, "total_compressed_size": 0,
                        "data_page_offset": 0, "encoding_stats_count": 0,
                    }
            path = folder / (case + ".arrows")
            inputs[case] = (wire, start, raw, schema, path)
            commands.append(f"#eval observe {json.dumps(str(path))} {lean_file(wire)} "
                            f"{json.dumps(name, ensure_ascii=False)} {str(nullable).lower()} {lean_slots(groups)}")
            if any(not batch for batch in groups):
                commands.append(f"#guard strictRejects {lean_file(wire)}")
            pin["cases"][case] = {"parquet": fingerprint(wire), "footer_start": start,
                                  "raw_groups": actual, "signed_batches": groups}

        wire, start, raw, _, _ = inputs["optional_middle"]

        def edit(change):
            footer = deepcopy(raw)
            change(footer[4][1][1])
            memory = TMemoryBuffer()
            write_struct(TCompactProtocol(memory), TType.STRUCT, footer)
            result = memory.getvalue()
            return wire[:start] + result + struct.pack("<I", len(result)) + b"PAR1"

        assert edit(lambda _: None) == wire

        def column(groups, index):
            return groups[index][1][1][1][0][3][1]

        def overlap(groups):
            groups[2][5] = (TType.I64, 4)
            column(groups, 2)[9] = (TType.I64, 4)

        def encoding_stats(groups):
            column(groups, 1)[13] = (TType.LIST, (TType.STRUCT, [
                {1: (TType.I32, 0), 2: (TType.I32, 0), 3: (TType.I32, 1)}
            ]))

        controls = {
            "value_count": (lambda groups: column(groups, 1).__setitem__(5, (TType.I64, 1)),
                            "(.validation .pageInterval)"),
            "positive_extent": (lambda groups: column(groups, 1).__setitem__(7, (TType.I64, 1)),
                                "(.validation .pageInterval)"),
            "positive_offset": (lambda groups: column(groups, 1).__setitem__(9, (TType.I64, 4)),
                                "(.validation .pageInterval)"),
            "dictionary_offset": (lambda groups: column(groups, 1).__setitem__(11, (TType.I64, 0)),
                                  "(.validation .pageInterval)"),
            "page_encoding_stats": (encoding_stats, "(.emptyMetadata 1)"),
            "wrong_ordinal": (lambda groups: groups[1].__setitem__(7, (TType.I16, 2)), "(.ordinal 1)"),
            "overlapping_framed_group": (overlap, "(.layout 2)"),
        }
        pin["controls"] = {}
        for case, (change, error) in controls.items():
            edited = edit(change)
            commands.append(f"#guard rejects {lean_file(edited)} {error}")
            pin["controls"][case] = {"parquet": fingerprint(edited), "error": error}

        harness = folder / "Oracle.lean"
        harness.write_text(TESTS.read_text(encoding="utf-8") + "\n" + "\n".join(commands) + "\n",
                           encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(harness)], cwd=ROOT, check=True)
        for case, (_, _, groups) in CASES.items():
            _, _, _, schema, path = inputs[case]
            wire = path.read_bytes()
            ipc["observe"](pa, wire, schema, groups)
            pin["cases"][case]["lean_ipc"] = fingerprint(wire)

    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(pin, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert pin == json.loads(manifest.read_text(encoding="utf-8")), json.dumps(pin, indent=2)
    print(f"PASS {len(CASES)} PyArrow DATE sources, exact native IPC readbacks, and {len(controls)} Thrift edits")


if __name__ == "__main__":
    main()
