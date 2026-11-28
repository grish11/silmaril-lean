"""Pin selected Parquet DATE leaves and independently read the native IPC."""

import argparse
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
TESTS = ROOT / "Silmaril/Formats/Parquet/Date/Leaf/Events/Tests.lean"
CASES = {
    "optional_second_v1": ("日付", True, 1, "1.0", [[-2147483648, None, -1], [2147483647, 0, 11016]]),
    "required_third_v2": ("époque", False, 2, "2.0", [[-719528, -1], [0, 11016]]),
}


def lean_groups(groups):
    return "[" + ", ".join("[" + ", ".join("none" if day is None else f"some ({day})"
                                           for day in group) + "]" for group in groups) + "]"


def produce(pa, pq, name, nullable, ordinal, page_version, groups):
    fields = [pa.field("unannotated", pa.int32(), nullable=False), pa.field("label", pa.string())]
    fields.insert(ordinal, pa.field(name, pa.date32(), nullable=nullable))
    schema = pa.schema(fields)
    with pa.BufferOutputStream() as sink:
        with pq.ParquetWriter(sink, schema, version="2.6", data_page_version=page_version,
                              use_dictionary=False, compression="NONE", write_statistics=False,
                              store_schema=False) as writer:
            for slots in groups:
                ints = pa.array(list(range(len(slots))), type=pa.int32())
                payload = pa.array(["neighbor"] * len(slots), type=pa.string())
                arrays = [ints, payload]
                arrays.insert(ordinal, pa.array(slots, type=pa.int32()).view(pa.date32()))
                writer.write_table(pa.Table.from_arrays(arrays, schema=schema))
        return sink.getvalue().to_pybytes()


def controls(source, spans, footer_start, ordinal, arrow, parquet, types, buffer, protocol, fields):
    opened = parquet.ParquetFile(arrow.BufferReader(source))

    def corrupt_page(group, column):
        chunk = opened.metadata.row_group(group).column(column)
        start = chunk.data_page_offset
        memory = buffer(source[start:start + chunk.total_compressed_size])
        reader = protocol(memory)
        for kind, field in fields(reader):
            if field != 5:
                reader.skip(kind)
                continue
            assert kind == types.STRUCT
            for kind, field in fields(reader):
                if field == 2:
                    offset = start + memory.cstringio_buf.tell()
                    assert kind == types.I32 and reader.readI32() == 0 and source[offset] == 0
                    # PLAIN (0) to RLE_DICTIONARY (8) with unchanged encoded width.
                    return source[:offset] + b"\x10" + source[offset + 1:], offset
                reader.skip(kind)
        raise AssertionError("No PLAIN V1 data page encoding field")

    def overlap():
        memory = buffer(source[footer_start:-8])
        reader = protocol(memory)
        for kind, field in fields(reader):
            if field != 4:
                reader.skip(kind)
                continue
            assert kind == types.LIST
            item, count = reader.readListBegin()
            assert item == types.STRUCT and count == 2
            for kind, field in fields(reader):  # group zero
                if field != 1:
                    reader.skip(kind)
                    continue
                item, count = reader.readListBegin()
                assert item == types.STRUCT and count == 3
                for kind, field in fields(reader):  # neighboring column zero
                    if field != 3:
                        reader.skip(kind)
                        continue
                    for kind, field in fields(reader):
                        if field != 9:
                            reader.skip(kind)
                            continue
                        offset = footer_start + memory.cstringio_buf.tell()
                        assert kind == types.I64 and reader.readI64() == 4
                        stop = footer_start + memory.cstringio_buf.tell()
                        replacement = buffer()
                        writer = protocol(replacement)
                        writer.writeStructBegin("")
                        writer.writeFieldBegin("", types.I64, 9)
                        payload_start = len(replacement.getvalue())
                        writer.writeI64(spans[0][0])
                        updated = replacement.getvalue()[payload_start:]
                        footer = source[footer_start:offset] + updated + source[stop:-8]
                        return source[:footer_start] + footer + struct.pack("<I", len(footer)) + b"PAR1", offset
        raise AssertionError("No neighbor data-page offset")

    return corrupt_page(1, ordinal), corrupt_page(1, 0), overlap()


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

    prior = ROOT / "scripts/parquet-date-csv-roundtrip-oracle"
    pin = json.loads((prior / "fixtures.json").read_text(encoding="utf-8"))
    seen = {key: pin[key] for key in
            ("cpython", "pyarrow", "pyarrow_wheel_sha256", "thrift", "thrift_wheel_sha256", "lean_toolchain")}
    assert sys.implementation.name == "cpython" and sys.version_info[:3] == (3, 13, 5)
    assert pa.__version__ == pa.cpp_build_info.version == pin["pyarrow"]
    assert version("thrift") == pin["thrift"]
    assert (ROOT / "lean-toolchain").read_text().strip() == pin["lean_toolchain"]

    oracle = runpy.run_path(str(ROOT / "scripts/parquet-date-oracle/check.py"))
    oracle["raw_leaf"].__globals__.update(TType=TType)
    ipc = runpy.run_path(str(ROOT / "scripts/arrow-date32-writer-oracle/check.py"))
    describe = ipc["hash_bytes"]
    lean_file = oracle["lean_bytes"]
    seen["cases"] = {}
    seen["controls"] = {}
    with tempfile.TemporaryDirectory(prefix="parquet-date-selected-leaf-") as temporary:
        folder = Path(temporary)
        commands = []
        native = {}
        originals = {}

        def add(case, wire, name, nullable, ordinal, groups, spans, raw):
            path = folder / (case + ".arrows")
            commands.append(f"#eval readBack {lean_file(wire)} {ordinal} {json.dumps(name, ensure_ascii=False)} "
                            f"{str(nullable).lower()} {lean_groups(groups)} {spans} {json.dumps(str(path))}")
            schema = pa.schema([pa.field(name, pa.date32(), nullable=nullable)])
            native[case] = (path, schema, groups)
            seen["cases"][case] = {"parquet": describe(wire), "physical_ordinal": ordinal,
                                    "selected_spans": [list(span) for span in spans], "raw_leaf": raw,
                                    "signed_slots": groups}

        for case, (name, nullable, ordinal, page_version, groups) in CASES.items():
            wire = produce(pa, pq, name, nullable, ordinal, page_version, groups)
            opened = pq.ParquetFile(pa.BufferReader(wire))
            assert opened.num_row_groups == len(groups)
            assert opened.schema_arrow[ordinal] == pa.field(name, pa.date32(), nullable=nullable)
            assert opened.schema_arrow[0] == pa.field("unannotated", pa.int32(), nullable=False)
            assert str(opened.schema.column(0).logical_type) == "None"
            spans = []
            for index, group in enumerate(groups):
                opened_group = opened.read_row_group(index, columns=[name])
                assert opened_group.column(0).combine_chunks().view(pa.int32()).to_pylist() == group
                chunk = opened.metadata.row_group(index).column(ordinal)
                assert chunk.num_values == len(group) and chunk.dictionary_page_offset is None
                spans.append((chunk.data_page_offset, chunk.data_page_offset + chunk.total_compressed_size))
            footer_start = len(wire) - 8 - struct.unpack("<I", wire[-8:-4])[0]
            protocol = TCompactProtocol(TMemoryBuffer(wire[footer_start:-8]))
            raw = None
            for kind, field in oracle["fields"](protocol):
                if field != 2:
                    protocol.skip(kind)
                    continue
                item, count = protocol.readListBegin()
                assert (item, count) == (TType.STRUCT, 4)
                leaf_fields = [oracle["leaf_annotation"](protocol) for _ in range(count)]
                protocol.readListEnd()
                assert "6" not in leaf_fields[1] and "10" not in leaf_fields[1]
                raw = leaf_fields[ordinal + 1]
            assert raw == {"1": 1, "3": int(nullable), "4": name, "6": 6, "10": [[6, []]]}
            originals[case] = (wire, spans, footer_start, raw)
            add(case, wire, name, nullable, ordinal, groups, spans, raw)
            commands.append(f"#guard strictRefuses {lean_file(wire)}")

        case = "optional_second_v1"
        name, nullable, ordinal, _, groups = CASES[case]
        source, spans, start, raw = originals[case]
        (late, edited), (neighbor, neighbor_edit), (overlap, overlap_edit) = controls(
            source, spans, start, ordinal, pa, pq, TType, TMemoryBuffer, TCompactProtocol, oracle["fields"])
        add("damaged_unselected_neighbor", neighbor, name, nullable, ordinal, groups, spans, raw)
        seen["cases"]["damaged_unselected_neighbor"]["thrift_edit_offset"] = neighbor_edit
        assert pq.ParquetFile(pa.BufferReader(neighbor)).read(columns=[name]).column(0).combine_chunks().view(
            pa.int32()).to_pylist() == [day for group in groups for day in group]

        refusals = {
            "unannotated_adjacent_int32": (source, 0, "(.source (.openFailure (.annotation .missingAnnotation)))", ""),
            "wrong_physical_type": (source, 2, "(.source (.openFailure (.annotation .notFlatInt32)))", ""),
            "nonexistent_column": (source, 3, "(.source (.openFailure (.footer (.leafOrdinal 4))))", ""),
            "overlapping_neighbor": (overlap, 1, "(.source (.groupFailure 0 .overlap))", ""),
            "late_selected_encoding": (late, 1, "(.source (.groupFailure 1 (.scan .unsupportedPageEncoding)))", ""),
            "output_batch_budget": (source, 1, "(.writer (.writer (.limit .batches)))",
                                    "{ ipc := { batches := 0 } }"),
        }
        for label, (wire, ordinal, error, options) in refusals.items():
            commands.append(f"#guard rejects {lean_file(wire)} {ordinal} {error} {options}".rstrip())
            seen["controls"][label] = {"parquet": describe(wire), "ordinal": ordinal, "error": error}
        seen["controls"]["late_selected_encoding"]["thrift_edit_offset"] = edited
        seen["controls"]["overlapping_neighbor"]["thrift_edit_offset"] = overlap_edit
        commands.append(f"#guard keepsPrefix {lean_file(late)} 1 {lean_groups([groups[0]])[1:-1]} "
                        "(.scan .unsupportedPageEncoding)")

        driver = folder / "Oracle.lean"
        driver.write_text(TESTS.read_text(encoding="utf-8") + "\n" + "\n".join(commands) + "\n",
                          encoding="utf-8")
        subprocess.run([os.environ.get("LAKE", "lake"), "env", "lean", "-DautoImplicit=false",
                        "-DwarningAsError=true", str(driver)], cwd=ROOT, check=True)
        for case, (path, schema, groups) in native.items():
            wire = path.read_bytes()
            ipc["observe"](pa, wire, schema, groups)
            seen["cases"][case]["lean_ipc"] = describe(wire)

    manifest = HERE / "fixtures.json"
    if args.regenerate:
        manifest.write_text(json.dumps(seen, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    else:
        assert seen == json.loads(manifest.read_text(encoding="utf-8")), json.dumps(seen, indent=2)
    print(f"PASS {len(native)} selected DATE native IPC readbacks and {len(refusals)} refusal controls")


if __name__ == "__main__":
    main()
