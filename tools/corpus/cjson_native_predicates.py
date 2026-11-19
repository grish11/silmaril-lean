#!/usr/bin/env python3
"""Finite canonical ELF executions; no semantic equivalence or new build claim."""
import ctypes
import hashlib
import json
import platform
from pathlib import Path


class CJSON(ctypes.Structure):
    _fields_ = [
        ("next", ctypes.c_void_p), ("prev", ctypes.c_void_p),
        ("child", ctypes.c_void_p), ("type", ctypes.c_int),
        ("valuestring", ctypes.c_void_p), ("valueint", ctypes.c_int),
        ("valuedouble", ctypes.c_double), ("string", ctypes.c_void_p),
    ]


def main():
    if platform.system() != "Linux" or platform.machine() != "x86_64":
        raise SystemExit("requires Linux x86_64 for actual canonical ELF execution")
    elf = Path(__file__).resolve().parents[2] / "corpus/elf/cjson/x86_64/libcjson.so.1"
    digest = hashlib.sha256(elf.read_bytes()).hexdigest()
    assert digest == "2cfb516d75b79b4ee7ba9e9645fc5f53daa4f428daf349d445d3bbd43e4576c2"
    assert ctypes.sizeof(CJSON) == 64
    assert ctypes.alignment(CJSON) == 8 and CJSON.type.offset == 24
    library = ctypes.CDLL(str(elf))
    rows = []
    for suffix, kind in [("Null", 4), ("Bool", 3), ("Number", 8),
                         ("String", 16), ("Array", 32), ("Object", 64),
                         ("Invalid", 0), ("False", 1), ("True", 2), ("Raw", 128)]:
        name = "cJSON_Is" + suffix
        function = getattr(library, name)
        function.argtypes = [ctypes.POINTER(CJSON)]
        function.restype = ctypes.c_int
        for value in dict.fromkeys([0, kind, kind + 256, 1, -256 + kind]):
            obj = CJSON()
            obj.type = value
            before = bytes(obj)
            got = function(ctypes.byref(obj))
            want = int(value & 3 != 0) if suffix == "Bool" else int(value & 255 == kind)
            assert got == want, (name, value, got, want)
            assert bytes(obj) == before
            rows.append({"name": name, "type": value, "null": False,
                         "result": got, "bytes_unchanged": True})
        assert function(None) == 0
        rows.append({"name": name, "null": True, "result": 0})
    print(json.dumps({
        "status": "finite native execution evidence, not semantic equivalence or a new build",
        "artifact_sha256": digest, "size": 64, "alignment": 8,
        "type_offset": 24, "cases": rows,
    }, indent=2))
    print(f"PASS {len(rows)} canonical ELF cases; layout64/8/type24; object bytes unchanged")


if __name__ == "__main__":
    main()
