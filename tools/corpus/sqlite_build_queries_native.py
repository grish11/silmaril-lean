#!/usr/bin/env python3
"""Execute two queries in the existing canonical ELF; no rebuild or proof."""
import ctypes
import hashlib
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ELF = ROOT / 'corpus/elf/sqlite/x86_64/libsqlite3.so'


class DlInfo(ctypes.Structure):
    _fields_ = [('name', ctypes.c_char_p), ('base', ctypes.c_void_p),
                ('symbol', ctypes.c_char_p), ('address', ctypes.c_void_p)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='optional public finite-execution receipt')
    output = parser.parse_args().output
    assert hashlib.sha256(ELF.read_bytes()).hexdigest() == 'fcdd0cd75ea98cee14f2743832c6ad2ed4dd4229e2b5093f8bce7dc33c9c17f8'
    library = ctypes.CDLL(str(ELF), mode=ctypes.RTLD_LOCAL)
    dladdr = ctypes.CDLL(None).dladdr
    dladdr.argtypes = [ctypes.c_void_p, ctypes.POINTER(DlInfo)]
    observed = []
    for name, offset, code, expected in [
        ('sqlite3_libversion_number', 79904, 'b8 b1 99 2e 00 c3', 3054001),
        ('sqlite3_threadsafe', 79920, 'b8 01 00 00 00 c3', 1),
    ]:
        function = getattr(library, name)
        function.argtypes = []
        function.restype = ctypes.c_int
        pointer = ctypes.cast(function, ctypes.c_void_p).value
        info = DlInfo()
        assert dladdr(pointer, ctypes.byref(info)) != 0
        assert pointer - info.base == offset
        actual_code = bytes.fromhex(code)
        assert ctypes.string_at(pointer, len(actual_code)) == actual_code
        result = function()
        assert result == expected
        observed.append({'symbol': name, 'address': offset, 'bytes_hex': actual_code.hex(' '),
                         'result': result, 'return_type': 'signed int', 'arguments': []})
        print(f'PASS canonical {name}: actual address/code and signed-int result={expected}; no threading guarantee')
    if output:
        output.write_text(json.dumps({
            'schema': 'silmaril.finite-native-query-check.v1',
            'artifact': str(ELF.relative_to(ROOT)),
            'artifact_sha256': hashlib.sha256(ELF.read_bytes()).hexdigest(),
            'command': ['python3', 'tools/corpus/sqlite_build_queries_native.py', '--output', '<receipt>'],
            'checks': observed,
            'limits': 'Existing canonical ELF only; no rebuild, historical build replay, threading guarantee or semantic proof.',
        }, indent=2) + '\n')


if __name__ == '__main__':
    main()
