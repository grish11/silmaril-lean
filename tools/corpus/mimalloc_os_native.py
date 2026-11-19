#!/usr/bin/env python3
"""Finite direct execution of existing canonical x86 ELF; not a rebuild or proof."""
import ctypes
import hashlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ELF = ROOT / 'corpus/elf/mimalloc/x86_64/libmimalloc.so.2.1'


class DlInfo(ctypes.Structure):
    _fields_ = [('name', ctypes.c_char_p), ('base', ctypes.c_void_p),
                ('symbol', ctypes.c_char_p), ('address', ctypes.c_void_p)]


def main():
    assert hashlib.sha256(ELF.read_bytes()).hexdigest() == '3e289e6c3f60e0bf53c93dcbb782cc845500c07358dc104c5a48156bf0e67f31'
    library = ctypes.CDLL(str(ELF), mode=ctypes.RTLD_LOCAL)
    info = DlInfo()
    dladdr = ctypes.CDLL(None).dladdr
    dladdr.argtypes = [ctypes.c_void_p, ctypes.POINTER(DlInfo)]
    assert dladdr(ctypes.cast(library.mi_version, ctypes.c_void_p), ctypes.byref(info)) != 0
    base = info.base
    raw = ELF.read_bytes()
    for address, size in [(0xf230, 8), (0xf240, 19)]:
        assert ctypes.string_at(base + address, size) == raw[address:address + size]
    fields = (ctypes.c_uint64 * 2).from_address(base + 0x22ae0)
    original = list(fields)
    functions = [ctypes.CFUNCTYPE(ctypes.c_uint64)(base + a) for a in [0xf230, 0xf240]]
    count = 0
    try:
        for page in [0, 4096, 65536, 1 << 63, (1 << 64) - 1]:
            for large in [0, 2097152, (1 << 64) - 1]:
                fields[:] = [page, large]
                for index, function in enumerate(functions):
                    expected = page if index == 0 or large == 0 else large
                    assert function() == expected
                    assert list(fields) == [page, large], 'global fields changed'
                    count += 1
    finally:
        fields[:] = original
    print(f'PASS {count} canonical native global-getter cases; exact code and global placement; original fields restored')


if __name__ == '__main__':
    main()
