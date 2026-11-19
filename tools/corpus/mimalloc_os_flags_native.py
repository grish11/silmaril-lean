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
    entries = [(0xf210, bytes.fromhex('0fb605f1380100c3')),
               (0xf220, bytes.fromhex('0fb605e3380100c3'))]
    for address, code in entries:
        assert ctypes.string_at(base + address, len(code)) == code == raw[address:address + len(code)]
    fields = (ctypes.c_ubyte * 3).from_address(base + 0x22ae0 + 40)
    original = bytes(fields)
    functions = [ctypes.CFUNCTYPE(ctypes.c_ubyte)(base + address) for address, _ in entries]
    count = 0
    try:
        for overcommit in [0, 1]:
            for reserve in [0, 1]:
                fields[0], fields[2] = overcommit, reserve
                before = ctypes.string_at(base + 0x22ae0, 48)
                for function, expected in zip(functions, [overcommit, reserve]):
                    assert function() == expected
                    assert ctypes.string_at(base + 0x22ae0, 48) == before
                    count += 1
    finally:
        fields[:] = original
    print(f'PASS {count} canonical native Boolean getter cases; exact code/global placement; fields restored')


if __name__ == '__main__':
    main()
