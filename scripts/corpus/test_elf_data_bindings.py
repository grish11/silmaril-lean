"""Real saved SQLite object/relocation evidence and identity negatives."""
import copy
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
loader = importlib.util.spec_from_file_location('data_bindings', ROOT / 'tools/compiler-explorer/data_bindings.py')
bindings = importlib.util.module_from_spec(loader)
loader.loader.exec_module(bindings)

class DataBindings(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = (ROOT / 'corpus/elf/sqlite/x86_64/libsqlite3.so').read_bytes()
        cls.spec = dict(symbol='sqlite3_version', address=0xed572, size=7,
                        bytes_hex='33 2e 35 34 2e 31 00',
                        relocation=dict(file_offset=53296, slot=0x10efc8, symbol_index=233,
                                        slot_bytes_hex='00 00 00 00 00 00 00 00'))

    def test_actual_object_and_raw_relocation(self):
        item, = bindings.export(self.data, [self.spec])
        self.assertEqual(item['bytes_hex'], self.spec['bytes_hex'])
        self.assertEqual(item['relocation']['slot'], 0x10efc8)
        self.assertEqual(item['relocation']['slot_bytes_hex'], '00 00 00 00 00 00 00 00')
        self.assertEqual(len(bytes.fromhex(item['relocation']['bytes_hex'])), 24)
        self.assertIn('No dynamic-loader', item['limit'])

    def test_identity_and_range_negatives(self):
        for key, value in [('symbol', 'sqlite3_libversion'), ('address', 0xed573),
                           ('size', 8), ('bytes_hex', '00'), ('size', 4097)]:
            with self.subTest(key=key, value=value):
                spec = copy.deepcopy(self.spec); spec[key] = value
                with self.assertRaises(ValueError): bindings.export(self.data, [spec])
        for key, value in [('file_offset', 53297), ('slot', 0x10efd0), ('symbol_index', 234)]:
            with self.subTest(key=key):
                spec = copy.deepcopy(self.spec); spec['relocation'][key] = value
                with self.assertRaises(ValueError): bindings.export(self.data, [spec])

    def test_actual_bytes_and_relocation_mutations(self):
        item, = bindings.export(self.data, [self.spec])
        for offset in [item['file_offset'], 53296, 53304, 53312, item['relocation']['slot_file_offset']]:
            with self.subTest(offset=offset):
                data = bytearray(self.data); data[offset] ^= 1
                with self.assertRaises(ValueError): bindings.export(data, [self.spec])

    def test_bounded_binding_count(self):
        with self.assertRaises(ValueError): bindings.export(self.data, [self.spec] * 9)

if __name__ == '__main__': unittest.main()
