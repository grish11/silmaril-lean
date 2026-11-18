"""Actual public registry/ELF export and rejection regressions; no corpus builds."""
from contextlib import closing
import importlib.util
import json
from pathlib import Path
import sqlite3
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('compiler_corpus', ROOT / 'tools/compiler-explorer/corpus.py')
corpus = importlib.util.module_from_spec(spec)
spec.loader.exec_module(corpus)


class CorpusCompilerBindings(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.work = Path(self.tmp.name)
        self.project = self.work / 'public.sqlite'
        self.statements = [s for s in json.loads((ROOT / corpus.REGISTRY).read_text())['statements'] if s['kind'] == 'contextual_c_to_elf']
        with closing(sqlite3.connect(self.project)) as db, db:
            db.executescript('CREATE TABLE corpus_meta(key TEXT,value TEXT); CREATE TABLE corpus_artifacts(id TEXT,path TEXT,sha256 TEXT); CREATE TABLE corpus_functions(artifact TEXT,symbol TEXT,address INTEGER,size INTEGER);')
            db.execute('INSERT INTO corpus_meta VALUES(?,?)', ('revision', 'a' * 40))
            artifacts = {}
            for s in self.statements:
                for name, digest in s['artifact_sha256'].items():
                    if name not in artifacts:
                        artifacts[name] = str(len(artifacts))
                        db.execute('INSERT INTO corpus_artifacts VALUES(?,?,?)', (artifacts[name], name, digest))
                    f = corpus.elf_function((ROOT / name).read_bytes(), s['function_symbol'], s.get('function_address'))
                    db.execute('INSERT INTO corpus_functions VALUES(?,?,?,?)', (artifacts[name], s['function_symbol'], f['address'], f['size']))
                    for manifest in (ROOT / 'corpus/compiler-bindings').glob('*.json'):
                        m = json.loads(manifest.read_text())
                        if m['registry_root'] == s['root']:
                            for callee in m.get('callees', []):
                                actual = corpus.elf_function((ROOT / name).read_bytes(), callee['symbol'], callee['address'])
                                db.execute('INSERT INTO corpus_functions VALUES(?,?,?,?)', (artifacts[name], callee['symbol'], actual['address'], actual['size']))

    def test_every_registered_problem_exports_without_proof_promotion(self):
        output = self.work / 'out'
        rows = corpus.export(self.project, output)
        self.assertEqual({r['declaration'] for r in rows}, {s['declaration'] for s in self.statements})
        self.assertEqual(len(rows), 30)
        for row in rows:
            p = json.loads((output / Path(row['static_path']).name).read_text())
            self.assertEqual(p['status'], 'UNPROVED')
            self.assertIsNone(p['proof_evidence'])
            self.assertIsNone(p['exporter_run'])
            self.assertFalse(p['interactive_compilation'])
            self.assertTrue(p['source']['projection']['spans'])
        null = next(r for r in rows if r['function_symbol'] == 'cJSON_IsNull')
        p = json.loads((output / Path(null['static_path']).name).read_text())
        self.assertEqual(p['source']['sha256'], 'c09e52545b71dcc83e603c21a65821a692bffbc4cb7fd3913a6660fc0fc942ab')
        self.assertEqual(p['core']['sha256'], '5567495bd982a19d43237278e2ce8455609fbf87d10f8c863c92b0f13243593a')
        self.assertEqual(p['artifacts'][0]['address'], 21600)
        self.assertEqual(p['artifacts'][0]['bytes_hex'], '48 85 ff 74 0b 31 c0 80 7f 18 04 0f 94 c0 c3 90 31 c0 c3')

    def test_actual_boolean_getter_identity_and_limits(self):
        output = self.work / 'out'
        rows = corpus.export(self.project, output)
        for symbol, address, code in [('_mi_os_has_overcommit', 61968, '0f b6 05 f1 38 01 00 c3'),
                                      ('_mi_os_has_virtual_reserve', 61984, '0f b6 05 e3 38 01 00 c3')]:
            row = next(r for r in rows if r['function_symbol'] == symbol)
            p = json.loads((output / Path(row['static_path']).name).read_text())
            self.assertEqual(p['source']['sha256'], '2e3f89c48db58c79a63cee47c143bdd05a6ef81fbae56ca41760e70292890885')
            self.assertEqual(p['core']['sha256'], '66bf5e95d82ee9cbd83fde17d4c0ed92571df1f4f4ecd868f96ff47a66d94434')
            self.assertEqual(p['artifacts'][0]['address'], address)
            self.assertEqual(p['artifacts'][0]['bytes_hex'], code)
            self.assertIn('Noncanonical _Bool bytes', ' '.join(p['limits']))

    def test_actual_detachment_pointer_return_and_exact_heap_context(self):
        output = self.work / 'out'
        rows = corpus.export(self.project, output)
        row = next(r for r in rows if r['function_symbol'] == 'cJSON_DetachItemViaPointer')
        p = json.loads((output / Path(row['static_path']).name).read_text())
        self.assertEqual(p['status'], 'UNPROVED')
        self.assertEqual(p['artifacts'][0]['address'], 23724)
        self.assertEqual(len(bytes.fromhex(p['artifacts'][0]['bytes_hex'])), 218)
        limits = ' '.join(p['limits'])
        for expected in ['arbitrary admissible addresses', 'arbitrary320', 'provenance',
                         'RAX pointer', 'ONLY diagnostic currentLocation', 'Only32', 'Unsupported']:
            self.assertIn(expected, limits)

    def test_actual_caller_helper_and_callee_catalog_rejection(self):
        output = self.work / 'out'
        rows = corpus.export(self.project, output)
        row = next(r for r in rows if r['function_symbol'] == 'cJSON_GetArrayItem')
        p = json.loads((output / Path(row['static_path']).name).read_text())
        self.assertEqual((p['artifacts'][0]['address'], p['artifacts'][0]['size']), (0x5427, 51))
        helper = p['artifacts'][0]['callees'][0]
        self.assertEqual((helper['function_symbol'], helper['address'], helper['size']), ('get_array_item', 0x53d3, 84))
        self.assertEqual(len(bytes.fromhex(helper['bytes_hex'])), 84)
        for clause in ['signed32', 'unsigned64', 'arbitrary payload', '72 bytes', 'not full-record', 'not proofs']:
            self.assertIn(clause, ' '.join(p['limits']))
        with closing(sqlite3.connect(self.project)) as db, db:
            db.execute("UPDATE corpus_functions SET address=0 WHERE symbol='get_array_item'")
        with self.assertRaisesRegex(ValueError, 'catalog callee mismatch'):
            corpus.export(self.project, self.work / 'wrong-callee')

    def test_wrong_callee_address_size_and_unbounded_list_rejected(self):
        name = 'CjsonArrayItem-Context.json'
        original = Path.read_bytes
        manifest = json.loads((ROOT / 'corpus/compiler-bindings' / name).read_text())
        mutations = [({'symbol':'get_array_item','address':0x53d4,'size':84}, 'ambiguous/missing'),
                     ({'symbol':'get_array_item','address':0x53d3,'size':83}, 'callee ELF size mismatch')]
        for i, (callee, _) in enumerate(mutations):
            changed = {**manifest, 'callees':[callee]}
            with patch.object(Path, 'read_bytes', lambda path: json.dumps(changed).encode() if path.name == name else original(path)):
                with self.assertRaisesRegex(ValueError, 'stale registered'):
                    corpus.export(self.project, self.work / str(i))
        changed = {**manifest, 'callees':manifest['callees']*9}
        with patch.object(Path, 'read_bytes', lambda path: json.dumps(changed).encode() if path.name == name else original(path)):
            with self.assertRaisesRegex(ValueError, 'stale registered'):
                corpus.export(self.project, self.work / 'unbounded')

    def test_stale_source_and_private_path_rejected(self):
        source = 'corpus/cjson/semantic-inputs/linux-x86_64/predicates/context.c'
        altered = self.work / 'changed.c'
        altered.write_bytes((ROOT / source).read_bytes() + b'\n')
        original = corpus.public_file
        with patch.object(corpus, 'public_file', side_effect=lambda root, name: altered if name == source else original(root, name)):
            with self.assertRaisesRegex(ValueError, 'stale registered'):
                corpus.export(self.project, self.work / 'out')
        for name in ['../private.sqlite', '/tmp/private.sqlite', 'tools/../../private.sqlite', 'tools/../private.sqlite']:
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, 'non-public'):
                original(ROOT, name)

    def test_catalog_identity_and_function_mismatches_rejected(self):
        with closing(sqlite3.connect(self.project)) as db, db:
            db.execute("UPDATE corpus_functions SET address=0 WHERE symbol='cJSON_IsNull'")
        with self.assertRaisesRegex(ValueError, 'catalog function mismatch'):
            corpus.export(self.project, self.work / 'out')
        with closing(sqlite3.connect(self.project)) as db, db:
            db.execute("UPDATE corpus_artifacts SET sha256='stale'")
        with self.assertRaisesRegex(ValueError, 'catalog artifact mismatch'):
            corpus.export(self.project, self.work / 'other')

    def test_wrong_elf_placement_rejected(self):
        data = (ROOT / 'corpus/elf/cjson/x86_64/libcjson.so.1').read_bytes()
        with self.assertRaisesRegex(ValueError, 'ambiguous/missing'):
            corpus.elf_function(data, 'cJSON_IsNull', 21601)


if __name__ == '__main__':
    unittest.main()
