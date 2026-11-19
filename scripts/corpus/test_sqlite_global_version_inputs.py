"""Actual pointer-global identities and forged source/data/relocation rejection."""
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('sqlite_global_gate',ROOT/'tools/corpus/check_sqlite_global_version_inputs.py')
g=importlib.util.module_from_spec(spec);spec.loader.exec_module(g)
class SqliteGlobalInputs(unittest.TestCase):
    def fixture(self,tmp):
        root=Path(tmp);manifest=json.loads((ROOT/g.REL/'manifest.json').read_text())
        names=[g.REL/name for name in manifest['files']]+[g.REL/'manifest.json']+[Path(n) for n in manifest['immutable_files']]+[Path('Silmaril/Elf/Corpus/SqliteGlobalVersion/Source/Defs.lean'),Path('tools/compiler-explorer/corpus.py'),Path('tools/compiler-explorer/data_bindings.py')]
        for name in names:
            dest=root/name;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/name,dest)
        return root
    def test_actual_public_inputs(self):g.check(ROOT)
    def test_stale_marker(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=self.fixture(tmp);p=root/'Silmaril/Elf/Corpus/SqliteGlobalVersion/Source/Defs.lean';p.write_text(p.read_text().replace('def externalInputSha256','def staleInputSha256'))
            with self.assertRaisesRegex(AssertionError,'stale literal marker'):g.check(root)
    def test_forged_span_with_rehashed_receipts(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=self.fixture(tmp);p=root/g.REL/'projection.json';m=json.loads(p.read_text());tu=(root/m['tu']).read_bytes();span=m['spans'][0];span['offset']+=1;span['sha256']=g.digest(tu[span['offset']:span['offset']+span['length']]);p.write_text(json.dumps(m))
            q=root/g.REL/'manifest.json';manifest=json.loads(q.read_text());manifest['files']['projection.json']=g.digest(p.read_bytes());q.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(AssertionError,'projected source closure'):g.check(root)
    def test_changed_global_or_relocation_even_after_rehash(self):
        for offset,message in [(0xed572,'global bytes'),(53296,'GLOB_DAT relocation')]:
            with self.subTest(offset=offset),tempfile.TemporaryDirectory() as tmp:
                root=self.fixture(tmp);q=root/g.REL/'manifest.json';m=json.loads(q.read_text());p=root/m['elf'];raw=bytearray(p.read_bytes());raw[offset]^=1;p.write_bytes(raw);m['immutable_files'][m['elf']]=g.digest(raw);q.write_text(json.dumps(m))
                with self.assertRaisesRegex(AssertionError,message):g.check(root)
if __name__=='__main__':unittest.main()
