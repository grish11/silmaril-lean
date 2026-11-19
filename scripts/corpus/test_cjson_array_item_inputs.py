import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('cjson_array_item_inputs', ROOT / 'tools/corpus/check_cjson_array_item_inputs.py')
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)
DATA = Path('corpus/cjson/semantic-inputs/linux-x86_64/get-array-item')


class CjsonArrayItemInputTest(unittest.TestCase):
    def fixture(self, root):
        manifest = json.loads((ROOT / DATA / 'manifest.json').read_text())
        paths = [DATA / 'manifest.json', Path('Silmaril/Elf/Corpus/CjsonArrayItem/Source/Defs.lean')]
        paths += [DATA / p for p in manifest['files']]
        paths += [Path(p) for p in manifest['immutable_files']]
        for path in paths:
            (root / path).parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / path, root / path)

    def test_public_inputs(self):
        GATE.check(ROOT)

    def test_modified_tu_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            projection = json.loads((root / DATA / 'projection.json').read_text())
            tu = root / projection['tu']
            tu.write_bytes(tu.read_bytes() + b'\n')
            with self.assertRaises(AssertionError):
                GATE.check(root)

    def test_forged_span_rejected_after_receipt_rehash(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            path = root / DATA / 'projection.json'
            projection = json.loads(path.read_text())
            projection['spans'][-1]['offset'] += 1
            tu = (root / projection['tu']).read_bytes()
            span = projection['spans'][-1]
            span['sha256'] = hashlib.sha256(tu[span['offset']:span['offset'] + span['length']]).hexdigest()
            path.write_text(json.dumps(projection))
            manifest_path = root / DATA / 'manifest.json'
            manifest = json.loads(manifest_path.read_text())
            manifest['files']['projection.json'] = hashlib.sha256(path.read_bytes()).hexdigest()
            manifest_path.write_text(json.dumps(manifest))
            with self.assertRaisesRegex(AssertionError, 'projected source closure'):
                GATE.check(root)

    def test_stale_literal_marker_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            self.fixture(root)
            source = root / 'Silmaril/Elf/Corpus/CjsonArrayItem/Source/Defs.lean'
            source.write_text(source.read_text().replace('def externalInputSha256', 'def staleInputSha256'))
            with self.assertRaisesRegex(AssertionError, 'stale literal marker'):
                GATE.check(root)
