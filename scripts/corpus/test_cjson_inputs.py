"""External literal changes must invalidate Lean input identity, without resealing ELF bytes."""
import hashlib
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import json

ROOT = Path(__file__).resolve().parents[2]


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'tools/corpus' / (name + '.py'))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class CjsonInputs(unittest.TestCase):
    def test_changed_literal_rejected_before_any_build(self):
        check = load('check_cjson_predicate_inputs')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            data = root / 'inputs'
            data.mkdir()
            for name in ['context.c', 'typed-ail.sexp', 'program.sexp', 'runtime.sexp']:
                (data / name).write_bytes(b'changed literal')
            source = root / 'Silmaril/Elf/Corpus/CjsonTypePredicates/Source/Defs.lean'
            source.parent.mkdir(parents=True)
            source.write_text('def externalInputSha256 : String := "' + '0' * 64 + '"')
            with patch.object(check, 'ROOT', root), patch.object(check, 'DATA', data):
                with self.assertRaisesRegex(AssertionError, 'external literals changed'):
                    check.main()

    def test_sealer_cannot_change_upstream_or_elf_pin(self):
        seal = load('seal_cjson_inputs')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            data = root / 'inputs'
            data.mkdir()
            artifact = root / 'canonical.so'
            artifact.write_bytes(b'changed canonical bytes')
            old = hashlib.sha256(b'original canonical bytes').hexdigest()
            manifest = data / 'manifest.json'
            original = json.dumps({'files': [{'path': 'canonical.so', 'sha256': old}]})
            manifest.write_text(original)
            with patch.object(seal, 'ROOT', root), patch.object(seal, 'DATA', data):
                with self.assertRaisesRegex(SystemExit, 'refusing to change non-generated pin'):
                    seal.main()
            self.assertEqual(manifest.read_text(), original)


if __name__ == '__main__':
    unittest.main()
