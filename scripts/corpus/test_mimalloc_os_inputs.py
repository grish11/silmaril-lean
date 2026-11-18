"""Reject stale compiled-literal identity and altered canonical artifact bytes."""
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]


class MimallocOsInputs(unittest.TestCase):
    def test_stale_identity_and_changed_elf_rejected(self):
        spec = importlib.util.spec_from_file_location('os_inputs', ROOT / 'tools/corpus/check_mimalloc_os_inputs.py')
        checker = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(checker)
        for mutation in ['literal', 'elf']:
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                data = root / 'inputs'
                shutil.copytree(checker.DATA, data)
                manifest = json.loads((data / 'manifest.json').read_text())
                for path in manifest['immutable_files']:
                    destination = root / path
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(ROOT / path, destination)
                source = Path('Silmaril/Elf/Corpus/MimallocOsGlobals/Source/Defs.lean')
                (root / source).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / source, root / source)
                if mutation == 'literal':
                    literal = data / 'context.c'
                    literal.write_bytes(literal.read_bytes() + b'\n')
                    manifest['files']['context.c'] = hashlib.sha256(literal.read_bytes()).hexdigest()
                    (data / 'manifest.json').write_text(json.dumps(manifest))
                    message = 'stale external literals'
                else:
                    (root / 'corpus/elf/mimalloc/x86_64/libmimalloc.so.2.1').write_bytes(b'changed ELF')
                    message = 'corpus/elf/mimalloc'
                with patch.object(checker, 'ROOT', root), patch.object(checker, 'DATA', data):
                    with self.assertRaisesRegex(AssertionError, message):
                        checker.main()


if __name__ == '__main__':
    unittest.main()
