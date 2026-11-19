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


class SqliteBuildQueryInputs(unittest.TestCase):
    def test_stale_identity_and_changed_elf_rejected(self):
        spec = importlib.util.spec_from_file_location('os_inputs', ROOT / 'tools/corpus/check_sqlite_build_query_inputs.py')
        checker = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(checker)
        for mutation in ['baseline', 'literal', 'elf', 'tu']:
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                data = root / 'inputs'
                shutil.copytree(checker.DATA, data)
                manifest = json.loads((data / 'manifest.json').read_text())
                for path in manifest['immutable_files']:
                    destination = root / path
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(ROOT / path, destination)
                source = Path('Silmaril/Elf/Corpus/SqliteBuildQueries/Source/Defs.lean')
                (root / source).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / source, root / source)
                if mutation == 'literal':
                    literal = data / 'context.c'
                    literal.write_bytes(literal.read_bytes() + b'\n')
                    manifest['files']['context.c'] = hashlib.sha256(literal.read_bytes()).hexdigest()
                    (data / 'manifest.json').write_text(json.dumps(manifest))
                    message = 'stale external literals'
                elif mutation == 'elf':
                    (root / 'corpus/elf/sqlite/x86_64/libsqlite3.so').write_bytes(b'changed ELF')
                    message = 'corpus/elf/sqlite'
                elif mutation == 'tu':
                    (data / 'translation-unit.i').write_bytes(b'changed saved translation unit')
                    message = ''
                with patch.object(checker, 'ROOT', root), patch.object(checker, 'DATA', data):
                    if mutation == 'baseline':
                        checker.main()
                    else:
                        with self.assertRaisesRegex(AssertionError, message):
                            checker.main()


if __name__ == '__main__':
    unittest.main()
