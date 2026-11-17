"""Assembly input provenance preserves actual bytes without overclaiming invocation."""
import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('openssl_assembly', ROOT / 'corpus/openssl/assembly-inputs.py')
assembly = importlib.util.module_from_spec(spec)
spec.loader.exec_module(assembly)


class OpenSSLAssembly(unittest.TestCase):
    def test_preserved_generators_and_assembly_have_distinct_evidence(self):
        with tempfile.TemporaryDirectory() as tmp:
            root, pristine = Path(tmp) / 'build', Path(tmp) / 'pristine'
            root.mkdir(); pristine.mkdir()
            for name, text in [('unused.pl', '# available, never invoked'), ('gen.pl', '# generator'),
                               ('original.S', 'upstream assembly'), ('generated.s', 'generated assembly')]:
                (root / name).write_text(text)
            (pristine / 'original.S').write_text('upstream assembly')
            (root / 'make-libs.log').write_text('perl gen.pl elf > generated.s\ncc -c generated.s\n')
            (root / 'make-apps.log').write_text('')
            with patch.object(assembly, 'version', return_value='pinned test version'):
                paths, result = assembly.inventory(root, pristine, 'x86_64')
            self.assertEqual({p.name for p in paths}, {'unused.pl', 'gen.pl', 'original.S', 'generated.s'})
            self.assertEqual({p['path']: p['origin'] for p in result['available_standalone_assembly']},
                             {'generated.s': 'generated-or-modified', 'original.S': 'upstream'})
            self.assertEqual([c['command'] for c in result['recorded_generator_commands']], ['perl gen.pl elf > generated.s'])
            self.assertEqual({p['path'] for p in result['available_generator_inputs']}, {'gen.pl', 'unused.pl'})
            (root / 'generated.s').write_text('changed actual bytes')
            with patch.object(assembly, 'version', return_value='pinned test version'):
                _, changed = assembly.inventory(root, pristine, 'x86_64')
            self.assertNotEqual(result['available_standalone_assembly'][0]['sha256'], changed['available_standalone_assembly'][0]['sha256'])

    def test_pristine_tree_and_target_required(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            with self.assertRaisesRegex(ValueError, 'pristine'):
                assembly.inventory(root, root / 'missing', 'x86_64')
            with self.assertRaisesRegex(ValueError, 'target'):
                assembly.inventory(root, root, 'arm32')

    def test_configuration_rejected_before_docker_for_other_packages(self):
        run = subprocess.run([sys.executable, str(ROOT / 'scripts/corpus/variants.py'), '--package', 'sqlite',
                              '--configuration', 'asm', '--work', '/unused'], capture_output=True, text=True)
        self.assertEqual(run.returncode, 2)
        self.assertIn('requires exactly --package openssl', run.stderr)


if __name__ == '__main__':
    unittest.main()
