"""Release identity and supported upstream embedding-plan checks."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import tomllib
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('boringssl_configure', ROOT / 'corpus/boringssl/configure.py')
embed = importlib.util.module_from_spec(spec)
spec.loader.exec_module(embed)


class Profiles(unittest.TestCase):
    def test_profile_recipes_are_valid_shell(self):
        for package in ['sqlite', 'boringssl']:
            for name in ['build.sh', 'test.sh', 'fetch.sh']:
                result = subprocess.run(['bash', '-n', str(ROOT / 'corpus' / package / name)],
                                        capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)

    def test_distinct_sqlite_upstream_versions_and_exact_sources(self):
        releases = tomllib.loads((ROOT / 'corpus/sqlite/releases.toml').read_text())
        self.assertEqual(len({r['sha256'] for r in releases.values()}), len(releases))
        for version, release in releases.items():
            result = subprocess.check_output(['python3', '-I', 'corpus/sqlite/release.py'],
                cwd=ROOT, env={**os.environ, 'CORPUS_SQLITE_VERSION': version}, text=True).splitlines()
            self.assertEqual(result, [version, release['root'], release['sha256'], release['url']])
        result = subprocess.run(['python3', '-I', 'corpus/sqlite/release.py'], cwd=ROOT,
            env={**os.environ, 'CORPUS_SQLITE_VERSION': '../../other'}, capture_output=True)
        self.assertNotEqual(result.returncode, 0)

    def test_unknown_version_rejected_before_docker(self):
        result = subprocess.run(['python3', 'scripts/corpus/variants.py', '--package', 'sqlite',
            '--version', '9.99.9', '--work', '/unused'], cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn('pinned release', result.stderr)

    def test_upstream_cmake_configuration_and_release_flags(self):
        for config in ['asm', 'no-asm', 'fips-shared']:
            args = embed.command('aarch64-linux-gnu-', '-O2 -g0', config)
            self.assertIn('-DBUILD_SHARED_LIBS=ON', args)
            self.assertIn('-DBUILD_TESTING=OFF', args)
            self.assertIn('-DFIPS=' + ('ON' if config == 'fips-shared' else 'OFF'), args)
            self.assertIn('-DOPENSSL_NO_ASM=' + ('ON' if config == 'no-asm' else 'OFF'), args)
            self.assertIn('-DCMAKE_SYSTEM_PROCESSOR=aarch64', args)
            self.assertIn('-DCMAKE_C_COMPILER=aarch64-linux-gnu-gcc', args)
            for language in ['C', 'CXX', 'ASM']:
                self.assertIn(f'-DCMAKE_{language}_FLAGS=-O2 -g0', args)
                self.assertIn(f'-DCMAKE_{language}_FLAGS_RELEASE=-g0 -DNDEBUG', args)
        with self.assertRaisesRegex(ValueError, 'unsupported'):
            embed.command('', '-O2', 'fabricated')

    def test_compiler_and_ninja_inputs_include_transitive_headers(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            build = root / 'build'; build.mkdir()
            (build / 'crypto.o').write_bytes(b'compiled')
            (build / 'compile_commands.json').write_text(json.dumps([
                {'directory': str(build), 'file': '../crypto.cc', 'output': 'crypto.o'},
                {'directory': str(build), 'file': '../unbuilt.cc', 'output': 'unbuilt.o'}]))
            (build / 'ninja-deps.txt').write_text('crypto.o: #deps 1\n    ../nested.h\n')
            selected = {p.resolve() for p in embed.inputs(root)}
            self.assertIn(root / 'crypto.cc', selected)
            self.assertNotIn(root / 'unbuilt.cc', selected)
            self.assertIn(root / 'nested.h', selected)
            self.assertIn(build / 'build.ninja', selected)


if __name__ == '__main__':
    unittest.main()
