"""Release identity and supported upstream embedding-plan checks."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import tempfile
import tomllib
import unittest
from variants import parse_profile, profile_axes
import argparse
from unittest.mock import patch
import variants

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('boringssl_configure', ROOT / 'corpus/boringssl/configure.py')
embed = importlib.util.module_from_spec(spec)
spec.loader.exec_module(embed)


class Profiles(unittest.TestCase):
    def test_explicit_profile_identity_and_axes(self):
        profiles = [parse_profile(p) for p in ['asm:aarch64:O2', 'fips-shared:aarch64:O0']]
        self.assertEqual(profiles, [('asm', 'aarch64', 'O2'), ('fips-shared', 'aarch64', 'O0')])
        self.assertEqual(profile_axes('boringssl', profiles), (['aarch64'], ['asm', 'fips-shared'], ['O2', 'O0']))
        with self.assertRaisesRegex(ValueError, 'unsupported'):
            profile_axes('sqlite', profiles)
        for value in ['asm:aarch64:Ofast', 'asm:other:O2', 'asm:aarch64', 'asm:aarch64:O2:extra']:
            with self.assertRaises(argparse.ArgumentTypeError):
                parse_profile(value)

    def test_invalid_profile_combinations_rejected_before_docker(self):
        for args in [['--package', 'boringssl', '--profile', 'asm:aarch64:O2', '--level', 'O0'],
                     ['--package', 'sqlite', '--profile', 'asm:aarch64:O2'],
                     ['--profile', 'default:x86_64:O0'],
                     ['--package', 'boringssl', '--profile', 'asm:aarch64:O9']]:
            result = subprocess.run(['python3', 'scripts/corpus/variants.py', *args, '--work', '/unused'],
                                    cwd=ROOT, capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
            self.assertNotIn('Traceback', result.stderr)

    def test_exact_profiles_do_not_execute_cartesian_cross_terms(self):
        # All four destinations exist. Only the two requested tuples may even be
        # retained; an accidental Cartesian expansion would print four rows.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            package = root / 'corpus/boringssl'
            package.mkdir(parents=True)
            (package / 'package.toml').write_text('version = "pin"\nobject = []\n')
            (root / 'scripts/corpus').mkdir(parents=True)
            for config in ['asm', 'fips-shared']:
                for level in ['O0', 'O2']:
                    dest = root / 'corpus/variants/boringssl/pin' / config / 'aarch64' / level
                    dest.mkdir(parents=True)
                    (dest / 'build.json').write_text(json.dumps({'project': 'boringssl', 'version': 'pin',
                        'optimization': level, 'target': 'aarch64-linux-gnu', 'configuration': config,
                        'included_source_files': []}))
                    for form in ['unstripped', 'stripped']:
                        (dest / form).mkdir()
                        (dest / form / 'receipt.json').write_text('{"reproducible": true, "outputs": []}')
            args = ['variants.py', '--package', 'boringssl', '--profile', 'asm:aarch64:O2',
                    '--profile', 'fips-shared:aarch64:O0', '--resume', '--work', str(root / 'work')]
            with patch.object(variants, 'ROOT', root), patch('sys.argv', args), \
                 patch.dict(os.environ, {'CORPUS_CACHE': str(root / 'cache')}), \
                 patch.object(variants.os, 'chdir'), patch.object(variants.signal, 'signal'), \
                 patch.object(variants.subprocess, 'check_output', return_value=''), \
                 patch.object(variants.subprocess, 'run') as fetch, \
                 patch.object(variants, 'ContainerPool') as pool, patch('builtins.print') as output:
                variants.main()
                pool.assert_called_once()
                pool.return_value.__enter__.return_value.prepare.assert_not_called()
                fetch.assert_called_once()
                retained = [call.args[0].split(': existing')[0] for call in output.call_args_list]
                self.assertEqual(retained, ['retained corpus/variants/boringssl/pin/asm/aarch64/O2',
                                            'retained corpus/variants/boringssl/pin/fips-shared/aarch64/O0'])

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
