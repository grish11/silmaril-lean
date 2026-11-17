"""Bounds and stripped-pair evidence regressions."""
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from variant_pair import executable_sections
from gen_variants import module_parts

ROOT = Path(__file__).resolve().parents[2]


class VariantContracts(unittest.TestCase):
    def test_executable_project_namespace_collision(self):
        parts = module_parts({'path': 'corpus/variants/darkhttpd/1.17/default/x86_64/O0/stripped/darkhttpd'})
        self.assertEqual(parts[-1], 'DarkhttpdBinary')
        self.assertEqual(len(parts), len(set(parts)))
        unchanged = module_parts({'path': 'corpus/variants/mimalloc/2.1.9/default/x86_64/O0/stripped/libmimalloc.so.2.1'})
        self.assertEqual(unchanged[-1], 'LibmimallocSo21')

    def test_resource_and_flag_guards(self):
        script = '. corpus/common.sh; printf "%s %s" "$JOBS" "$CORPUS_OPT_LEVEL"'
        for jobs, level, expected in [('8', 'O0', 0), ('1', 'Og', 0), ('9', 'O2', 2), ('0', 'O2', 2), ('8', 'fast', 2)]:
            result = subprocess.run(['bash', '-c', script], cwd=ROOT,
                                    env={**os.environ, 'JOBS': jobs, 'CORPUS_OPT_LEVEL': level}, capture_output=True)
            self.assertEqual(result.returncode, expected)

    def test_changed_executable_bytes_detected(self):
        original = ROOT / 'corpus/elf/cjson/x86_64/libcjson.so.1'
        sections = executable_sections(original, 'readelf')
        self.assertIn('.text', sections)
        # Find the actual .text file range using the ELF section headers.
        import re
        headers = subprocess.check_output(['readelf', '-SW', str(original)], text=True)
        line = next(l for l in headers.splitlines() if re.search(r'\]\s+\.text\s', l))
        fields = line.split(']', 1)[1].split()
        offset = int(fields[3], 16)
        with tempfile.TemporaryDirectory() as tmp:
            changed = Path(tmp) / 'changed.so'
            data = bytearray(original.read_bytes())
            data[offset] ^= 1
            changed.write_bytes(data)
            self.assertNotEqual(sections, executable_sections(changed, 'readelf'))


if __name__ == '__main__':
    unittest.main()
