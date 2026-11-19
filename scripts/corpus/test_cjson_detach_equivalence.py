"""Real loop-pair identity/domain/receipt rejection, with no artifact builds."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('array_binary', ROOT/'tools/compiler-explorer/equivalence.py')
e = importlib.util.module_from_spec(spec)
spec.loader.exec_module(e)

class InteriorDetachEquivalence(unittest.TestCase):
    def setUp(self):
        self.manifest = json.loads((ROOT/e.MANIFESTS[2]).read_text())
        self.pair = self.manifest['pairs'][0]
        self.left,self.right = self.manifest['endpoints']

    def test_real_different_mutation_bytes_and_actual_receipts(self):
        e.validate_pair(self.pair,self.left,self.right)
        for endpoint in [self.left,self.right]:
            e.validate_cjson_build(ROOT,endpoint)
            actual=e.c.elf_function((ROOT/endpoint['path']).read_bytes(),'cJSON_DetachItemViaPointer')
            self.assertEqual(actual,endpoint['functions']['cJSON_DetachItemViaPointer'])
        self.assertNotEqual(self.left['functions'],self.right['functions'])
        self.assertIsNone(self.pair['value'])

    def test_incompatible_sources_versions_configs_and_target_are_rejected(self):
        for key,value in [('source_sha256','0'*64),('version','1.7.18'),('configuration','other'),('target','aarch64-linux-gnu')]:
            right=copy.deepcopy(self.right);right['build'][key]=value
            with self.assertRaisesRegex(ValueError,'incompatible detachment'):
                e.validate_pair(self.pair,self.left,right)

    def test_frame_domain_and_desired_result_are_not_relaxed(self):
        for key,value in [('left_frame',128),('right_frame',32),('object_count',6),('value',64)]:
            pair=copy.deepcopy(self.pair);pair[key]=value
            with self.assertRaises(ValueError):e.validate_pair(pair,self.left,self.right)

    def test_display_build_fields_must_match_actual_receipts(self):
        for key,value in [('cflags','-O0'),('compiler','invented'),('configure_args','invented'),('image_id','sha256:'+'0'*64),('source_inputs',[])]:
            endpoint=copy.deepcopy(self.right);endpoint['build'][key]=value
            with self.assertRaises(ValueError):e.validate_cjson_build(ROOT,endpoint)

if __name__=='__main__':unittest.main()
