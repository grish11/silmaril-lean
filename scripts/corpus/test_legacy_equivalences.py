"""Audit the six original actual ELF contracts; no builds or semantic claims."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('equivalence',ROOT/'tools/compiler-explorer/equivalence.py')
e=importlib.util.module_from_spec(spec);spec.loader.exec_module(e)

class LegacyBindings(unittest.TestCase):
    def setUp(self):
        self.manifest=json.loads((ROOT/'corpus/legacy/equivalence/manifest.json').read_text())
        self.endpoints={x['id']:x for x in self.manifest['endpoints']}
    def test_actual_original_six_contracts_and_real_bytes(self):
        self.assertEqual(len(self.manifest['pairs']),6)
        for p in self.manifest['pairs']:
            left,right=[self.endpoints[p[k]] for k in ['left','right']]
            e.validate_pair(p,left,right)
            for endpoint in [left,right]:
                f=endpoint['functions'][p['function_symbol']]
                actual=e.c.elf_function((ROOT/endpoint['path']).read_bytes(),p['function_symbol'],f['address'])
                self.assertEqual(actual,f)
            if p['function_symbol']=='isid':
                self.assertEqual([left['functions']['isid']['address'],right['functions']['isid']['address']],[0x7508,0x5e05])
                self.assertNotEqual(left['functions']['isid']['bytes_hex'],right['functions']['isid']['bytes_hex'])
                self.assertEqual([p['left_frame'],p['right_frame']],[16,16])
                self.assertIsNone(p['value'])
            else:
                self.assertEqual(p['value'],219)
                self.assertEqual([p['left_frame'],p['right_frame']],[8,8])
    def test_identity_compatibility_and_original_frame_negatives(self):
        for p in self.manifest['pairs']:
            left,right=[self.endpoints[p[k]] for k in ['left','right']]
            for key in ['configuration','version','project','target','source_inputs']:
                wrong=copy.deepcopy(right);wrong['build'][key]='different'
                with self.assertRaisesRegex(ValueError,'incompatible legacy'):e.validate_pair(p,left,wrong)
            wrong=copy.deepcopy(right);wrong['source']['sha256']='0'*64
            with self.assertRaisesRegex(ValueError,'included source'):e.validate_pair(p,left,wrong)
            wrong=copy.deepcopy(p);wrong['right_frame']=0
            with self.assertRaisesRegex(ValueError,'original legacy contract frame'):e.validate_pair(wrong,left,right)
            wrong=copy.deepcopy(p);wrong['value']=999
            with self.assertRaisesRegex(ValueError,'contract meaning'):e.validate_pair(wrong,left,right)
    def test_tinycc_duplicate_symbol_requires_selected_address(self):
        endpoint=self.endpoints['tinyccO0unstripped']
        with self.assertRaises(ValueError):e.c.elf_function((ROOT/endpoint['path']).read_bytes(),'isid')
        self.assertEqual(e.c.elf_function((ROOT/endpoint['path']).read_bytes(),'isid',0x7508)['size'],51)

if __name__=='__main__':unittest.main()
