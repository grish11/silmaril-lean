"""Real source/TU/Core pin checking and stale-input rejection; no builds."""
import importlib.util
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('darkhttpd_inputs',ROOT/'tools/corpus/check_darkhttpd_logencoding_inputs.py')
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)

class DarkhttpdLogEncodingInputs(unittest.TestCase):
    def test_actual_public_inputs(self):c.main()
    def test_changed_tu_and_literal_marker_are_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            data=Path(tmp)/'inputs';shutil.copytree(c.DATA,data)
            with (data/'translation-unit.i').open('ab') as f:f.write(b'\nchanged')
            with patch.object(c,'DATA',data),self.assertRaises(AssertionError):c.main()
        with patch.object(c,'digest',return_value='0'*64),self.assertRaisesRegex(AssertionError,'stale external literals'):c.main()
if __name__=='__main__':unittest.main()
