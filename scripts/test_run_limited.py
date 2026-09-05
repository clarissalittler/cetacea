import importlib.util
import json
from pathlib import Path
import sys
import time
import unittest

spec = importlib.util.spec_from_file_location('run_limited', Path(__file__).with_name('run_limited.py'))
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class LimitedCheckerTests(unittest.TestCase):
    def run_python(self, source, **limits):
        return runner.run_limited([sys.executable, '-c', source], **limits)

    def test_normal_results_preserve_streams_and_rejection_code(self):
        code, out, err = self.run_python("import sys; print('result'); print('diagnostic', file=sys.stderr); sys.exit(1)")
        self.assertEqual((code, out, err), (1, b'result\n', b'diagnostic\n'))

    def test_timeout_does_not_return_partial_certification(self):
        start = time.monotonic()
        code, out, err = self.run_python("import time; print('{\"ok\":true}', flush=True); time.sleep(10)", seconds=0.15)
        self.assertEqual(code, 124)
        self.assertFalse(json.loads(out)['ok'])
        self.assertEqual(json.loads(out)['resource_limit']['kind'], 'time')
        self.assertLess(time.monotonic() - start, 3)

    def test_combined_output_is_bounded_without_pipe_deadlock(self):
        code, out, err = self.run_python("import os\nwhile True:\n os.write(1,b'x'*65536)\n os.write(2,b'x'*65536)", output_mib=0.1)
        self.assertEqual(code, 125)
        self.assertEqual(json.loads(out)['resource_limit']['kind'], 'output')

    def test_descendant_holding_output_open_is_stopped_at_deadline(self):
        start = time.monotonic()
        code, out, err = self.run_python("import subprocess, sys; subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(10)'])", seconds=0.15)
        self.assertEqual(code, 124)
        self.assertLess(time.monotonic() - start, 3)

    def test_nonfinite_limits_are_rejected(self):
        for seconds in [float('inf'), float('nan'), 0, -1]:
            with self.assertRaises(ValueError): self.run_python('pass', seconds=seconds)

    def test_memory_limit_prevents_excessive_allocation(self):
        code, out, err = self.run_python("try:\n value = bytearray(256 * 1024 * 1024)\n print('unbounded')\nexcept MemoryError:\n print('bounded')", memory_mib=128)
        self.assertEqual(code, 0)
        self.assertEqual(out, b'bounded\n')


if __name__ == '__main__':
    unittest.main()
