"""HTTP representation and mutation regressions for the Pages-shaped server."""
import gzip
import http.client
import os
from pathlib import Path
import socket
import subprocess
import sys
import tempfile
import time
import unittest


class PagesServerTest(unittest.TestCase):
    def test_gzip_head_get_range_and_preserved_mtime_write(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            file = root / 'project.sqlite'
            first = b'first public test data' * 256
            file.write_bytes(first)
            with socket.socket() as reservation:
                reservation.bind(('127.0.0.1', 0))
                port = reservation.getsockname()[1]
            process = subprocess.Popen([
                sys.executable, '-I', str(Path(__file__).with_name('pages_server.py')),
                '--root', tmp, '--port', str(port), '--log', str(root / 'requests.jsonl'),
            ], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            try:
                for _ in range(100):
                    try:
                        with socket.create_connection(('127.0.0.1', port), timeout=.1):
                            break
                    except OSError:
                        if process.poll() is not None:
                            self.fail('server exited before readiness')
                        time.sleep(.01)
                def request(method, headers):
                    connection = http.client.HTTPConnection('127.0.0.1', port, timeout=5)
                    try:
                        connection.request(method, '/project.sqlite', headers=headers)
                        response = connection.getresponse()
                        return response.status, dict(response.getheaders()), response.read()
                    finally:
                        connection.close()
                for _ in range(2):
                    status, head, body = request('HEAD', {'Accept-Encoding': 'gzip'})
                    self.assertEqual(status, 200)
                    self.assertEqual(body, b'')
                    status, get, body = request('GET', {'Accept-Encoding': 'gzip'})
                    self.assertEqual(status, 200)
                    self.assertEqual(get['Content-Encoding'], 'gzip')
                    self.assertEqual(head['Content-Length'], str(len(body)))
                    self.assertEqual(head['ETag'], get['ETag'])
                    self.assertTrue(get['ETag'].startswith('W/'))
                    self.assertEqual(gzip.decompress(body), first)
                status, headers, body = request('GET', {'Accept-Encoding': 'gzip', 'Range': 'bytes=7-19'})
                self.assertEqual(status, 206)
                self.assertNotIn('Content-Encoding', headers)
                self.assertFalse(headers['ETag'].startswith('W/'))
                self.assertEqual(headers['Content-Range'], f'bytes 7-19/{len(first)}')
                self.assertEqual(body, first[7:20])
                prior = file.stat()
                second = b'other public test data' * 256
                self.assertEqual(len(first), len(second))
                file.write_bytes(second)
                os.utime(file, ns=(prior.st_atime_ns, prior.st_mtime_ns))
                status, headers, body = request('GET', {'Accept-Encoding': 'gzip'})
                self.assertEqual(status, 200)
                self.assertEqual(gzip.decompress(body), second)
                status, headers, body = request('GET', {'Range': 'bytes=0-15'})
                self.assertEqual(status, 206)
                self.assertEqual(body, second[:16])
            finally:
                process.terminate()
                process.wait(timeout=5)


if __name__ == '__main__':
    unittest.main()
