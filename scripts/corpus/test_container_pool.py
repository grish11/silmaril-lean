"""Failure, isolation and lifetime regressions without requiring a Docker daemon."""
from pathlib import Path
import json
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from container_pool import ContainerPool, ENV, RESET, sha


class PoolContract(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.recipes = self.root / 'recipes'
        lock = self.recipes / 'corpus/toolchain/lock.txt'
        lock.parent.mkdir(parents=True)
        lock.write_bytes(b'pkg\t1\n')
        self.hashes = {'corpus/toolchain/lock.txt': sha(lock)}
        self.pool = ContainerPool('sha256:' + 'a' * 64, self.recipes,
                                  self.root / 'cache', self.root / 'pool')

    def outputs(self, command, **kwargs):
        if command[:2] == ['docker', 'run']:
            return f'worker-{len(self.pool.containers)}\n'
        if 'dpkg-query' in command:
            return b'pkg\t1\n'
        self.fail(f'unexpected captured command {command}')

    @patch('container_pool.subprocess.run')
    @patch('container_pool.subprocess.check_output')
    def test_extended_lock_and_non_dpkg_go_tree_are_required(self, output, run):
        extension = self.recipes / 'corpus/toolchain/boringssl'
        extension.mkdir()
        (extension / 'lock.txt').write_bytes(b'pkg\t1\n')
        (extension / 'tools.json').write_bytes(b'tools')
        (extension / 'go-tree.sha256').write_bytes(b'go tree')
        self.pool.toolchain = 'corpus/toolchain/boringssl'
        def checked(command, **kwargs):
            if '/tmp/toolchain-verification/tools.json' in command:
                return b'tools'
            if '/tmp/toolchain-verification/go-tree.sha256' in command:
                return b'TAMPERED GO TREE'
            return self.outputs(command, **kwargs)
        output.side_effect = checked
        run.return_value = subprocess.CompletedProcess([], 0, '', '')
        with self.assertRaisesRegex(ValueError, 'extended tool inventory differs: go-tree'):
            self.pool.__enter__()
        self.assertEqual(run.call_args.args[0], ['docker', 'rm', '--force', 'worker-0'])

    @patch('container_pool.subprocess.run')
    @patch('container_pool.subprocess.check_output')
    def test_reconnect_reuses_only_verified_idle_workers_without_reset(self, output, run):
        output.side_effect = self.outputs
        run.return_value = subprocess.CompletedProcess([], 0, '', '')
        self.pool.__enter__()
        self.pool.prepare('current', self.hashes, {})
        for slot in range(2):
            (self.pool.output(slot) / 'keep').write_text('completed build')

        def reconnect_output(command, **kwargs):
            if command[1] == 'inspect':
                slot = int(command[2][-1])
                return json.dumps([{'State': {'Running': True}, 'Image': self.pool.image,
                    'HostConfig': {'ReadonlyRootfs': True, 'Privileged': False, 'NanoCpus': 3_000_000_000,
                        'Memory': 12 * 1024**3, 'PidsLimit': 256, 'NetworkMode': 'host',
                        'Tmpfs': {'/build': 'rw,exec,size=8g', '/tmp': 'rw,exec,size=1g', '/root': 'rw,size=64m'}},
                    'Mounts': [{'Type': 'bind', 'Destination': dest, 'Source': str(source), 'RW': rw}
                        for dest, source, rw in [('/corpus', self.recipes / 'corpus', False),
                            ('/scripts', self.recipes / 'scripts', False), ('/cache', self.pool.cache, False),
                            ('/out', self.pool.output(slot), True)]]}])
            if command[1] == 'top':
                return 'PID COMMAND\n1 sleep\n'
            return self.outputs(command, **kwargs)

        output.reset_mock(); run.reset_mock()
        output.side_effect = reconnect_output
        attached = ContainerPool.reconnect(self.pool.directory, self.recipes, self.pool.cache,
                                           self.pool.image, {'test': 'controller hash'})
        with attached:
            attached.prepare('current', self.hashes, {})
            self.assertTrue(attached.recovered)
            self.assertEqual(attached.profiles, 1)
            self.assertTrue((attached.output(0) / 'keep').exists())
            with self.assertRaisesRegex(ValueError, 'identity differs'):
                attached.prepare('different', self.hashes, {})
            attached.complete()
            self.assertFalse(attached.recovered)
        self.assertFalse(any(c.args[0][1] == 'run' for c in output.call_args_list))
        self.assertFalse(any(c.args[0][1] == 'exec' for c in run.call_args_list))

    @patch('container_pool.subprocess.run')
    @patch('container_pool.subprocess.check_output')
    def test_reconnect_refuses_busy_workers_without_removing_them(self, output, run):
        output.side_effect = self.outputs
        run.return_value = subprocess.CompletedProcess([], 0, '', '')
        self.pool.__enter__()
        self.pool.prepare('current', self.hashes, {})
        # Reject an image/limit mismatch before attempting any workspace mutation.
        output.side_effect = [json.dumps([{'State': {'Running': True}, 'Image': 'wrong', 'HostConfig': {}}])]
        run.reset_mock()
        with self.assertRaisesRegex(ValueError, 'runtime/image'):
            ContainerPool.reconnect(self.pool.directory, self.recipes, self.pool.cache, self.pool.image, {})
        run.assert_not_called()

    @patch('container_pool.subprocess.run')
    @patch('container_pool.subprocess.check_output')
    def test_fixed_two_workers_reset_and_sanitized_environment(self, output, run):
        output.side_effect = self.outputs
        run.return_value = subprocess.CompletedProcess([], 0, '', '')
        with self.pool as pool:
            first = pool.prepare('one', self.hashes, {})
            for slot in range(2):
                (pool.output(slot) / '.stale').write_text('old config')
                (pool.output(slot) / 'generated').mkdir()
                (pool.output(slot) / 'generated/result').write_text('old output')
            second = pool.prepare('two', self.hashes, {})
            self.assertFalse(first['profiles'][0]['container_reused'])
            self.assertTrue(second['profiles'][0]['container_reused'])
            for slot in range(2):
                self.assertEqual([p.name for p in pool.output(slot).iterdir()], ['repository.json'])
            with self.assertRaisesRegex(ValueError, 'environment'):
                pool.exec(0, ['true'], env={'CC': 'ccache gcc'})
        launches = [c.args[0] for c in output.call_args_list if c.args[0][1] == 'run']
        self.assertEqual(len(launches), 2)
        for slot, command in enumerate(launches):
            for token in ['--read-only', '--network', 'host', '--cpus', '3', '--memory', '12g']:
                self.assertIn(token, command)
            self.assertIn(f'{self.pool.output(slot)}:/out', command)
            self.assertNotIn(f'{self.pool.output(1-slot)}:/out', command)
        executions = [c.args[0] for c in run.call_args_list if c.args[0][1] == 'exec']
        self.assertEqual(len(executions), 4)
        for command in executions:
            self.assertEqual(command[3:5], ['env', '-i'])
            self.assertIn('JOBS=3', command)
            self.assertEqual(command[-len(RESET):], RESET)
        removals = [c.args[0] for c in run.call_args_list if c.args[0][1] == 'rm']
        self.assertEqual(len(removals), 2)

    @patch('container_pool.subprocess.run')
    @patch('container_pool.subprocess.check_output')
    def test_failed_build_finalizes_profile_and_removes_both_workers(self, output, run):
        output.side_effect = self.outputs
        run.return_value = subprocess.CompletedProcess([], 0, '', '')
        with self.assertRaisesRegex(RuntimeError, 'upstream build guard'):
            with self.pool as pool:
                pool.prepare('successful', self.hashes, {})
                pool.complete()
                pool.prepare('unsupported', self.hashes, {})
                raise RuntimeError('upstream build guard')
        record = json.loads((self.pool.directory / 'lifecycle.json').read_text())
        self.assertEqual([p['status'] for p in record['profiles']], ['passed', 'failed'])
        failed = record['profiles'][-1]
        self.assertEqual(failed['failure'], record['failure'])
        self.assertIn('finished_utc', failed)
        self.assertIn('stopped_utc', record)
        self.assertEqual([r['container_id'] for r in record['removal']], ['worker-0', 'worker-1'])
        self.assertTrue(all(r['exit_code'] == 0 for r in record['removal']))
        self.assertEqual(sum(c.args[0][:2] == ['docker', 'run'] for c in output.call_args_list), 2)

    @patch('container_pool.subprocess.run')
    @patch('container_pool.subprocess.check_output')
    def test_lock_mismatch_fails_and_removes_initialized_worker(self, output, run):
        output.side_effect = ['worker-0\n', b'pkg\twrong\n']
        run.return_value = subprocess.CompletedProcess([], 0, '', '')
        with self.assertRaisesRegex(ValueError, 'whole installed package lock differs'):
            with self.pool:
                self.fail('must not enter a mismatched image')
        self.assertEqual(run.call_args.args[0], ['docker', 'rm', '--force', 'worker-0'])
        self.assertIn('failure', (self.pool.directory / 'lifecycle.json').read_text())

    @patch('container_pool.subprocess.run')
    @patch('container_pool.subprocess.check_output')
    def test_second_initialization_failure_has_no_retry(self, output, run):
        output.side_effect = ['worker-0\n', b'pkg\t1\n',
                              subprocess.CalledProcessError(125, ['docker', 'run'])]
        run.return_value = subprocess.CompletedProcess([], 0, '', '')
        with self.assertRaises(subprocess.CalledProcessError):
            with self.pool:
                self.fail('must not continue with one worker')
        self.assertEqual(output.call_count, 3)
        self.assertEqual(run.call_args.args[0], ['docker', 'rm', '--force', 'worker-0'])

    @patch('container_pool.subprocess.run')
    @patch('container_pool.subprocess.check_output')
    def test_changed_frozen_recipe_stops_before_reset(self, output, run):
        output.side_effect = self.outputs
        run.return_value = subprocess.CompletedProcess([], 0, '', '')
        with self.pool:
            (self.recipes / 'corpus/toolchain/lock.txt').write_bytes(b'changed')
            with self.assertRaisesRegex(ValueError, 'frozen recipe changed'):
                self.pool.prepare('bad', self.hashes, {})
        self.assertFalse(any(c.args[0][1] == 'exec' for c in run.call_args_list))


if __name__ == '__main__':
    unittest.main()
