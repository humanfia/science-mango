import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('rootless', ROOT / 'scripts/run_answer_blind_rootless_campaign.py')
LAUNCHER = importlib.util.module_from_spec(spec)
spec.loader.exec_module(LAUNCHER)


class RootlessTests(unittest.TestCase):
    def args(self, base, bwrap='bwrap'):
        for folder in ('runtime', 'campaign', 'seed', 'packages', 'home', 'toolchain/bin'):
            (base / folder).mkdir(parents=True, exist_ok=True)
        return SimpleNamespace(runtime=base/'runtime', campaign=base/'campaign',
                               seed=base/'seed', packages=base/'packages', private_home=base/'home',
                               lean_bin=base/'toolchain/bin', python=Path('/usr/bin/python3'),
                               codex=Path('/usr/bin/true'), bwrap=Path(bwrap))

    def test_model_command_preserves_native_review_and_parallelism(self):
        with tempfile.TemporaryDirectory() as directory:
            args = self.args(Path(directory))
            command = LAUNCHER.native_command(args, resume=True)
            self.assertIn('--resume', command)
            self.assertIn('--target-lifecycle', command)
            self.assertEqual(command[command.index('--max-parallel')+1], '32')
            self.assertEqual(command[command.index('--expected-items')+1], '68')

    def test_namespace_mount_allowlist_and_no_host_env(self):
        with tempfile.TemporaryDirectory() as directory:
            args = self.args(Path(directory))
            command = LAUNCHER.namespace(args, ['true'])
            self.assertIn('--clearenv', command)
            self.assertIn('--unshare-pid', command)
            self.assertNotIn(str(Path.home()), command)
            self.assertNotIn(str(ROOT), command)
            self.assertNotIn('--share-net', command)
            self.assertNotIn('--unshare-net', command)  # do not claim network isolation

    def test_codex_companion_is_mounted_next_to_cli(self):
        with tempfile.TemporaryDirectory() as directory:
            args = self.args(Path(directory))
            args.codex = args.runtime / 'codex'
            companion = args.runtime / 'codex-code-mode-host'
            companion.touch()
            command = LAUNCHER.namespace(args, ['true'])
            offset = command.index(str(companion))
            self.assertEqual(command[offset-1:offset+2],
                             ['--ro-bind', str(companion), '/tools/codex-code-mode-host'])

    def test_supervisor_creates_policy_and_marks_abnormal_exit_failed(self):
        with tempfile.TemporaryDirectory() as directory:
            args = self.args(Path(directory))
            args.source = Path(directory) / 'source'
            workspace = args.campaign / 'workspace'
            (workspace / '.archon').mkdir(parents=True)
            (workspace / '.archon/config.json').write_text(json.dumps({'loop': {}}))
            (args.campaign / 'campaign.json').write_text(json.dumps({'status': 'running'}))
            child = Mock(pid=12345)
            child.wait.return_value = -15
            with patch.object(LAUNCHER, 'namespace', return_value=['mock-namespace']), \
                 patch.object(LAUNCHER.subprocess, 'run'), \
                 patch.object(LAUNCHER.subprocess, 'Popen', return_value=child):
                self.assertEqual(LAUNCHER.supervise(args), -15)
            self.assertIn('Rootless full-theory derivation policy',
                          (workspace / 'AGENTS.md').read_text())
            status = json.loads((args.campaign.parent / 'campaign.rootless.json').read_text())
            self.assertEqual(status['status'], 'failed')
            self.assertEqual(status['returncode'], -15)

    @unittest.skipUnless(shutil.which('bwrap'), 'bwrap not installed on PATH')
    def test_real_namespace_hides_host_sentinel_and_protects_inputs(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            args = self.args(base, shutil.which('bwrap'))
            sentinel = base/'host-secret'
            sentinel.write_text('must never be visible')
            (args.seed/'problem.txt').write_text('problem only')
            command = ['sh', '-c', 'test ! -e "$1" && test -r "$2" && ! touch "$3"',
                       'probe', str(sentinel), str(args.seed/'problem.txt'), str(args.seed/'forbidden')]
            result = subprocess.run(LAUNCHER.namespace(args, command), capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertFalse((args.seed/'forbidden').exists())


if __name__ == '__main__':
    unittest.main()
