"""Check the portable launch boundary without any model calls."""
from contextlib import redirect_stderr
import io
from pathlib import Path
import runpy
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
LAUNCHER = ROOT / 'scripts' / 'run_quantum_harness.py'


class ResearchLauncherTests(unittest.TestCase):
    def invoke(self, args):
        with patch('sys.argv', [str(LAUNCHER), *args]):
            return runpy.run_path(str(LAUNCHER))['main']()

    def test_prepare_freezes_the_research_checkout_not_the_harness_checkout(self):
        with tempfile.TemporaryDirectory(prefix='quantum research ') as tmp:
            repo = Path(tmp)
            for name in ['docs', 'scripts', 'tests', 'evidence', 'data']:
                (repo / name).mkdir()
            (repo / 'docs' / 'external-scope.md').write_text('scope')
            (repo / 'tests' / 'external_baseline.py').write_text('# baseline')
            with patch('subprocess.call', return_value=0) as call:
                self.assertEqual(self.invoke(['--repo', tmp, '--prepare']), 0)
            cmd = call.call_args.args[0]
            self.assertEqual(cmd[cmd.index('--repo') + 1], str(repo.resolve()))
            self.assertIn('docs/external-scope.md', cmd)
            self.assertIn('tests/external_baseline.py', cmd)
            self.assertIn('--checks', cmd)
            self.assertNotIn('--live', cmd)
            self.assertEqual(call.call_args.kwargs['cwd'], ROOT)

    def test_audit_seed_is_forwarded_without_starting_live_turns_by_default(self):
        with tempfile.TemporaryDirectory() as tmp:
            for name in ['docs', 'scripts', 'tests', 'evidence', 'data']:
                (Path(tmp) / name).mkdir()
            seed = '.humanize-quantum-runs/controller/audit.json'
            with patch('subprocess.call', return_value=0) as call:
                self.invoke(['--repo', tmp, '--audit-input', seed, '--audit-only'])
            cmd = call.call_args.args[0]
            self.assertEqual(cmd[cmd.index('--audit-input') + 1], seed)
            self.assertIn('--no-integrate', cmd)
            self.assertNotIn('--live', cmd)

    def test_prepare_and_live_cannot_be_combined(self):
        with patch('subprocess.call') as call, redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit) as error:
                self.invoke(['--repo', str(ROOT), '--prepare', '--live'])
            self.assertEqual(error.exception.code, 2)
            call.assert_not_called()
