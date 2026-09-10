"""Non-root tests of the expanded problem-only scope and campaign binding."""
import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def module(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / f'{name}.py')
    result = importlib.util.module_from_spec(spec)
    sys.modules[name] = result
    spec.loader.exec_module(result)
    return result


BUNDLE = module('build_icho_answer_blind_bundles')
CAMPAIGN = module('run_answer_blind_gpt_campaign')
SEED = module('build_answer_blind_solver_seed')


class FullTheoryTests(unittest.TestCase):
    def tearDown(self):
        CAMPAIGN.configure_target_scope(32)

    def test_contracts_cover_canonical_scope_without_changing_old_scope(self):
        self.assertEqual(len(BUNDLE.REQUESTED_OUTPUTS), 32)
        self.assertEqual(len(BUNDLE.FULL_THEORY_OUTPUTS), 68)
        for identifier, outputs in BUNDLE.FULL_THEORY_OUTPUTS.items():
            self.assertTrue(outputs, identifier)
            self.assertEqual(len(outputs), len({item['id'] for item in outputs}))
        self.assertEqual(len(BUNDLE.FULL_THEORY_OUTPUTS['icho_2026_t8_a4']), 35)
        for item in BUNDLE.FULL_THEORY_OUTPUTS['icho_2026_t6_a2']:
            self.assertTrue(item['semantic_requirements'])

    def test_real_bundle_is_blind_complete_and_controller_accepts_only_correct_scope(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = ROOT / 'icho_2026_source'
            blind = root / 'questions.jsonl'
            manifest = BUNDLE.build_bundles(
                input_jsonl=source / 'processed/icho_2026_theory.jsonl',
                blind_output=blind, grader_output=root / 'grader.jsonl',
                image_root=source / 'image', problem_pdf=source / 'raw/theory_problem.pdf',
                solution_pdf=source / 'raw/theory_solution.pdf',
                expected_count=68, full_theory=True,
            )
            self.assertEqual(manifest['row_count'], 68)
            rows = [json.loads(line) for line in blind.read_text().splitlines()]
            self.assertEqual(sum(row['points'] for row in rows), 437)
            self.assertTrue(all(row['formalization_ready'] for row in rows))
            self.assertTrue(all(row['official_answer_seen'] is False for row in rows))
            contract = SEED._blind_bundle_contract(blind.read_bytes(), location='test-bundle')
            self.assertEqual(len(contract.target_ids), 68)
            self.assertIn('icho_2026_t8_a10', contract.target_ids)
            with self.assertRaises(CAMPAIGN.CampaignError):
                CAMPAIGN._bundle_rows(blind)
            CAMPAIGN.configure_target_scope(68)
            self.assertEqual(len(CAMPAIGN._bundle_rows(blind)[1]), 68)
            self.assertEqual(CAMPAIGN.FULL_SCOPE_KIND, 'full68')
            rows[-1]['id'] = 'icho_2026_t9_a10'
            blind.write_text(''.join(json.dumps(row) + '\n' for row in rows))
            with self.assertRaisesRegex(CAMPAIGN.CampaignError, 'canonical'):
                CAMPAIGN._bundle_rows(blind)

    def test_concurrency_is_independent_of_target_count(self):
        args = CAMPAIGN._parser().parse_args([
            '--campaign-id', 'full68', '--campaign-root', '/srv/new-campaign',
            '--runtime-root', '/opt/new-runtime', '--target-count', '68',
        ])
        self.assertEqual(args.concurrency, 32)
        self.assertEqual(CAMPAIGN.MODEL_ID, 'gpt-5.6-sol')


if __name__ == '__main__':
    unittest.main()
