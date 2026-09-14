"""Regression: incomplete composition audits continue; they do not rewrite proofs."""
import json
import unittest
from . import test_flow as fake, test_integration as integration


def incomplete(session):
    return fake.review(session, verdict='inconclusive', full_claim_checked=False,
                       first_fault='Unfinished dependency reading', repair='Finish own reading')


def composed(session):
    return {'candidate': integration.combination(session, scope='selected_obligation'), 'next_tasks': []}


class IntegrationReauditTests(unittest.TestCase):
    setUp = fake.FlowTests.setUp
    git = fake.FlowTests.git
    source_files = fake.FlowTests.source_files
    make_agents = fake.FlowTests.make_agents
    assert_stopped = fake.FlowTests.assert_stopped

    def execute(self, script, **changes):
        settings = dict(integrate=True, optimize=True, integration_closure=True,
                        coverage_planning=False, audit_continuations=2)
        settings.update(changes)
        return fake.FlowTests.execute(self, script, **settings)

    def test_composition_continues_only_unfinished_reviewer(self):
        def finish(session):
            previous = [c for c in script.calls if c.role == 'reviewer_a'][-2]
            self.assertIs(previous.session, session)
            self.assertIn('SAME-REVIEWER AUDIT CONTINUATION', session.prompts[-1])
            return fake.review(session)
        script = fake.Script(solver=[integration.local], integrator=[composed],
                             reviewer_a=[fake.DEFAULT, incomplete, finish])
        work, result = self.execute(script)
        self.assertEqual(result['status'], 'reviewed_candidate_pending_manual_integration')
        self.assertEqual(script.role_calls['reviewer_a'], 3)
        self.assertEqual(script.role_calls['reviewer_b'], 2)
        self.assertEqual(script.role_calls['mender'], 0)
        requests = [json.loads(p.read_text()) for p in work.glob('call-*/request.json')]
        self.assertEqual(sum(bool(r['continuation_of']) for r in requests), 1)

    def test_large_audit_can_finish_on_fourth_continuation(self):
        def finish(session):
            own = [c for c in script.calls if c.role == 'reviewer_a'][1:]
            self.assertTrue(all(c.session is session for c in own))
            return fake.review(session)
        script = fake.Script(solver=[integration.local], integrator=[composed],
            reviewer_a=[fake.DEFAULT, incomplete, incomplete, incomplete, incomplete, finish])
        _, result = self.execute(script, audit_continuations=4)
        self.assertEqual(result['status'], 'reviewed_candidate_pending_manual_integration')
        self.assertEqual(script.role_calls['reviewer_b'], 2)
        self.assertEqual(script.role_calls['mender'], 0)

    def test_larger_read_ranges_preserve_single_line_unicode_json(self):
        from ._audit import byte_ranges
        data = json.dumps({'argument': '证明🙂éα' * 12000}, ensure_ascii=False).encode()
        ranges = list(byte_ranges(data))
        chunks = [data[start:start+count] for start, count in ranges]
        self.assertEqual(b''.join(chunks), data)
        self.assertTrue(all(len(c) <= 8192 for c in chunks))
        self.assertGreater(len(chunks[0]), 4096)
        self.assertEqual(''.join(c.decode('utf-8') for c in chunks), data.decode('utf-8'))

    def test_exhausted_composition_audit_queues_unchanged_draft(self):
        script = fake.Script(solver=[integration.local], integrator=[composed],
                             reviewer_a=[fake.DEFAULT, incomplete, incomplete, incomplete])
        work, result = self.execute(script)
        record = json.loads((work/'integration-1.json').read_text())
        self.assertEqual(record['status'], 'audit_pending')
        self.assertEqual(result['pending_audits'], 1)
        self.assertEqual(script.role_calls['mender'], 0)
        self.assertNotEqual(result['status'], 'reviewed_candidate_pending_manual_integration')

    def test_recovered_composition_finishes_without_reintegration(self):
        script = fake.Script(solver=[integration.local], integrator=[composed],
                             reviewer_a=[fake.DEFAULT, incomplete, incomplete, incomplete, fake.DEFAULT])
        _, result = self.execute(script, rounds=2)
        self.assertEqual(result['status'], 'reviewed_candidate_pending_manual_integration')
        self.assertEqual(script.role_calls['integrator'], 1)
        self.assertEqual(script.role_calls['solver'], 1)
        self.assertEqual(script.role_calls['mender'], 0)
        self.assertEqual(result['pending_audits'], 0)

    def test_real_composition_gap_still_requires_repair(self):
        script = fake.Script(solver=[integration.local], integrator=[composed],
                             reviewer_a=[fake.DEFAULT, fake.negative])
        work, result = self.execute(script)
        record = json.loads((work/'integration-1.json').read_text())
        self.assertEqual(record['status'], 'needs_repair')
        self.assertNotEqual(result['status'], 'reviewed_candidate_pending_manual_integration')

    def test_subtask_success_is_reviewable_without_global_promotion(self):
        def draft(session):
            return integration.local(session,
                claim='Synthetic bounded exclusion task is met; full M5 remains open.',
                remaining_obligations=['Full M5 coverage remains unproved.'])

        def checked(session):
            prompt = session.prompts[-1]
            self.assertIn('SCOPE AND COMPLETION', prompt)
            self.assertIn('A valid sublemma', prompt)
            self.assertIn('audit its actual quantified coverage', prompt)
            return fake.review(session)

        script = fake.Script(solver=[draft], reviewer_a=[checked], reviewer_b=[checked])
        work, result = self.execute(script, integrate=False)
        record = json.loads((work/'candidate-result-1-0.json').read_text())
        self.assertEqual(record['status'], 'reviewed_sublemma_pending_manual_integration')
        self.assertFalse(result['research_goal_proved'])
        self.assertEqual(script.role_calls['mender'], 0)

    def test_other_obligation_draft_is_evidence_not_pending_integration(self):
        import hashlib
        from . import Candidate, proof_bytes, proof_path
        name = fake.pipeline.COMMON_INPUTS[0]
        candidate = Candidate(obligation_id='distance_law', scope='sublemma',
            evidence='analytic_draft', claim='Other obligation historical draft',
            argument='Synthetic fixture', unproved_steps=[], dependencies=[{
                'path': name, 'sha256': hashlib.sha256((self.repo/name).read_bytes()).hexdigest(),
                'section': 'Fixture'}])
        data = proof_bytes(candidate)
        path = proof_path(data)
        (self.repo/path).write_bytes(data)
        script = fake.Script(solver=[None])
        _, result = self.execute(script, extra_inputs=[path])
        self.assertEqual(script.role_calls['integrator'], 0)
        self.assertFalse(result['integration_pending'])
        self.assertTrue(all((s.cwd/path).read_bytes()==data for s in script.sessions))
