import asyncio
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from .engine import Draft, Spec, check_axiom_output, fingerprint, render, run, verify
from .search import SearchUnavailable, _request, search_both


def spec(**kwargs):
    return Spec(name='Demo.result', statement='True', imports=[], queries=['finite sum'], **kwargs)


def project(path):
    (path / 'lean-toolchain').write_text('leanprover/lean4:v4.34.0-rc1\n')
    (path / 'lakefile.toml').write_text('name = "formal_smoke"\nversion = "0.1.0"\n')


async def found(queries):
    return [{'library': lib, 'status': 'ok', 'query': q, 'results': []}
            for q in queries for lib in ['Mathlib', 'Physlib']]


class RetrievalTests(unittest.IsolatedAsyncioTestCase):
    async def test_both_libraries_receive_each_query(self):
        calls = []
        def request(q, package, limit, timeout):
            calls.append((q, package))
            return {'results': [], 'packages_applied': [package]}
        receipts = await search_both(['sum', 'units'], request=request)
        self.assertEqual(set(calls), {(q,p) for q in ['sum','units'] for p in ['Mathlib','Physlib']})
        self.assertEqual(len(receipts), 4)
        self.assertTrue(all(x['status'] == 'ok' for x in receipts))

    async def test_service_failure_is_not_an_empty_library_result(self):
        def request(q, package, limit, timeout):
            if package == 'Physlib':
                raise SearchUnavailable('HTTP 500')
            return {'results': [], 'packages_applied': [package]}
        receipts = await search_both(['sum'], request=request)
        self.assertEqual([x['status'] for x in receipts], ['ok', 'unavailable'])

    def test_unapplied_package_filter_is_rejected(self):
        class Response:
            def __enter__(self): return self
            def __exit__(self, *args): pass
            def read(self): return b'{"packages_applied":[],"results":[]}'
        with patch(_request.__module__ + '.urlopen', return_value=Response()):
            with self.assertRaises(SearchUnavailable):
                _request('sum', 'Physlib', 5, 10)


class GateTests(unittest.TestCase):
    def test_humanize_recognizes_the_formal_flow_config(self):
        from hmz.flows import configures
        schema = configures(Path(__file__).parent)
        self.assertIsNotNone(schema)
        self.assertIn('result_path', schema.model_fields)
        self.assertIn('project', schema.model_fields)

    def test_native_output_schema_requires_every_property(self):
        schema = Draft.model_json_schema()
        self.assertEqual(set(schema['required']), set(schema['properties']))

    def test_axiom_receipt_requires_exact_target_and_standard_axioms(self):
        self.assertTrue(check_axiom_output("'Demo.result' depends on axioms: [propext, Classical.choice, Quot.sound]",'Demo.result')[0])
        self.assertTrue(check_axiom_output("'Demo.result' does not depend on any axioms",'Demo.result')[0])
        for output in ["'Other' does not depend on any axioms", '',
                       "'Demo.result' depends on axioms: [sorryAx]",
                       "'Demo.result' depends on axioms: [my_custom_axiom]",
                       "'Demo.result' does not depend on any axioms\n'Demo.result' does not depend on any axioms"]:
            self.assertFalse(check_axiom_output(output,'Demo.result')[0])

    def test_direct_escape_and_unfinished_proof_are_rejected(self):
        for body in ['sorry', 'exact sorryAx _ false', 'admit', 'native_decide',
                     'run_tac pure ()', 'exact True.intro\naxiom escape : False',
                     '#print axioms Demo.result']:
            with self.subTest(body=body), self.assertRaises(ValueError):
                render(spec(), body)

    def test_compiler_timeout_is_not_a_mathematical_rejection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); project(root); attempt=root/'attempt'; attempt.mkdir()
            with patch(verify.__module__ + '.command', return_value={
                'returncode':None, 'timed_out':True, 'output':''}):
                report=verify(spec(),'exact True.intro',root,attempt,1)
            self.assertFalse(report['accepted'])
            self.assertEqual(report['stage'],'compiler_timeout')
            self.assertIn('timed out',report['feedback'])

    def test_source_changes_are_detected_but_run_artifacts_are_excluded(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); project(root)
            initial = fingerprint(root)
            runs = root / '.humanize-formal-runs'; runs.mkdir()
            (runs / 'Generated.lean').write_text('theorem demo : True := by trivial')
            self.assertEqual(initial, fingerprint(root))
            (root / 'Local.lean').write_text('def n := 1')
            self.assertNotEqual(initial, fingerprint(root))


class LoopTests(unittest.IsolatedAsyncioTestCase):
    async def test_compile_feedback_drives_repair_without_changing_target(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp); project(root); prompts = []; checked = []
            async def propose(prompt, attempt):
                prompts.append(prompt)
                return Draft(proof='bad' if len(prompts)==1 else 'exact True.intro')
            def check(target, proof, project, attempt, timeout):
                checked.append(target.model_dump())
                return {'accepted': proof!='bad', 'stage':'compile', 'feedback':'unknown constant bad'}
            outcome = await run(spec(),root,propose,max_rounds=2,search=found,checker=check,build=False)
            self.assertTrue(outcome['accepted'])
            self.assertIn('unknown constant bad',prompts[1])
            self.assertEqual(checked[0],checked[1])
            self.assertEqual(len(outcome['attempts']),2)

    async def test_missing_second_library_stops_before_model_call(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);project(root)
            async def search(queries): return [{'library':'Mathlib','status':'ok','results':[]}]
            async def propose(*args): self.fail('must not call model')
            outcome=await run(spec(),root,propose,search=search,build=False)
            self.assertEqual(outcome['status'],'retrieval_unavailable')
            self.assertFalse(outcome['accepted'])

    async def test_project_drift_cannot_receive_acceptance(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);project(root)
            async def propose(*args):
                (root/'Extra.lean').write_text('axiom forged : False')
                return Draft(proof='exact forged.elim')
            outcome=await run(spec(),root,propose,search=found,build=False)
            self.assertEqual(outcome['status'],'environment_changed')
            self.assertFalse(outcome['accepted'])

    async def test_round_limit_is_not_acceptance(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);project(root)
            async def propose(*args): return Draft(proof='bad')
            def check(*args): return {'accepted':False,'stage':'compile','feedback':'bad'}
            outcome=await run(spec(),root,propose,max_rounds=1,search=found,checker=check,build=False)
            self.assertEqual(outcome['status'],'round_limit')
            self.assertFalse(outcome['accepted'])


@unittest.skipUnless(os.environ.get('QUANTUM_LEAN_TEST_TOOLCHAIN'), 'set QUANTUM_LEAN_TEST_TOOLCHAIN for real Lean tests')
class RealLeanTests(unittest.TestCase):
    def test_real_kernel_acceptance_and_rejection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp); project(root)
            (root/'lean-toolchain').write_text(os.environ['QUANTUM_LEAN_TEST_TOOLCHAIN']+'\n')
            for index,(context,body,accepted) in enumerate([
                ('','exact True.intro',True),
                ('','exact Nat.zero',False),
                ('axiom unproved_helper : True','exact unproved_helper',False),
                ('theorem unfinished_helper : True := by sorry','exact unfinished_helper',False),
            ]):
                with self.subTest(index=index):
                    attempt=root/'.humanize-formal-runs'/str(index); attempt.mkdir(parents=True)
                    report=verify(spec(context=context),body,root,attempt,120)
                    self.assertEqual(report['accepted'],accepted,report)
                    if index>=2:
                        self.assertEqual(report['stage'],'acceptance')
                        self.assertTrue(report['axioms'])
