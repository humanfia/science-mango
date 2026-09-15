import asyncio
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from . import dag_runner as runner
from . import engine
from .engine import digest, render


def artifact(name, ancestors=()):
    payload = {'name': name, 'ancestors': list(ancestors),
               'declaration': f'theorem {name} : True := by trivial',
               'imports': ['Mathlib'], 'spec_sha256': 'frozen'}
    return {'payload': payload, 'sha256': digest(payload)}


def receipt(artifacts):
    return {'accepted': True, 'result': {'artifacts': artifacts}}


def node(name, deps=(), imports=None):
    return {'id': name, 'dependencies': list(deps),
            'spec': {'name': name, 'statement': 'True', 'imports': imports or ['Mathlib'],
                     'queries': ['True']}}


class DependencyTests(unittest.TestCase):
    def test_transitive_diamond_merges_once_in_order(self):
        a, b, c = artifact('a'), artifact('b', ['a']), artifact('c', ['a'])
        values, context = runner.proof_context({'b': receipt({'b': b, 'a': a}),
                                               'c': receipt({'c': c, 'a': a})})
        self.assertEqual(set(values), {'a', 'b', 'c'})
        self.assertEqual(context.count('theorem a'), 1)
        self.assertLess(context.index('theorem a'), context.index('theorem b'))

    def test_unaccepted_tampered_missing_cycle_conflict_rejected(self):
        a = artifact('a')
        tampered = artifact('a')
        tampered['payload']['declaration'] = 'theorem forged : False := by sorry'
        conflict = artifact('different')
        cases = [{'a': {'accepted': False}}, {'a': receipt({'a': tampered})},
                 {'b': receipt({'b': artifact('b', ['missing'])})},
                 {'a': receipt({'a': artifact('a', ['b']), 'b': artifact('b', ['a'])})},
                 {'a': receipt({'a': a}), 'b': receipt({'a': conflict})}]
        for case in cases:
            with self.subTest(case=case), self.assertRaises(ValueError):
                runner.proof_context(case)

    def test_load_graph_rejects_context_and_duplicate_declarations(self):
        for change in ['context', 'duplicate']:
            with self.subTest(change=change), tempfile.TemporaryDirectory() as tmp:
                nodes = [node('a'), node('b')]
                if change == 'context':
                    nodes[0]['spec']['context'] = 'axiom bad : False'
                else:
                    nodes[1]['spec']['name'] = 'a'
                path = Path(tmp) / 'graph.json'
                path.write_text(json.dumps({'nodes': nodes}))
                with self.assertRaises(ValueError):
                    runner.load_graph(path)


class RunnerTests(unittest.IsolatedAsyncioTestCase):
    async def scenario(self, nodes, *, failure=None, corrupt=False, assembly_code=0,
                       assembly_axioms=None, changed=False, altered_draft=False):
        with tempfile.TemporaryDirectory() as tmp:
            area = Path(tmp)
            graph = area / 'graph.json'
            graph.write_text(json.dumps({'nodes': nodes}))
            calls, commands = {}, []
            async def run(spec, project, propose, **kwargs):
                calls[spec.name] = spec
                if spec.name == failure:
                    return {'accepted': False, 'attempts': []}
                attempt = area / spec.name
                attempt.mkdir()
                target = attempt / 'FrozenTarget.lean'
                source = attempt / 'Candidate.lean'
                target.write_text('def QuantumHarnessFrozenTarget : Prop := True\n')
                source.write_text(render(spec, 'trivial'))
                (attempt / 'draft.json').write_text(json.dumps({'proof': 'exact True.intro' if altered_draft else 'trivial'}))
                return {'accepted': True, 'attempts': [{'proof_path': str(source),
                        'target_path': str(target),
                        'target_sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
                        'source_sha256': 'wrong' if corrupt else hashlib.sha256(source.read_bytes()).hexdigest()}]}
            def command(args, project, timeout):
                commands.append(args)
                build = args[1] == 'build'
                names = list(calls) if assembly_axioms is None else assembly_axioms
                output = '\n'.join(f"'{name}' does not depend on any axioms" for name in names)
                return {'returncode': 0 if build else assembly_code, 'timed_out': False, 'output': output}
            def fingerprint(project):
                return {'source': 'changed' if changed and len(commands) > 1 else 'fixed'}
            async def propose(*args):
                self.fail('mock run should not invoke model')
            with patch.object(runner, 'run', run), patch.object(runner, 'command', command), \
                 patch.object(runner, 'fingerprint', fingerprint):
                result = await runner.run_graph(graph, area, area / 'out', propose)
            union = area / 'out/AcceptedExperiment.lean'
            state = json.loads((area / 'out/nodes/state.json').read_text())
            return result, calls, commands, union.read_text() if union.exists() else '', state

    async def test_accepted_dependency_bound_in_child_context_and_union(self):
        result, calls, commands, union, state = await self.scenario([
            node('a', imports=['Mathlib.Data.Nat.Basic']), node('b', ['a'])])
        self.assertIn('theorem a : True', calls['b'].context)
        self.assertIn('Mathlib.Data.Nat.Basic', calls['b'].imports)
        self.assertEqual(union.count('theorem a'), 1)
        self.assertLess(union.index('theorem a'), union.index('theorem b'))
        self.assertTrue(result['assembly_accepted'])
        self.assertTrue(result['experiment_passed'])
        self.assertFalse(result['m5_formalized'])
        self.assertEqual(commands[-1][:3], ['lake', 'env', 'lean'])
        self.assertEqual(state['nodes']['b']['result']['artifacts']['b']['payload']['ancestors'], ['a'])

    async def test_failed_proof_blocks_child_but_independent_branch_compiles(self):
        result, calls, commands, union, state = await self.scenario([
            node('a'), node('b', ['a']), node('c')], failure='a')
        self.assertEqual(set(calls), {'a', 'c'})
        self.assertEqual(result['accepted_nodes'], ['c'])
        self.assertFalse(result['experiment_passed'])
        self.assertEqual(state['nodes']['b']['status'], 'blocked')
        self.assertNotIn('theorem a', union)

    async def test_corrupt_candidate_never_published(self):
        result, calls, commands, union, state = await self.scenario([node('a')], corrupt=True)
        self.assertEqual(result['accepted_nodes'], [])
        self.assertFalse(result['assembly_accepted'])
        self.assertEqual(union, '')
        self.assertIn('source changed', state['nodes']['a']['result']['error'])

    async def test_altered_draft_never_published_even_if_candidate_hash_matches(self):
        result, calls, commands, union, state = await self.scenario([node('a')], altered_draft=True)
        self.assertEqual(result['accepted_nodes'], [])
        self.assertEqual(union, '')
        self.assertIn('draft does not match', state['nodes']['a']['result']['error'])

    async def test_retrieval_fallback_keeps_history_and_real_engine_rejects_unavailable(self):
        for fallback_ok in [True, False]:
            with self.subTest(fallback_ok=fallback_ok), tempfile.TemporaryDirectory() as tmp:
                area = Path(tmp)
                graph = area / 'graph.json'
                n = node('a')
                n['metadata'] = {'fallback_queries': ['fallback query']}
                graph.write_text(json.dumps({'nodes': [n]}))
                searched, proposed, compiled = [], [], []

                async def provider(queries):
                    searched.append(list(queries))
                    return [{'library': lib, 'status': 'ok' if lib == 'Mathlib' or
                             (queries == ['fallback query'] and fallback_ok) else 'unavailable',
                             'query': queries[0], 'results': [{'name': ('original' if queries == ['True'] else 'fallback') + ' ' + lib + ' lemma'}]} for lib in ['Mathlib', 'Physlib']]

                async def propose(*args):
                    proposed.append(args[1])
                    return {'proof': 'trivial', 'queries': []}

                def checker(spec, proof, project, attempt, timeout):
                    compiled.append(True)
                    target, source = attempt / 'FrozenTarget.lean', attempt / 'Candidate.lean'
                    target.write_text('def QuantumHarnessFrozenTarget : Prop := True\n')
                    source.write_text(render(spec, proof))
                    return {'accepted': True, 'stage': 'acceptance', 'proof_path': str(source),
                            'target_path': str(target),
                            'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest()}

                # Exercise the real engine retrieval gate, mocking only Lean compilation.
                async def actual_run(spec, project, propose, **kwargs):
                    return await engine.run(spec, project, propose, checker=checker, **kwargs)

                with patch.object(runner, 'run', actual_run), \
                     patch.object(runner, 'fingerprint', return_value={'fixed': 'hash'}), \
                     patch.object(engine, 'fingerprint', return_value={'fixed': 'hash'}), \
                     patch.object(runner, 'command', return_value={'returncode': 0, 'timed_out': False,
                                                                  'output': "'a' does not depend on any axioms"}):
                    result = await runner.run_graph(graph, area, area / 'out', propose, search=provider)
                self.assertEqual(searched, [['True'], ['fallback query']])
                history = json.loads((area / 'out/nodes/a/retrieval-history.json').read_text())
                self.assertEqual(len(history), 2)
                self.assertEqual(history[0]['receipts'][1]['status'], 'unavailable')
                self.assertEqual(history[1]['fallback_for'], ['True'])
                self.assertEqual(history[1]['receipts'][1]['status'], 'ok' if fallback_ok else 'unavailable')
                self.assertEqual(bool(proposed), fallback_ok)
                self.assertEqual(bool(compiled), fallback_ok)
                self.assertEqual(result['experiment_passed'], fallback_ok)
                if fallback_ok:
                    self.assertIn('original Mathlib lemma', proposed[0])
                    self.assertNotIn('fallback Mathlib lemma', proposed[0])
                    self.assertIn('fallback Physlib lemma', proposed[0])
                if not fallback_ok:
                    state = json.loads((area / 'out/nodes/state.json').read_text())
                    self.assertEqual(state['nodes']['a']['result']['status'], 'retrieval_unavailable')

    async def test_final_compile_missing_axiom_and_environment_fail_gate(self):
        for options in [{'assembly_code': 1}, {'assembly_axioms': []}, {'changed': True}]:
            with self.subTest(options=options):
                result, *_ = await self.scenario([node('a')], **options)
                self.assertFalse(result['experiment_passed'])

    async def test_planned_root_does_not_become_formalized(self):
        result, calls, commands, union, state = await self.scenario([
            node('a'), {'id': 'm5', 'dependencies': ['a'], 'spec': None}])
        self.assertEqual(result['accepted_nodes'], ['a'])
        self.assertEqual(result['planned_nodes'], 1)
        self.assertFalse(result['m5_formalized'])
        self.assertEqual(state['nodes']['m5']['status'], 'planned')

    async def test_cancelled_executor_leaves_honest_scheduler_receipts(self):
        entered, cleaned = asyncio.Event(), asyncio.Event()
        async def run(*args, **kwargs):
            entered.set()
            try:
                await asyncio.Event().wait()
            finally:
                cleaned.set()
        async def propose(*args):
            self.fail('no live model calls')
        with tempfile.TemporaryDirectory() as tmp:
            area = Path(tmp)
            graph = area / 'graph.json'
            graph.write_text(json.dumps({'nodes': [node('a'), node('b', ['a'])]}))
            with patch.object(runner, 'run', run), \
                 patch.object(runner, 'fingerprint', return_value={'fixed': 'hash'}), \
                 patch.object(runner, 'command', return_value={'returncode': 0, 'timed_out': False, 'output': ''}):
                task = asyncio.create_task(runner.run_graph(graph, area, area / 'out', propose))
                await entered.wait()
                task.cancel()
                with self.assertRaises(asyncio.CancelledError):
                    await task
            self.assertTrue(cleaned.is_set())
            state = json.loads((area / 'out/nodes/state.json').read_text())
            self.assertEqual(state['status'], 'cancelled')
            self.assertTrue(all(not n['accepted'] for n in state['nodes'].values()))


if __name__ == '__main__':
    unittest.main()
