import asyncio
import json
from pathlib import Path
import tempfile
import unittest

from .dag import Node, run_dag, validate


class ValidationTests(unittest.TestCase):
    def test_invalid_graphs(self):
        graphs = [[Node('a'), Node('a')], [Node('a', ('missing',))],
                  [Node('a', ('b',)), Node('b', ('a',))], [Node('../escape')],
                  [Node('a', ('b', 'b')), Node('b')]]
        for graph in graphs:
            with self.subTest(graph=graph), self.assertRaises(ValueError):
                validate(graph)

    def test_stable_topological_order(self):
        self.assertEqual(validate([Node('z', ('b',)), Node('b'), Node('a')]), ['a', 'b', 'z'])


class SchedulerTests(unittest.IsolatedAsyncioTestCase):
    async def test_dependency_gate_and_parallel_bound(self):
        active, peak = 0, 0
        started, finished = [], set()
        async def execute(node, deps, directory):
            nonlocal active, peak
            self.assertTrue(set(node.dependencies) <= finished)
            self.assertTrue(all(r['accepted'] for r in deps.values()))
            self.assertTrue(directory.is_dir())
            started.append(node.id)
            active += 1
            peak = max(peak, active)
            await asyncio.sleep(.01)
            active -= 1
            finished.add(node.id)
            return {'accepted': True}
        nodes = [Node(f'n{i:02}', spec={}) for i in range(20)]
        nodes.append(Node('root', tuple(n.id for n in nodes), spec={}))
        with tempfile.TemporaryDirectory() as tmp:
            result = await run_dag(nodes, execute, tmp)
            self.assertEqual(peak, 16)
            self.assertEqual(started[:16], [f'n{i:02}' for i in range(16)])
            self.assertTrue(result['all_nodes_accepted'])
            self.assertFalse(result['m5_formalized'])
            self.assertEqual(json.loads((Path(tmp) / 'state.json').read_text()), result)
            self.assertTrue(json.loads((Path(tmp) / 'root/receipt.json').read_text())['accepted'])

    async def test_failure_and_planned_block_only_descendants(self):
        called = []
        async def execute(node, deps, directory):
            called.append(node.id)
            if node.id == 'bad':
                raise RuntimeError('compiler failed')
            return {'accepted': True}
        nodes = [Node('bad', spec={}), Node('child', ('bad',), {}),
                 Node('grandchild', ('child',), {}), Node('planned'),
                 Node('waiting', ('planned',), {}), Node('good', spec={})]
        with tempfile.TemporaryDirectory() as tmp:
            result = await run_dag(nodes, execute, tmp)
        self.assertEqual(set(called), {'bad', 'good'})
        self.assertEqual({k: v['status'] for k, v in result['nodes'].items()},
                         {'bad': 'failed', 'child': 'blocked', 'grandchild': 'blocked',
                          'planned': 'planned', 'waiting': 'blocked', 'good': 'accepted'})
        self.assertFalse(result['all_nodes_accepted'])

    async def test_cancellation_durable_and_reaps_tasks(self):
        entered, cleaned = asyncio.Event(), asyncio.Event()
        async def execute(node, deps, directory):
            entered.set()
            try:
                await asyncio.Event().wait()
            finally:
                cleaned.set()
        with tempfile.TemporaryDirectory() as tmp:
            task = asyncio.create_task(run_dag([Node('a', spec={}), Node('b', ('a',), {})], execute, tmp))
            await entered.wait()
            task.cancel()
            with self.assertRaises(asyncio.CancelledError):
                await task
            self.assertTrue(cleaned.is_set())
            state = json.loads((Path(tmp) / 'state.json').read_text())
            self.assertEqual(state['status'], 'cancelled')
            self.assertTrue(all(r['status'] == 'cancelled' for r in state['nodes'].values()))
            self.assertFalse(state['all_nodes_accepted'])

    async def test_acceptance_requires_literal_true_and_json_receipt(self):
        for receipt in [{'accepted': 1}, {'accepted': 'true'}, None, {'accepted': True, 'bad': object()}]:
            async def execute(*args):
                return receipt
            with self.subTest(receipt=receipt), tempfile.TemporaryDirectory() as tmp:
                result = await run_dag([Node('a', spec={})], execute, tmp)
                self.assertEqual(result['nodes']['a']['status'], 'failed')

    async def test_reject_stale_output_and_bad_concurrency(self):
        async def execute(*args):
            return {'accepted': True}
        with tempfile.TemporaryDirectory() as tmp:
            for limit in [0, 17, True, 1.5]:
                with self.assertRaises(ValueError):
                    await run_dag([], execute, tmp, max_concurrency=limit)
            result = await run_dag([], execute, tmp)
            self.assertFalse(result['all_nodes_accepted'])
            with self.assertRaises(ValueError):
                await run_dag([], execute, tmp)

    async def test_executor_cancellation_blocks_child_and_continues_branch(self):
        async def execute(node, deps, directory):
            if node.id == 'a':
                raise asyncio.CancelledError()
            return {'accepted': True}
        with tempfile.TemporaryDirectory() as tmp:
            result = await run_dag([Node('a', spec={}), Node('b', ('a',), {}),
                                    Node('c', spec={})], execute, tmp)
        self.assertEqual(result['nodes']['a']['status'], 'cancelled')
        self.assertEqual(result['nodes']['b']['status'], 'blocked')
        self.assertEqual(result['nodes']['c']['status'], 'accepted')

    async def test_dependency_receipts_are_copies(self):
        async def execute(node, deps, directory):
            if deps:
                deps['a']['status'] = 'failed'
                deps['a']['result']['accepted'] = False
            return {'accepted': True}
        with tempfile.TemporaryDirectory() as tmp:
            result = await run_dag([Node('a', spec={}), Node('b', ('a',), {})], execute, tmp)
        self.assertTrue(result['all_nodes_accepted'])
        self.assertTrue(result['nodes']['a']['result']['accepted'])


if __name__ == '__main__':
    unittest.main()
