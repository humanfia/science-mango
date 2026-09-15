"""Replay verified exact character repairs, then continue the frozen DAG."""
import asyncio
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(HERE.parents[4]))
from hmz.flows import flow
from pipelines.quantum_formalize_dag import Agents, Config
from pipelines.quantum_formalize.engine import Spec, Draft, render, digest, save
from pipelines.quantum_formalize.dag_runner import run_graph, load_graph
from pipelines.quantum_formalize.search import search_both

ARCHIVE = HERE / 'experiments/interrupted_initial'
REPAIRS = {}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

@flow
async def repair_dag(agents: Agents, task: str, config: Config | None = None) -> None:
    if config is None:
        raise ValueError('config required')
    graph, nodes = load_graph(config.graph)
    assert graph == json.loads((ARCHIVE / 'graph.json').read_text())
    for name, value in json.loads((ARCHIVE / 'MANIFEST.json').read_text()).items():
        assert sha(ARCHIVE / name) == value
    drafts, sources, calls, replays = {}, {}, [], []
    for node in nodes:
        receipt_path = ARCHIVE / 'nodes' / node.id / 'receipt.json'
        receipt = json.loads(receipt_path.read_text()) if receipt_path.exists() else {}
        if receipt.get('accepted'):
            result = receipt['result']
            assert result['accepted']
            last = result['attempts'][-1]
            folder = ARCHIVE / 'node_runs' / node.id / Path(last['proof_path']).parent.name
            assert digest(result['artifacts'][node.id]['payload']) == result['artifacts'][node.id]['sha256']
            origin = 'Unchanged accepted live proof; recompile exact target and audit again.'
        elif node.id in REPAIRS:
            folder = HERE / 'repairs' / REPAIRS[node.id]
            last = json.loads((folder / 'verdict.json').read_text())
            assert last['accepted']
            origin = 'Independently kernel/target/axiom-verified tactic repair; no statement or assumption change.'
        else:
            continue
        spec = Spec.model_validate(json.loads((ARCHIVE / 'nodes' / node.id / 'resolved-spec.json').read_text()))
        assert spec.statement == node.spec['statement']
        draft = json.loads((folder / 'draft.json').read_text())
        candidate = folder / Path(last['proof_path']).name
        target = folder / Path(last['target_path']).name
        assert sha(candidate) == last['source_sha256']
        assert sha(target) == last['target_sha256']
        assert candidate.read_text() == render(spec, draft['proof'], target.stem)
        drafts[node.id] = draft
        sources[node.id] = {'origin': origin, 'draft_sha256': sha(folder / 'draft.json')}

    interrupted = {}
    for name in ['boundary_weighted_sum', 'dual_weighted_sum']:
        folder = ARCHIVE / 'node_runs' / name / 'attempt-001'
        interrupted[name] = json.loads((folder / 'draft.json').read_text())

    async def propose(node, prompt, attempt):
        if node.id in interrupted:
            return interrupted.pop(node.id)
        if node.id in drafts:
            assert node.id not in replays, 'Deterministic repair failed; inspect before retrying'
            replays.append(node.id)
            return drafts[node.id]
        calls.append({'node': node.id, 'attempt': attempt.name})
        worker = agents.prover.clone(name=f'{node.id}-{attempt.name}', skills=[])
        session = worker.new(attempt)
        session.loads([])
        turn = asyncio.create_task(session.aturn(prompt, schema=Draft))
        try:
            return await asyncio.wait_for(turn, timeout=config.turn_timeout)
        finally:
            try:
                session.close()
            finally:
                worker.stop()
            if not turn.done():
                turn.cancel()
            await asyncio.gather(turn, return_exceptions=True)

    result = await run_graph(config.graph, config.project, config.output, propose,
        concurrency=config.concurrency, rounds=config.rounds, timeout=config.compile_timeout,
        search=search_both)
    save(Path(config.result_path), result)
    save(HERE / 'REPAIR_REPLAY.json', {'sources': sources, 'replayed_nodes': replays,
        'live_model_attempts': calls, 'retrieval': 'Fresh Mathlib and Physlib searches',
        'math_statements_changed': False, 'result': result})
    print(json.dumps(result, indent=2), flush=True)
