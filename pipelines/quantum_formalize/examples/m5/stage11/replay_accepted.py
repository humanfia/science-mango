"""Replay receipt-verified accepted drafts through the real kernel, without model/search calls.

Default verifies inputs only. Pass --run after the portable-declaration regression passes.
Historical retrieval receipts are replayed verbatim and explicitly marked as historical here.
"""
import argparse
import asyncio
import copy
import hashlib
import json
import os
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
sys.path.insert(0, str(REPO))
from pipelines.quantum_formalize.dag_runner import load_graph, run_graph
from pipelines.quantum_formalize.engine import Spec, digest, render

ARCHIVE = HERE / 'experiments/initial_transport_failure'
PROJECT = Path('/home/jing/m5-lean-binomial-formalization')

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def save(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')

def prepare():
    graph, nodes = load_graph(HERE / 'graph.json')
    assert graph == json.loads((ARCHIVE / 'graph.json').read_text())
    state = json.loads((ARCHIVE / 'nodes/state.json').read_text())
    manifest = json.loads((ARCHIVE / 'MANIFEST.json').read_text())
    for name, value in manifest.get('files', manifest).items():
        assert sha(ARCHIVE / name) == value
    drafts, inputs, retrievals = {}, {}, {}
    for node in nodes:
        if node.spec is None:
            continue
        record = state['nodes'][node.id]
        assert record['accepted'] and record['status'] == 'accepted'
        receipt_path = ARCHIVE / 'nodes' / node.id / 'receipt.json'
        assert json.loads(receipt_path.read_text()) == record
        result = record['result']
        last = result['attempts'][-1]
        assert last['accepted'] and set(last['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
        area = ARCHIVE / 'node_runs' / node.id / Path(last['proof_path']).parent.name
        candidate = area / Path(last['proof_path']).name
        target = area / Path(last['target_path']).name
        draft_path = area / 'draft.json'
        draft = json.loads(draft_path.read_text())
        spec = Spec.model_validate(json.loads((ARCHIVE / 'nodes' / node.id / 'resolved-spec.json').read_text()))
        assert spec.statement == node.spec['statement'] and spec.name == node.spec['name']
        assert sha(candidate) == last['source_sha256'] and sha(target) == last['target_sha256']
        assert render(spec, draft['proof'], target.stem) == candidate.read_text()
        frozen = ''.join(f'import {x}\n' for x in spec.imports) + '\n' + spec.context + '\ndef QuantumHarnessFrozenTarget : Prop :=\n' + '\n'.join('  ' + line for line in spec.statement.splitlines()) + '\n'
        assert target.read_text() == frozen
        artifact = result['artifacts'][node.id]
        assert digest(artifact['payload']) == artifact['sha256']
        assert digest(node.spec) == artifact['payload']['spec_sha256']
        original_declaration = f'theorem {spec.name} : {spec.statement} := by\n' + '\n'.join('  ' + line for line in draft['proof'].splitlines())
        assert artifact['payload']['declaration'] == original_declaration
        drafts[node.id] = draft
        # run_graph begins each fresh one-attempt replay with the original spec queries.
        # Keep the original first-attempt successful dual-library receipt, not a fresh search.
        retrieval_path = ARCHIVE / 'node_runs' / node.id / 'attempt-001/retrieval.json'
        receipts = json.loads(retrieval_path.read_text())
        assert {r['library'] for r in receipts} == {'Mathlib', 'Physlib'}
        assert all(r['status'] == 'ok' for r in receipts)
        key = tuple(spec.queries)
        retrievals.setdefault(key, []).append({'node': node.id, 'path': str(retrieval_path.relative_to(HERE)), 'sha256': sha(retrieval_path), 'receipts': receipts})
        inputs[node.id] = {'receipt': str(receipt_path.relative_to(HERE)), 'receipt_sha256': sha(receipt_path), 'candidate': str(candidate.relative_to(HERE)), 'candidate_sha256': sha(candidate), 'target': str(target.relative_to(HERE)), 'target_sha256': sha(target), 'draft': str(draft_path.relative_to(HERE)), 'draft_sha256': sha(draft_path), 'proof_body_sha256': hashlib.sha256(draft['proof'].encode()).hexdigest(), 'accepted_attempt': last['attempt'], 'artifact_sha256': artifact['sha256']}
    assert len(drafts) == 4
    return drafts, inputs, retrievals

async def main(execute):
    drafts, inputs, retrievals = prepare()
    provenance = {'kind': 'deterministic accepted-proof replay', 'model_calls': 0, 'network_search_calls': 0, 'proof_bodies_modified': False, 'graph_sha256': sha(HERE / 'graph.json'), 'original_archive_manifest_sha256': sha(ARCHIVE / 'MANIFEST.json'), 'controller_sha256': sha(REPO / 'pipelines/quantum_formalize/dag_runner.py'), 'inputs': inputs, 'retrieval_policy': 'Historical successful first-attempt dual-library receipts, verbatim; for identical query lists choose the lexicographically first source node. No fresh retrieval claim.', 'status': 'prepared', 'fresh_kernel_checks': False}
    save(HERE / 'replay_prepared.json', provenance)
    if not execute:
        print(json.dumps({'status': 'prepared', 'verified_accepted_drafts': len(drafts), 'model_calls': 0}))
        return
    parent = Path(tempfile.mkdtemp(prefix='replay-accepted-', dir=PROJECT / '.humanize-formal-runs'))
    output = parent / 'experiment'
    print(json.dumps({'status': 'replaying', 'work': str(output), 'model_calls': 0}), flush=True)
    calls, searches = [], []
    async def propose(node, prompt, attempt):
        assert node.id not in calls, 'Replay must not invent another proof round'
        calls.append(node.id)
        return copy.deepcopy(drafts[node.id])
    async def search(queries):
        sources = retrievals[tuple(queries)]
        source = sorted(sources, key=lambda x: x['node'])[0]
        searches.append({'queries': queries, 'historical_source': source['path'], 'source_sha256': source['sha256'], 'fresh_search': False})
        return copy.deepcopy(source['receipts'])
    os.environ['PATH'] = '/home/jing/.elan/bin:' + os.environ.get('PATH', '')
    result = await run_graph(HERE / 'graph.json', PROJECT, output, propose, concurrency=16, rounds=1, timeout=180, search=search)
    provenance.update(status='finished', work=str(output), fresh_kernel_checks=True, replayed_nodes=calls, retrieval_replays=searches, result=result)
    save(parent / 'REPLAY_PROVENANCE.json', provenance)
    save(HERE / 'REPLAY.json', provenance)
    print(json.dumps(result))
    assert result['experiment_passed'], 'Fresh kernel replay or final assembly failed; inspect preserved output'

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', action='store_true')
    args = parser.parse_args()
    asyncio.run(main(args.run))
