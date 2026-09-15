"""Bind DAG edges to real accepted Lean proof bodies, then compile their union."""
import asyncio
import hashlib
import json
from pathlib import Path

from .dag import Node, run_dag, validate
from .engine import Spec, command, digest, fingerprint, run, save, check_axiom_output, render
from .search import search_both


def load_graph(path):
    data = json.loads(Path(path).read_text())
    nodes = [Node(x['id'], tuple(x.get('dependencies', [])), x.get('spec'), x.get('metadata', {})) for x in data['nodes']]
    validate(nodes)
    names = [Spec.model_validate(n.spec).name for n in nodes if n.spec is not None]
    if len(names) != len(set(names)):
        raise ValueError('duplicate Lean declaration names')
    # Context is shared via immutable project imports and accepted dependencies.
    if any(n.spec and n.spec.get('context', '').strip() for n in nodes):
        raise ValueError('DAG node contexts must be empty; use a frozen shared foundation module')
    return data, nodes


def proof_context(dependencies):
    artifacts = {}
    for receipt in dependencies.values():
        if receipt.get('accepted') is not True:
            raise ValueError('dependency is not accepted')
        for key, value in receipt['result']['artifacts'].items():
            if key in artifacts and artifacts[key] != value:
                raise ValueError('inconsistent dependency proof')
            if digest(value['payload']) != value['sha256']:
                raise ValueError('dependency proof hash mismatch')
            artifacts[key] = value
    # Each artifact carries its complete transitive ancestor list.
    pending = dict(artifacts)
    ordered = []
    while pending:
        ready = sorted(k for k, v in pending.items() if set(v['payload']['ancestors']) <= set(ordered))
        if not ready:
            raise ValueError('invalid accepted dependency artifact graph')
        for key in ready:
            ordered.append(key)
            pending.pop(key)
    return artifacts, '\n\n'.join(artifacts[k]['payload']['declaration'] for k in ordered)


async def run_graph(graph_path, project, output, propose, *, concurrency=16, rounds=5,
                    timeout=180, search=None):
    graph, nodes = load_graph(graph_path)
    project, output = Path(project).resolve(), Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        raise ValueError('experiment directory must be empty')
    save(output/'graph.json', graph)
    original = fingerprint(project)
    imports = sorted({m for n in nodes if n.spec for m in Spec.model_validate(n.spec).imports})
    build = await asyncio.to_thread(command, ['lake', 'build', *imports], project, timeout)
    save(output/'build.json', build)
    if build['returncode'] != 0 or build['timed_out']:
        raise RuntimeError('shared imports failed preflight; see build.json')
    locked = fingerprint(project)
    if {k:v for k,v in original.items() if k != 'lake-manifest.json'} != {k:v for k,v in locked.items() if k != 'lake-manifest.json'}:
        raise ValueError('source changed during shared preflight')
    save(output/'environment.json', locked)
    retrieval_slots = asyncio.Semaphore(2)

    async def execute(node, dependencies, area):
        ancestors, context = proof_context(dependencies)
        spec = Spec.model_validate(node.spec).model_copy(update={'context': context})
        # Include ancestor imports, not just the immediate node's imports.
        inherited = {m for a in ancestors.values() for m in a['payload']['imports']}
        spec = spec.model_copy(update={'imports': sorted(set(spec.imports) | inherited)})
        save(area/'resolved-spec.json', spec.model_dump())
        if fingerprint(project) != locked:
            raise ValueError('shared project changed')
        async def node_propose(prompt, attempt):
            return await propose(node, prompt, attempt)
        history = []
        async def node_search(queries):
            async with retrieval_slots:
                provider = search_both if search is None else search
                receipts = await provider(queries)
                history.append({'queries': queries, 'receipts': receipts})
                save(area/'retrieval-history.json', history)
                if any(r['status'] != 'ok' for r in receipts):
                    fallback = node.metadata.get('fallback_queries', [])
                    if fallback:
                        receipts = await provider(fallback)
                        history.append({'queries': fallback, 'fallback_for': queries, 'receipts': receipts})
                        save(area/'retrieval-history.json', history)
                return receipts
        result = await run(spec, project, node_propose, max_rounds=rounds, timeout=timeout,
                           build=False, search=node_search)
        if result.get('accepted') is True:
            last = result['attempts'][-1]
            proof_file = Path(last['proof_path'])
            if hashlib.sha256(proof_file.read_bytes()).hexdigest() != last['source_sha256']:
                raise ValueError('accepted proof source changed')
            draft = json.loads((proof_file.parent/'draft.json').read_text())['proof']
            if render(spec, draft, Path(last['target_path']).stem) != proof_file.read_text():
                raise ValueError('draft does not match the compiled accepted proof')
            declaration = f'theorem {spec.name} : {spec.statement} := by\n' + '\n'.join('  '+line for line in draft.splitlines())
            payload = {'declaration': declaration, 'imports': spec.imports,
                       'name': spec.name, 'ancestors': sorted(ancestors),
                       'spec_sha256': digest(node.spec)}
            artifacts = dict(ancestors, **{node.id: {'payload': payload, 'sha256': digest(payload)}})
            result['artifacts'] = artifacts
            (area/'declaration.lean.txt').write_text(declaration+'\n')
        return result

    state = await run_dag(nodes, execute, output/'nodes', max_concurrency=concurrency)
    accepted = {k:v for k,v in state['nodes'].items() if v['accepted']}
    artifacts, context = proof_context(accepted)
    if artifacts:
        union = output/'AcceptedExperiment.lean'
        names = [a['payload']['name'] for a in artifacts.values()]
        union.write_text(''.join(f'import {m}\n' for m in imports)+'\n'+context+'\n'+
                         '\n'.join(f'#print axioms {name}' for name in names)+'\n')
        audit = await asyncio.to_thread(command, ['lake','env','lean',str(union)], project, timeout)
        save(output/'assembly-compile.json', audit)
        assembly_ok = audit['returncode'] == 0 and not audit['timed_out'] and all(check_axiom_output(audit['output'], name)[0] for name in names)
    else:
        assembly_ok = False
    result = {'status': 'finished', 'graph_sha256': digest(graph), 'max_concurrency': concurrency,
              'accepted_nodes': sorted(accepted), 'executable_nodes': sum(n.spec is not None for n in nodes),
              'planned_nodes': sum(n.spec is None for n in nodes), 'assembly_accepted': assembly_ok,
              'environment_unchanged': fingerprint(project) == locked,
              'experiment_passed': bool(accepted) and len(accepted) == sum(n.spec is not None for n in nodes) and assembly_ok and fingerprint(project) == locked,
              'm5_formalized': False, 'work': str(output)}
    save(output/'result.json', result)
    return result
