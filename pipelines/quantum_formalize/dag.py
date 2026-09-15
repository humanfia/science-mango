"""Dependency-aware, bounded scheduling for independently accepted declarations.

The executor owns Lean compilation and semantic review. This scheduler trusts only
its explicit boolean ``accepted`` receipt; finishing a graph is never, by itself,
a claim that the complete natural-language M5 theorem has been formalized.
"""
import asyncio
from copy import deepcopy
from dataclasses import dataclass, field
from datetime import datetime, timezone
import heapq
import json
import os
from pathlib import Path
import re
import tempfile


@dataclass(frozen=True)
class Node:
    id: str
    dependencies: tuple[str, ...] = ()
    spec: dict | None = None
    metadata: dict = field(default_factory=dict)


def validate(nodes):
    """Validate a graph and return a deterministic topological ordering."""
    nodes = list(nodes)
    ids = [node.id for node in nodes]
    if any(not isinstance(x, str) or not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_-]{0,127}', x) for x in ids):
        raise ValueError('node IDs must be safe, nonempty filesystem slugs')
    if len(ids) != len(set(ids)):
        raise ValueError('duplicate node ID')
    known = set(ids)
    children = {x: [] for x in ids}
    counts = {}
    for node in nodes:
        if len(node.dependencies) != len(set(node.dependencies)):
            raise ValueError(f'duplicate dependency for {node.id}')
        missing = set(node.dependencies) - known
        if missing:
            raise ValueError(f'missing dependencies for {node.id}: {sorted(missing)}')
        counts[node.id] = len(node.dependencies)
        for dep in node.dependencies:
            children[dep].append(node.id)
    ready = [x for x in ids if counts[x] == 0]
    heapq.heapify(ready)
    ordered = []
    while ready:
        current = heapq.heappop(ready)
        ordered.append(current)
        for child in sorted(children[current]):
            counts[child] -= 1
            if counts[child] == 0:
                heapq.heappush(ready, child)
    if len(ordered) != len(nodes):
        raise ValueError('dependency cycle')
    return ordered


def _save(path, value):
    """Atomically replace a flushed JSON receipt, including its directory entry."""
    path = Path(path)
    payload = json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + '\n'
    fd, temporary = tempfile.mkstemp(prefix='.' + path.name, dir=path.parent)
    try:
        with os.fdopen(fd, 'w') as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        directory = os.open(path.parent, os.O_DIRECTORY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


async def run_dag(nodes, executor, output_dir, max_concurrency=16):
    """Run executable nodes only after every dependency has been accepted.

    ``executor(node, dependency_receipts, node_dir)`` is an async callback returning
    a JSON-serializable dict with ``accepted is True`` on success. ``spec=None``
    denotes a planned node, never executable. The output directory must be fresh
    or empty; receipts are not silently reused as accepted proofs. Executors must
    cooperate with cancellation and reap any child processes they create.
    """
    if type(max_concurrency) is not int or not 1 <= max_concurrency <= 16:
        raise ValueError('max_concurrency must be an integer between 1 and 16')
    nodes = list(nodes)
    order = validate(nodes)
    by_id = {node.id: node for node in nodes}
    manifest = [{'id': node.id, 'dependencies': list(node.dependencies),
                 'spec': node.spec, 'metadata': node.metadata} for node in nodes]
    # Validate serialization before creating any output.
    json.dumps(manifest, allow_nan=False)
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    if any(output_dir.iterdir()):
        raise ValueError('DAG output directory must be empty; choose a new run directory')
    _save(output_dir / 'graph.json', manifest)
    records = {x: {'id': x, 'status': 'planned' if by_id[x].spec is None else 'pending',
                   'accepted': False} for x in order}
    tasks = {}

    def persist(run_status='running'):
        summary = {'status': run_status, 'max_concurrency': max_concurrency,
                   'updated_at': datetime.now(timezone.utc).isoformat(),
                   'all_nodes_accepted': bool(records) and all(r['status'] == 'accepted' for r in records.values()),
                   'm5_formalized': False, 'nodes': records}
        _save(output_dir / 'state.json', summary)
        return summary

    def update(node_id, status, **extra):
        records[node_id] = {'id': node_id, 'status': status,
                            'accepted': status == 'accepted', **extra}
        _save(output_dir / node_id / 'receipt.json', records[node_id])

    for node_id in order:
        (output_dir / node_id).mkdir()
        _save(output_dir / node_id / 'receipt.json', records[node_id])
    persist()

    async def execute(node_id):
        try:
            result = await executor(by_id[node_id],
                                    {d: deepcopy(records[d]) for d in by_id[node_id].dependencies},
                                    output_dir / node_id)
            if not isinstance(result, dict):
                raise ValueError('executor must return a JSON receipt dictionary')
            json.dumps(result, allow_nan=False)
            return result
        except asyncio.CancelledError:
            raise
        except Exception as error:
            return {'accepted': False, 'error': f'{type(error).__name__}: {error}'}

    try:
        while True:
            # Topological traversal propagates blocked ancestors in a single pass.
            for node_id in order:
                if records[node_id]['status'] != 'pending':
                    continue
                bad = [d for d in by_id[node_id].dependencies
                       if records[d]['status'] in {'failed', 'blocked', 'planned', 'cancelled'}]
                if bad:
                    update(node_id, 'blocked', blocked_by=bad)
            ready = sorted(x for x in order if records[x]['status'] == 'pending'
                           and all(records[d]['status'] == 'accepted' for d in by_id[x].dependencies))
            for node_id in ready[:max_concurrency - len(tasks)]:
                update(node_id, 'running')
                tasks[asyncio.create_task(execute(node_id), name=f'dag:{node_id}')] = node_id
            persist()
            if not tasks:
                break
            done, _ = await asyncio.wait(tasks, return_when=asyncio.FIRST_COMPLETED)
            for task in sorted(done, key=lambda t: tasks[t]):
                node_id = tasks.pop(task)
                if task.cancelled():
                    update(node_id, 'cancelled', reason='executor cancelled')
                else:
                    result = task.result()
                    update(node_id, 'accepted' if result.get('accepted') is True else 'failed', result=result)
        return persist('finished')
    except BaseException:
        for task in tasks:
            task.cancel()
        await asyncio.gather(*tasks, return_exceptions=True)
        for node_id in order:
            if records[node_id]['status'] in {'running', 'pending'}:
                update(node_id, 'cancelled', reason='DAG run interrupted; acceptance not recorded')
        persist('cancelled')
        raise
