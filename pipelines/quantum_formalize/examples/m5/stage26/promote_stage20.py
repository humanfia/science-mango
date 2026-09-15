"""Verify accepted archives and compose their exact declarations, without proving new goals."""
import hashlib
import json
import re
import shutil
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[5]))
from pipelines.quantum_formalize.dag_runner import portable_declaration
from pipelines.quantum_formalize.engine import Spec

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
PROJECT = Path('/home/jing/m5-lean-anchored-count-formalization')
STAGES = ['stage20']

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, ensure_ascii=False).encode()).hexdigest()

def save(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')

PROJECT.mkdir(exist_ok=True)
(HERE / 'lean').mkdir(exist_ok=True)
modules, entries, imported, declarations = {}, [], {}, {}
for stage in STAGES:
    directory = BASE / stage
    experiment = directory / ('experiment' if stage else 'experiments/accepted')
    result = json.loads((experiment / 'result.json').read_text())
    assert result['experiment_passed'] and result['assembly_accepted']
    state = json.loads((experiment / 'nodes/state.json').read_text())
    graph_specs = {n['id']: n['spec'] for n in json.loads((experiment / 'graph.json').read_text())['nodes']}
    assembly = (experiment / 'AcceptedExperiment.lean').read_text()
    accepted = [(key, value) for key, value in state['nodes'].items() if value.get('accepted')]
    accepted.sort(key=lambda kv: assembly.index('theorem ' + kv[1]['result']['target'] + ' :'))
    for node, record in accepted:
        receipt = record['result']
        assert json.loads((experiment / 'nodes' / node / 'receipt.json').read_text()) == record
        artifact = receipt['artifacts'][node]
        payload = artifact['payload']
        assert digest(payload) == artifact['sha256']
        last = receipt['attempts'][-1]
        assert last['accepted'] and set(last['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
        area = experiment / 'node_runs' / node / Path(last['proof_path']).parent.name
        candidate = area / Path(last['proof_path']).name
        target = area / Path(last['target_path']).name
        assert sha(candidate) == last['source_sha256']
        assert sha(target) == last['target_sha256']
        spec = json.loads((experiment / 'nodes' / node / 'resolved-spec.json').read_text())
        assert digest(graph_specs[node]) == payload['spec_sha256']
        assert spec['statement'] == graph_specs[node]['statement']
        frozen = ''.join(f'import {x}\n' for x in spec['imports']) + '\n' + spec['context'] + '\ndef QuantumHarnessFrozenTarget : Prop :=\n' + '\n'.join('  ' + line for line in spec['statement'].splitlines()) + '\n'
        assert target.read_text() == frozen
        draft = json.loads((area / 'draft.json').read_text())['proof']
        body = '\n'.join('  ' + line for line in draft.splitlines())
        assert candidate.read_text() == f'import {target.stem}\ntheorem {spec["name"]} : QuantumHarnessFrozenTarget := by\n{body}\n'
        declaration = portable_declaration(Spec.model_validate(spec), draft)
        assert declaration == payload['declaration'] and declaration in assembly
        assert spec['name'] not in declarations
        declarations[spec['name']] = declaration
        olean_checks = {}
        for field, original in [('olean_sha256', Path(last['proof_path']).with_suffix('.olean')), ('target_olean_sha256', Path(last['target_path']).with_suffix('.olean'))]:
            if original.exists():
                assert sha(original) == last[field]
                olean_checks[field] = 'original verified'
            else:
                olean_checks[field] = 'original unavailable; global checkpoint recompiles exact source'
        entries.append({'stage': stage or 'stage1', 'node': node, 'name': spec['name'], 'payload_sha256': artifact['sha256'], 'declaration_sha256': hashlib.sha256(declaration.encode()).hexdigest(), 'receipt': str((experiment / 'nodes' / node / 'receipt.json').relative_to(BASE)), 'receipt_sha256': sha(experiment / 'nodes' / node / 'receipt.json'), 'candidate': str(candidate.relative_to(BASE)), 'source_sha256': sha(candidate), 'target': str(target.relative_to(BASE)), 'target_sha256': sha(target), 'olean_verification': olean_checks})

assert len(declarations) == 6
source = 'import M5ArithmeticSubset\n\n' + '\n\n'.join(declarations.values()) + '\n'
(HERE / 'lean/M5ArithmeticSubsetAccepted.lean').write_text(source)
save(HERE/'STAGE20_DEPENDENCY_IMPORT.json', {'accepted':True,'theorem_count':6,'source_sha256':hashlib.sha256(source.encode()).hexdigest(),'theorems':entries,'proofs_modified':False})
print('Verified six accepted stage20 proofs and their exact dependency closure')
