"""Verify accepted archives and compose their exact declarations, without proving new goals."""
import hashlib
import json
import re
import shutil
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE.parent.parent
PROJECT = Path('/home/jing/m5-lean-integrated-formalization')
STAGES = ['', 'stage2', 'stage3', 'stage4', 'stage5', 'stage6', 'stage9']

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
        declaration = f'theorem {spec["name"]} : {spec["statement"]} := by\n{body}'
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
    for path in (directory / 'lean').glob('*.lean'):
        if path.name in modules:
            assert modules[path.name].read_bytes() == path.read_bytes()
        else:
            modules[path.name] = path

for name, path in modules.items():
    content = path.read_text()
    names = re.findall(r'^theorem (\S+) :', content, re.M)
    for theorem in names:
        assert theorem in declarations and declarations[theorem] in content
        assert theorem not in imported
        imported[theorem] = name
    shutil.copy2(path, PROJECT / name)
    shutil.copy2(path, HERE / 'lean' / name)

source = '\n'.join('import ' + Path(name).stem for name in sorted(modules)) + '\n\n'
source += '\n\n'.join(text for name, text in declarations.items() if name not in imported)
source += '\n\n' + '\n'.join('#print axioms ' + name for name in declarations) + '\n'
(PROJECT / 'M5Accepted.lean').write_text(source)
(HERE / 'lean' / 'M5Accepted.lean').write_text(source)
for name in ['lean-toolchain', 'lake-manifest.json']:
    shutil.copy2(BASE / 'lean' / name, PROJECT / name)
    shutil.copy2(BASE / 'lean' / name, HERE / 'lean' / name)
lake = (BASE / 'lean' / 'lakefile.toml').read_text().replace('defaultTargets = ["M5Foundation"]', 'defaultTargets = ["M5Accepted"]')
for name in sorted(modules) + ['M5Accepted.lean']:
    if name != 'M5Foundation.lean':
        lake += '\n[[lean_lib]]\nname = ' + json.dumps(Path(name).stem) + '\n'
(PROJECT / 'lakefile.toml').write_text(lake)
(HERE / 'lean' / 'lakefile.toml').write_text(lake)
(PROJECT / '.lake').mkdir(exist_ok=True)
cache = PROJECT / '.lake/packages'
if not cache.exists():
    cache.symlink_to('/home/jing/lean-1st-proof/.lake/packages', target_is_directory=True)
assert len(declarations) == 41
save(HERE / 'PROVENANCE.json', {'natural_language_source_sha256': 'a7c0e2ae5f555864340f4b3e6d6674e5b2e74abf382ca5de4d3e5d68da6951a3', 'lean_toolchain': (PROJECT / 'lean-toolchain').read_text().strip(), 'mathlib_revision': 'de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11', 'theorem_count': len(declarations), 'declared_here': len(declarations) - len(imported), 'imported_verified': imported, 'source_modules': {name: {'source': str(path.relative_to(BASE)), 'sha256': sha(path)} for name, path in modules.items()}, 'theorems': entries, 'integrated_source_sha256': sha(PROJECT / 'M5Accepted.lean'), 'proofs_modified': False, 'm5_formalized': False})
print(json.dumps({'theorems': len(declarations), 'declared': len(declarations) - len(imported), 'imported': len(imported), 'project': str(PROJECT)}))
