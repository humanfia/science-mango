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
PROJECT = Path('/home/jing/m5-lean-integrated90-formalization')
STAGES = ['', 'stage2', 'stage3', 'stage4', 'stage5', 'stage6', 'stage7', 'stage8', 'stage9', 'stage10', 'stage11', 'stage12', 'stage13', 'stage14', 'stage15', 'stage17', 'stage18']

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
checkpoint = BASE / 'integrated72'
base_provenance = json.loads((checkpoint / 'PROVENANCE.json').read_text())
manifest = json.loads((checkpoint / 'MANIFEST.json').read_text())
for name, expected in manifest['files'].items():
    assert sha(checkpoint / name) == expected
assert json.loads((checkpoint / 'VALIDATION.json').read_text())['accepted']
for entry in base_provenance['theorems']:
    assert hashlib.sha256(declarations[entry['name']].encode()).hexdigest() == entry['declaration_sha256']
for path in (checkpoint / 'lean').glob('*.lean'):
    if path.name != 'Acceptance.lean':
        modules[path.name] = path
assert sha(modules['M5Checkpoint72.lean']) == base_provenance['integrated_source_sha256']
for stage, name in [('stage14','M5SubsetCharacter.lean'),('stage15','M5TupleCharacter.lean'),('stage17','M5FiniteExclusion.lean'),('stage18','M5FactorProduct.lean')]:
    modules[name] = BASE / stage / 'lean' / name
# Stage18 imports a promoted pair of declarations already accepted in checkpoint72.
binary_source = (BASE / 'stage18/lean/M5BinaryDivisibility.lean').read_text()
for name in ['M5.Signature.binary_monic','M5.Signature.binary_dvd_antisymm']:
    assert declarations[name] in binary_source
for name,path in modules.items():
    shutil.copy2(path,PROJECT/name)
    shutil.copy2(path,HERE/'lean'/name)
for root in [PROJECT,HERE/'lean']:
    (root/'M5BinaryDivisibility.lean').write_text('import M5Checkpoint72\n')
base_names = {e['name'] for e in base_provenance['theorems']}
source='\n'.join('import '+Path(name).stem for name in sorted(modules))+'\n\n'
source+='\n\n'.join(text for name,text in declarations.items() if name not in base_names)
source+='\n\n'+'\n'.join('#print axioms '+name for name in declarations)+'\n'
for root in [PROJECT,HERE/'lean']:
    (root/'M5Checkpoint90.lean').write_text(source)
    for name in ['lean-toolchain','lake-manifest.json']:
        shutil.copy2(checkpoint/'lean'/name,root/name)
lake=(checkpoint/'lean/lakefile.toml').read_text().replace('defaultTargets = ["M5Checkpoint72"]','defaultTargets = ["M5Checkpoint90"]')
for name in ['M5SubsetCharacter','M5TupleCharacter','M5FiniteExclusion','M5FactorProduct','M5BinaryDivisibility','M5Checkpoint90']:
    lake+='\n[[lean_lib]]\nname = '+json.dumps(name)+'\n'
for root in [PROJECT,HERE/'lean']:
    (root/'lakefile.toml').write_text(lake)
(PROJECT/'.lake').mkdir(exist_ok=True)
cache=PROJECT/'.lake/packages'
if not cache.exists():cache.symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
assert len(declarations)==90
save(HERE/'PROVENANCE.json',{'natural_language_source_sha256':base_provenance['natural_language_source_sha256'],'lean_toolchain':(PROJECT/'lean-toolchain').read_text().strip(),'mathlib_revision':base_provenance['mathlib_revision'],'theorem_count':90,'declared_here':18,'imported_verified_count':72,'base_source_sha256':sha(PROJECT/'M5Checkpoint72.lean'),'base_manifest_sha256':sha(checkpoint/'MANIFEST.json'),'source_modules':{name:{'source':str(path.relative_to(BASE)),'sha256':sha(path)} for name,path in modules.items()},'theorems':entries,'integrated_source_sha256':sha(PROJECT/'M5Checkpoint90.lean'),'proofs_modified':False,'portable_alias_wrapper':'dag_runner.portable_declaration preserves exact draft with local reducible alias when necessary','module_adjustments':['stage18 M5BinaryDivisibility forwards import M5Checkpoint72; its two promoted proofs are identical to existing accepted declarations'],'m5_formalized':False})
print(json.dumps({'theorems':90,'declared':18,'imported':72,'project':str(PROJECT)}))
