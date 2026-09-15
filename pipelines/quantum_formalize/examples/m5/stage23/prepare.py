"""Prepare frozen definitions; full experiment remains gated on accepted stage16 imports."""
from pathlib import Path
import json,hashlib,shutil
H=Path(__file__).resolve().parent; B=H.parent
P=Path('/home/jing/m5-lean-polynomial-indicator-formalization')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
checkpoint=B/'integrated90'
for name,digest in json.loads((checkpoint/'MANIFEST.json').read_text())['files'].items():assert sha(checkpoint/name)==digest
v=json.loads((checkpoint/'VALIDATION.json').read_text());assert v['accepted'] and v['theorem_count']==90
P.mkdir(exist_ok=True)
files={}
for p in (checkpoint/'lean').iterdir():
 if p.is_file() and p.name!='Acceptance.lean':
  shutil.copy2(p,P/p.name);shutil.copy2(p,H/'lean'/p.name);files[p.name]=sha(p)
p=B/'stage16/lean/M5PolynomialExclusion.lean';shutil.copy2(p,P/p.name);shutil.copy2(p,H/'lean'/p.name);files[p.name]=sha(p)
shutil.copy2(H/'lean/M5PolynomialIndicator.lean',P/'M5PolynomialIndicator.lean')
lake=(checkpoint/'lean/lakefile.toml').read_text().replace('defaultTargets = ["M5Checkpoint90"]','defaultTargets = ["M5PolynomialIndicator"]')
for name in ['M5PolynomialExclusion','M5PolynomialIndicator']:
 lake+='\n[[lean_lib]]\nname = '+json.dumps(name)+'\n'
for root in [P,H/'lean']:(root/'lakefile.toml').write_text(lake)
(P/'.lake').mkdir(exist_ok=True)
if not (P/'.lake/packages').exists():(P/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
g=json.loads((H/'graph.json').read_text())
s='import M5PolynomialIndicator\n\n'
for node in g['nodes']:
 spec=node['spec'];assert not spec['context']
 s+='noncomputable def M5.Stage23Target.'+node['id']+' : Prop :=\n  '+spec['statement']+'\n\n#check M5.Stage23Target.'+node['id']+'\n\n'
for root in [P,H/'lean']:(root/'GraphPreflight.lean').write_text(s)
(H/'DEPENDENCY_IMPORT.json').write_text(json.dumps({'checkpoint':'../integrated90','checkpoint_manifest_sha256':sha(checkpoint/'MANIFEST.json'),'checkpoint_validation_sha256':sha(checkpoint/'VALIDATION.json'),'accepted_theorems':90,'copied_files':files,'stage16_definitions_sha256':sha(p),'stage16_proof_imported':False,'proofs_changed':False},indent=2)+'\n')
(H/'PREFLIGHT.json').write_text(json.dumps({'ready_for_full_experiment':False,'pending_dependencies':['stage16'],'graph_sha256':sha(H/'graph.json'),'new_theorems_proved':0,'m5_formalized':False},indent=2)+'\n')
print('Verified integrated90; stage16 proof gate remains pending')
