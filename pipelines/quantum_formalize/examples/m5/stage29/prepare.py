from pathlib import Path
import json,hashlib,shutil
H=Path(__file__).resolve().parent;B=H.parent;P=Path('/home/jing/m5-lean-anchored-tuple-formalization');P.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();C=B/'integrated90'
for f,v in json.loads((C/'MANIFEST.json').read_text())['files'].items():assert sha(C/f)==v
v=json.loads((C/'VALIDATION.json').read_text());assert v['accepted'] and v['theorem_count']==90
copied={}
for f in (C/'lean').iterdir():
 if f.is_file() and f.name!='Acceptance.lean':
  shutil.copy2(f,P/f.name);shutil.copy2(f,H/'lean'/f.name);copied[f.name]=sha(f)
shutil.copy2(B/'stage24/lean/M5ArithmeticTuple.lean',H/'lean/M5ArithmeticTuple.lean')
for name in ['M5ArithmeticTuple','M5ArithmeticTupleAccepted','M5AnchoredTupleCount']:shutil.copy2(H/'lean'/f'{name}.lean',P/f'{name}.lean')
g=json.loads((H/'graph.json').read_text());pre='import M5AnchoredTupleCount\n\n'+'\n'.join('noncomputable def preflight_'+n['id']+' : Prop :=\n  '+n['spec']['statement']+'\n' for n in g['nodes'])
for f in [H/'lean/GraphPreflight.lean',P/'GraphPreflight.lean']:f.write_text(pre)
lake=(P/'lakefile.toml').read_text().replace('defaultTargets = ["M5Checkpoint90"]','defaultTargets = ["M5AnchoredTupleCount"]')
for name in ['M5ArithmeticTuple','M5ArithmeticTupleAccepted','M5AnchoredTupleCount']:lake+='\n[[lean_lib]]\nname = '+json.dumps(name)+'\n'
for f in [H/'lean/lakefile.toml',P/'lakefile.toml']:f.write_text(lake)
(P/'.lake').mkdir(exist_ok=True)
if not (P/'.lake/packages').exists():(P/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
(H/'DEPENDENCY_IMPORT.json').write_text(json.dumps({'checkpoint':'../integrated90','validation_sha256':sha(C/'VALIDATION.json'),'manifest_sha256':sha(C/'MANIFEST.json'),'copied_files':copied,'accepted_theorem_count':90,'stage24_proof_provenance_sha256':sha(H/'STAGE24_DEPENDENCY_IMPORT.json'),'arithmetic_tuple_definition_sha256':sha(H/'lean/M5ArithmeticTuple.lean'),'proofs_changed':False},indent=2)+'\n')
