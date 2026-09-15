from pathlib import Path
import json,hashlib,sys,shutil
H=Path(__file__).resolve().parent;BASE=H.parent;sys.path.insert(0,str(H.parents[4]))
from pipelines.quantum_formalize.engine import Spec,render,digest
from pipelines.quantum_formalize.dag_runner import portable_declaration
P=Path('/home/jing/m6-lean-recipe-isometries-formalization');P.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for filename,stage in [('M6Physical.lean','physical'),('M6Flatten.lean','flatten'),('M6Spaces.lean','spaces'),('M6SpacesReady.lean','spaces'),('M6Character.lean','character'),('M6Pinned.lean','pinned_recovery')]:
 p=BASE/stage/'lean'/filename;shutil.copy2(p,H/'lean'/filename);shutil.copy2(p,P/filename)
records={}
for stage,mod,imports in [('physical','M6PhysicalAccepted',['M6Physical']),('flatten','M6FlattenAccepted',['M6Flatten']),('spaces','M6SpacesAccepted',['M6SpacesReady'])]:
 A=BASE/stage/'experiment';m=json.loads((A/'MANIFEST.json').read_text());m=m.get('files',m)
 for name,h in m.items():assert sha(A/name)==h
 result=json.loads((A/'result.json').read_text());assert result['experiment_passed'] and result['assembly_accepted'] and result['environment_unchanged']
 state=json.loads((A/'nodes/state.json').read_text());specs={n['id']:n['spec']for n in json.loads((A/'graph.json').read_text())['nodes']};asm=(A/'AcceptedExperiment.lean').read_text();items=list(state['nodes'].items());items.sort(key=lambda x:asm.index('theorem '+x[1]['result']['target']+' :'))
 decs=[]
 for name,rec in items:
  assert rec['accepted'] and rec==json.loads((A/'nodes'/name/'receipt.json').read_text());r=rec['result'];last=r['attempts'][-1];folder=A/'node_runs'/name/Path(last['proof_path']).parent.name;spec=Spec.model_validate(json.loads((A/'nodes'/name/'resolved-spec.json').read_text()));assert spec.statement==specs[name]['statement'];draft=json.loads((folder/'draft.json').read_text());cand=folder/Path(last['proof_path']).name;target=folder/Path(last['target_path']).name
  assert sha(cand)==last['source_sha256'] and sha(target)==last['target_sha256'];assert cand.read_text()==render(spec,draft['proof'],target.stem)
  art=r['artifacts'][name];assert digest(art['payload'])==art['sha256'] and digest(specs[name])==art['payload']['spec_sha256'];dec=portable_declaration(spec,draft['proof']);assert dec==art['payload']['declaration'] and dec in asm;decs.append(dec)
  records[spec.name]={'stage':stage,'payload_sha256':art['sha256'],'source_sha256':last['source_sha256'],'target_sha256':last['target_sha256']}
 text=''.join('import '+i+'\n'for i in imports)+'\n'+'\n\n'.join(decs)+'\n';(H/'lean'/f'{mod}.lean').write_text(text);(P/f'{mod}.lean').write_text(text)
assert len(records)==30
(H/'PROMOTION.json').write_text(json.dumps({'accepted':True,'verified_declarations':30,'proofs_modified':False,'nodes':records,'module_hashes':{p.name:sha(p)for p in (H/'lean').glob('M6*.lean')}},indent=2)+'\n')
S=Path('/home/jing/m6-lean-euclid-formalization')
for n in ['lean-toolchain','lake-manifest.json']:shutil.copy2(S/n,P/n);shutil.copy2(S/n,H/'lean'/n)
mods=[p.stem for p in (H/'lean').glob('M6*.lean')]+['M6RecipeIsometries'];lake='name = "M6RecipeIsometriesProject"\nversion = "0.1.0"\ndefaultTargets = ["M6RecipeIsometries"]\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4.git"\nrev = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"\n'+''.join('\n[[lean_lib]]\nname = "'+m+'"\n'for m in dict.fromkeys(mods));(P/'lakefile.toml').write_text(lake);(H/'lean/lakefile.toml').write_text(lake)
(P/'.lake').mkdir(exist_ok=True);(P/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
print('Verified and promoted30 actual physical/flatten/space declarations unchanged')
