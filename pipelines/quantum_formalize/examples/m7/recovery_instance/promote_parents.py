from pathlib import Path
import json,hashlib,shutil,sys
H=Path(__file__).resolve().parent
R=H.parents[4];P=Path('/home/jing/m7-lean-recovery-instance-formalization');sys.path.insert(0,str(R))
from pipelines.quantum_formalize.engine import Spec,render,digest
from pipelines.quantum_formalize.dag_runner import load_graph,portable_declaration
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
provs=json.loads((H/'IMPORT_PROVENANCE.json').read_text())
parents=[('prefix_orbit','M7PrefixOrbitAccepted'),('recovery_prefix','M7RecoveryPrefixAccepted')]
# Both canonical parents must exist and their recorded definition bodies must match before any mutation.
for stage,module in parents:
 B=H.parent/stage;A=B/'experiment'
 result=json.loads((A/'result.json').read_text());assert all(result[k] for k in ['experiment_passed','assembly_accepted','environment_unchanged'])
 definition=module.removesuffix('Accepted')+'.lean'
 assert sha(B/'lean'/definition)==provs[stage+'_pending_definition']['source_sha256']
for stage,module in parents:
 B=H.parent/stage;A=B/'experiment';m=json.loads((A/'MANIFEST.json').read_text());files=m.get('files',m);assert all(sha(A/n)==v for n,v in files.items());res=json.loads((A/'result.json').read_text());assert all(res[k] for k in ['experiment_passed','assembly_accepted','environment_unchanged']);env=json.loads((A/'environment.json').read_text());g,nodes=load_graph(A/'graph.json');s=json.loads((A/'nodes/state.json').read_text());proofs={}
 for n in nodes:
  rec=s['nodes'][n.id];assert rec==json.loads((A/'nodes'/n.id/'receipt.json').read_text()) and rec['accepted'];r=rec['result'];a=r['attempts'][-1];f=A/'node_runs'/n.id/Path(a['proof_path']).parent.name;spec=Spec.model_validate(json.loads((A/'nodes'/n.id/'resolved-spec.json').read_text()));d=json.loads((f/'draft.json').read_text());assert spec.statement==n.spec['statement'];assert sha(f/Path(a['proof_path']).name)==a['source_sha256'];assert sha(f/Path(a['target_path']).name)==a['target_sha256'];assert (f/Path(a['proof_path']).name).read_text()==render(spec,d['proof'],Path(a['target_path']).stem);art=r['artifacts'][n.id];assert digest(art['payload'])==art['sha256'];assert digest(n.spec)==art['payload']['spec_sha256'];assert portable_declaration(spec,d['proof'])==art['payload']['declaration'];proofs[n.id]=art['sha256']
 for f in (B/'lean').glob('*.lean'):
  if f.name not in env or f.name == 'GraphPreflight.lean':continue
  assert sha(f)==env[f.name]
  if (P/f.name).exists() and f.name not in ['M7PrefixOrbitAccepted.lean','M7RecoveryPrefixAccepted.lean']:assert(P/f.name).read_bytes()==f.read_bytes(),('definition collision',stage,f.name)
  shutil.copy2(f,P/f.name);shutil.copy2(f,H/'lean'/f.name)
 f=A/'AcceptedExperiment.lean'
 # Replace only preflight adapters with verified canonical assemblies.
 for dest in [P,H/'lean']:(dest/(module+'.lean')).write_bytes(f.read_bytes())
 provs[stage]={'canonical_manifest_sha256':sha(A/'MANIFEST.json'),'verified_count':len(nodes),'source_environment_verified':True,'accepted_module_sha256':sha(f),'nodes':proofs}

for stage,module in parents:provs[stage+'_pending_definition']['proof_gate_pending']=False
(H/'IMPORT_PROVENANCE.json').write_text(json.dumps(provs,indent=2)+'\n')
# Include every genuine source library, preserving the frozen own definitions/target types.
lake=(P/'lakefile.toml').read_text()
for f in sorted(P.glob('*.lean')):
 if f.stem!='GraphPreflight' and ('name = "'+f.stem+'"') not in lake:lake+='\n[[lean_lib]]\nname = "'+f.stem+'"\n'
(P/'lakefile.toml').write_text(lake);(H/'lakefile.toml').write_text(lake)
(H/'DEPENDENCY_GATE.json').write_text(json.dumps({'resolved':True,'pending':[],'canonical_parents_verified':[s for s,_ in parents],'normal_preflight_required_before_launch':True},indent=2)+'\n')
print('Verified and promoted both canonical parent closures; rerun full type/build preflight before freezing and launching.')
