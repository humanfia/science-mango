from pathlib import Path
import json,hashlib,shutil,sys,re
H=Path(__file__).resolve().parent;R=H.parents[4];P=Path('/home/jing/m7-lean-final-selector-formalization')
parents=[('generated_family','M7GeneratedFamilyAccepted'),('streaming_indices','M7StreamingIndicesAccepted'),('query_sectors','M7QuerySectorsAccepted'),('global_query','M7GlobalQueryAccepted'),('query_rebase','M7QueryRebaseAccepted')]
# Verify every parent final gate before creating the project.
for stage,module in parents:
 a=H.parent/stage/'experiment';r=json.loads((a/'result.json').read_text());assert all(r[k] for k in ['experiment_passed','assembly_accepted','environment_unchanged'])
(H/'lean').mkdir(exist_ok=True);P.mkdir(exist_ok=True);(P/'.lake').mkdir(exist_ok=True)
if not(P/'.lake/packages').exists():(P/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
sys.path.insert(0,str(R))
from pipelines.quantum_formalize.engine import Spec,render,digest
from pipelines.quantum_formalize.accepted_order import order_only_equivalent
from pipelines.quantum_formalize.dag_runner import load_graph,portable_declaration
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();provs={};order_reconciliations=[]
def promote(source, name, parent):
 dest=P/name
 if dest.exists() and dest.read_bytes()!=source.read_bytes():
  assert name.endswith('Accepted.lean') and order_only_equivalent(dest.read_text(),source.read_text()), ('source collision',parent,name)
  order_reconciliations.append({'module':name,'parent':parent,'kept_sha256':sha(dest),'incoming_sha256':sha(source),'rule':'exact theorem names and complete bodies; import multiset identical; only declaration order and allowed local #print axioms differ'})
  return
 for d in [P,H/'lean']:(d/name).write_bytes(source.read_bytes())
for stage,module in parents:
 B=H.parent/stage;A=B/'experiment';m=json.loads((A/'MANIFEST.json').read_text());files=m.get('files',m);assert all(sha(A/n)==v for n,v in files.items());res=json.loads((A/'result.json').read_text());assert all(res[k] for k in ['experiment_passed','assembly_accepted','environment_unchanged']);env=json.loads((A/'environment.json').read_text());g,nodes=load_graph(A/'graph.json');s=json.loads((A/'nodes/state.json').read_text());proofs={}
 for n in nodes:
  rec=s['nodes'][n.id];assert rec==json.loads((A/'nodes'/n.id/'receipt.json').read_text()) and rec['accepted'];r=rec['result'];a=r['attempts'][-1];f=A/'node_runs'/n.id/Path(a['proof_path']).parent.name;spec=Spec.model_validate(json.loads((A/'nodes'/n.id/'resolved-spec.json').read_text()));d=json.loads((f/'draft.json').read_text());assert spec.statement==n.spec['statement'];assert sha(f/Path(a['proof_path']).name)==a['source_sha256'];assert sha(f/Path(a['target_path']).name)==a['target_sha256'];assert (f/Path(a['proof_path']).name).read_text()==render(spec,d['proof'],Path(a['target_path']).stem);art=r['artifacts'][n.id];assert digest(art['payload'])==art['sha256'];assert digest(n.spec)==art['payload']['spec_sha256'];assert portable_declaration(spec,d['proof'])==art['payload']['declaration'];proofs[n.id]=art['sha256']
 for f in (B/'lean').glob('*.lean'):
  if f.name not in env:continue
  assert sha(f)==env[f.name]
  if f.stem in ['GraphPreflight','Preflight']:
   for q in list((B/'lean').glob('*.lean'))+[A/'AcceptedExperiment.lean']:
    if q.name in env or q==A/'AcceptedExperiment.lean':assert f.stem not in [t for line in re.findall(r'(?m)^\s*import\s+([^\n]+)',q.read_text())for t in line.split()]
   continue
  promote(f,f.name,stage)
 f=A/'AcceptedExperiment.lean'
 promote(f,module+'.lean',stage)
 provs[stage]={'canonical_manifest_sha256':sha(A/'MANIFEST.json'),'verified_count':len(nodes),'source_environment_verified':True,'accepted_module_sha256':sha(f),'nodes':proofs}

for name in ['M7FinalSelector.lean','GraphPreflight.lean']:
 for d in [P,H/'lean']:shutil.copy2(H/'planned'/name,d/name)
for name in ['lake-manifest.json','lean-toolchain']:
 for d in [P,H]:shutil.copy2(H.parent/'query_sectors'/name,d/name)
for stage in ['generated-family','query-sectors','streaming-indices']:
 c=Path('/home/jing/m7-lean-'+stage+'-formalization/.lake/build')
 if c.exists():shutil.copytree(c,P/'.lake/build',dirs_exist_ok=True)
lake='name = "M7FinalSelectorProject"\nversion = "0.1.0"\ndefaultTargets = ["M7FinalSelector"]\n[[require]]\nname = "mathlib"\ngit = "https://github.com/leanprover-community/mathlib4.git"\nrev = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"\n'
for f in sorted(P.glob('*.lean')):
 if f.stem!='GraphPreflight':lake+='\n[[lean_lib]]\nname = "'+f.stem+'"\n'
for d in [P,H]:(d/'lakefile.toml').write_text(lake)
(H/'ORDER_ONLY_RECONCILIATIONS.json').write_text(json.dumps(order_reconciliations,indent=2)+'\n')
(H/'IMPORT_PROVENANCE.json').write_text(json.dumps(provs,indent=2)+'\n')
(H/'DEPENDENCY_GATE.json').write_text(json.dumps({'resolved':True,'pending':[],'all_parent_receipts_and_payloads_verified':True,'normal_closed_type_preflight_required':True},indent=2)+'\n')
print('parents verified',sum(v['verified_count']for v in provs.values()))
