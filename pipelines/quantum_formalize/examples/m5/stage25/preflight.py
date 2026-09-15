"""Verify immutable imports, compile definitions and exact target propositions."""
from pathlib import Path
import sys,subprocess,json,hashlib,shutil
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H.parents[4]))
from pipelines.quantum_formalize.dag_runner import load_graph
P=Path('/home/jing/m5-lean-physical-order-formalization')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
g,nodes=load_graph(H/'graph.json')
assert len(nodes)==3 and all(n.spec and not n.spec['context'] for n in nodes)
imports=json.loads((H/'DEPENDENCY_IMPORT.json').read_text())
for name,value in imports['copied_files'].items():
 if name!='lakefile.toml':assert sha(P/name)==value
assert 'Build completed successfully' in (P/'preflight-build.log').read_text()
r=subprocess.run(['/home/jing/.elan/bin/lake','env','lean','GraphPreflight.lean'],cwd=P,capture_output=True,text=True,timeout=180)
(H/'preflight-types.log').write_text(r.stdout+r.stderr)
assert r.returncode==0,r.stdout+r.stderr
shutil.copy2(P/'preflight-build.log',H/'preflight-build.log')
result={'accepted':True,'kind':'definitions_and_exact_target_types_only','project':str(P),'graph_sha256':sha(H/'graph.json'),'target_count':3,'contexts_empty':True,'graph_loader_passed':True,'dependency_checkpoint':90,'dependency_provenance_sha256':sha(H/'DEPENDENCY_IMPORT.json'),'ready_for_full_experiment':True,'new_theorems_proved':0,'m5_formalized':False}
(H/'PREFLIGHT.json').write_text(json.dumps(result,indent=2)+'\n')
(H/'MANIFEST.json').write_text(json.dumps({'files':{str(f.relative_to(H)):sha(f) for f in sorted(H.rglob('*')) if f.is_file() and f.name!='MANIFEST.json'}},indent=2)+'\n')
print(json.dumps(result))
