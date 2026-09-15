from pathlib import Path
import json,hashlib,subprocess,sys
H=Path(__file__).resolve().parent;P=Path('/home/jing/m6-lean-euclid-storage-formalization');sys.path.insert(0,str(H.parents[4]))
from pipelines.quantum_formalize.dag_runner import load_graph
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
g,nodes=load_graph(H/'graph.json');assert len(nodes)==13 and all(not n.spec['context'] for n in nodes)
promo=json.loads((H/'PROMOTION.json').read_text());assert promo['verified_count']==21
assert sha(P/'M6EuclidAccepted.lean')==promo['module_sha256']
for n in ['M6EuclidStorage.lean','M6Euclid.lean','M6EuclidAccepted.lean']:assert (P/n).read_bytes()==(H/'lean'/n).read_bytes()
for cmd,log in [(['build','M6EuclidStorage','M6EuclidAccepted'],'build.log'),(['env','lean','GraphPreflight.lean'],'preflight.log')]:
 r=subprocess.run(['/home/jing/.elan/bin/lake',*cmd],cwd=P,capture_output=True,text=True,timeout=600);(H/log).write_text(r.stdout+r.stderr);assert r.returncode==0,r.stdout+r.stderr
out={'accepted':True,'kind':'definitions and thirteen exact frozen target types; no new proofs at preflight','project':str(P),'graph_sha256':sha(H/'graph.json'),'definition_sha256':sha(H/'lean/M6EuclidStorage.lean'),'verified_imported_proofs':21,'contexts_empty':True,'pending_dependencies':[],'ready_for_live_experiment':True}
(H/'PREFLIGHT.json').write_text(json.dumps(out,indent=2)+'\n');(H/'DEPENDENCY_GATE.json').write_text(json.dumps({'ready_for_live_experiment':True,'pending':[],'resolved_by':promo},indent=2)+'\n');print(json.dumps(out))
