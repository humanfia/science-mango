from pathlib import Path
import json,hashlib,subprocess,sys
H=Path(__file__).resolve().parent;P=Path('/home/jing/m7-lean-actual-presentation-formalization');sys.path.insert(0,str(H.parents[4]))
from pipelines.quantum_formalize.dag_runner import load_graph
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
g,nodes=load_graph(H/'graph.json');assert len(nodes)==9 and all(not n.spec['context'] for n in nodes)
assert (P/'M7ActualPresentation.lean').read_bytes()==(H/'lean/M7ActualPresentation.lean').read_bytes()
assert len(json.loads((H/'PROMOTION.json').read_text())['nodes'])==12
for cmd,log in [(['build','M7ActualPresentation','M7PresentationAccepted'],'build.log'),(['env','lean','GraphPreflight.lean'],'preflight.log')]:
 r=subprocess.run(['/home/jing/.elan/bin/lake',*cmd],cwd=P,capture_output=True,text=True,timeout=600);(H/log).write_text(r.stdout+r.stderr);assert r.returncode==0,r.stdout+r.stderr
out={'accepted':True,'kind':'definitions and nine exact target types only','project':str(P),'graph_sha256':sha(H/'graph.json'),'definition_sha256':sha(H/'lean/M7ActualPresentation.lean'),'contexts_empty':True,'pending_dependencies':[],'new_theorems_proved':0,'ready_for_live_experiment':True,'mathlib_revision':'de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11'}
(H/'PREFLIGHT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
