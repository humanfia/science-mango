from pathlib import Path
import json,hashlib,subprocess,sys
H=Path(__file__).resolve().parent;P=Path('/home/jing/m6-lean-pinned-recovery-formalization')
sys.path.insert(0,str(H.parents[4]))
from pipelines.quantum_formalize.dag_runner import load_graph
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
g,nodes=load_graph(H/'graph.json')
assert len(nodes)==14 and all(n.spec and not n.spec['context'] for n in nodes)
assert (H/'lean/M6Pinned.lean').read_bytes()==(P/'M6Pinned.lean').read_bytes()
for command,log in [(['build','M6Pinned'],'build.log'),(['env','lean','GraphPreflight.lean'],'preflight.log')]:
 r=subprocess.run(['/home/jing/.elan/bin/lake',*command],cwd=P,capture_output=True,text=True,timeout=600)
 (H/log).write_text(r.stdout+r.stderr);assert r.returncode==0,r.stdout+r.stderr
out={'accepted':True,'kind':'definitions and frozen target types only','project':str(P),'definition_sha256':sha(H/'lean/M6Pinned.lean'),'graph_sha256':sha(H/'graph.json'),'frozen_target_count':14,'graph_loader_passed':True,'contexts_empty':True,'pending_dependencies':[],'ready_for_full_experiment':True,'imported_theorem_assumptions':[],'mathlib_revision':'de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11','new_theorems_proved':0,'build_log_sha256':sha(H/'build.log'),'target_type_log_sha256':sha(H/'preflight.log')}
(H/'PREFLIGHT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
