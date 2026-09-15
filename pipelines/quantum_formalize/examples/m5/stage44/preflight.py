from pathlib import Path
import sys, subprocess, json, hashlib, shutil, re
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H.parents[4]))
from pipelines.quantum_formalize.dag_runner import load_graph
P=Path("/home/jing/m5-lean-prefix-partition-formalization")
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
g,nodes=load_graph(H/'graph.json')
assert 'Build completed successfully' in (P/'preflight-build.log').read_text()
for file in ['GraphPreflight.lean']:
 r=subprocess.run(['/home/jing/.elan/bin/lake','env','lean',file],cwd=P,capture_output=True,text=True,timeout=180)
 (H/(file+'.log')).write_text(r.stdout+r.stderr)
 assert r.returncode==0,r.stdout+r.stderr
 if file=='DependencyAudit.lean':
  axioms=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',r.stdout)
  assert len(axioms)==18, len(axioms)
  assert all(set(x.strip() for x in line.split(','))<={'propext','Classical.choice','Quot.sound'} for line in axioms)
shutil.copy2(P/'preflight-build.log',H/'preflight-build.log')
result={'accepted':True,'kind':'definitions_and_exact_target_types_only','project':str(P),'graph_sha256':sha(H/'graph.json'),'target_count':sum(n.spec is not None for n in nodes),'pending_import_gates':[n.id for n in nodes if n.spec is None],'new_theorems_proved':0,'m5_formalized':False}
(H/'PREFLIGHT.json').write_text(json.dumps(result,indent=2)+'\n')
(H/'MANIFEST.json').write_text(json.dumps({'files':{str(f.relative_to(H)):sha(f) for f in sorted(H.rglob('*')) if f.is_file() and f.name!='MANIFEST.json'}},indent=2)+'\n')
print(json.dumps(result))
