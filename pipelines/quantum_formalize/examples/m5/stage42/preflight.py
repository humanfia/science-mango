"""Check definitions, frozen targets and already accepted imports, with all accepted dependencies verified."""
from pathlib import Path
import json,hashlib,subprocess,sys,re
H=Path(__file__).resolve().parent;P=Path('/home/jing/m5-lean-conditional-residue-count-formalization')
sys.path.insert(0,str(H.parents[4]))
from pipelines.quantum_formalize.dag_runner import load_graph
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
g,nodes=load_graph(H/'graph.json')
assert len(nodes)==6 and sum(n.spec is not None for n in nodes)==6
assert all(not n.spec['context'] for n in nodes if n.spec)
b=subprocess.run(['/home/jing/.elan/bin/lake','build','M5ConditionalResidueCount'],cwd=P,capture_output=True,text=True,timeout=600)
(H/'build.log').write_text(b.stdout+b.stderr);assert b.returncode==0,b.stdout+b.stderr
r=subprocess.run(['/home/jing/.elan/bin/lake','env','lean','GraphPreflight.lean'],cwd=P,capture_output=True,text=True,timeout=180)
(H/'preflight.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stdout+r.stderr
proof=json.loads((H/'ACCEPTED_IMPORTS.json').read_text())
lines=['import M5ConditionalResidueCount']
for entry in proof['theorems']:
 rec=json.loads((H.parent/entry['receipt']).read_text())
 dec=rec['result']['artifacts'][entry['node']]['payload']['declaration']
 statement=dec.split(' : ',1)[1].split(' := by\n',1)[0]
 lines += [f'example : {statement} := {entry["name"]}',f'#print axioms {entry["name"]}']
s='\n\n'.join(lines)+'\n'
for root in [P,H/'lean']:(root/'DependencyAudit.lean').write_text(s)
a=subprocess.run(['/home/jing/.elan/bin/lake','env','lean','DependencyAudit.lean'],cwd=P,capture_output=True,text=True,timeout=180)
(H/'dependency-audit.log').write_text(a.stdout+a.stderr);assert a.returncode==0,a.stdout+a.stderr
for entry in proof['theorems']:
 matches=re.findall("'"+re.escape(entry['name'])+r"' depends on axioms:\s*\[([^\]]*)\]",a.stdout)
 empty=f"'{entry['name']}' does not depend on any axioms" in a.stdout
 assert len(matches)+int(empty)==1
 if matches:assert set(x.strip() for x in matches[0].split(','))<={'propext','Classical.choice','Quot.sound'}
out={'accepted':True,'kind':'definitions_and_frozen_target_types_only','project':str(P),'graph_sha256':sha(H/'graph.json'),'preflight_source_sha256':sha(H/'lean/GraphPreflight.lean'),'definition_sha256':sha(H/'lean/M5ConditionalResidueCount.lean'),'graph_loader_passed':True,'contexts_empty':True,'frozen_target_count':6,'pending_dependencies':[],'ready_for_full_experiment':True,'new_theorems_proved':0,'dependency_exact_type_axiom_audit_passed':True,'dependency_audit_sha256':sha(H/'dependency-audit.log'),'build_log_sha256':sha(H/'build.log'),'preflight_log_sha256':sha(H/'preflight.log'),'m5_formalized':False}
(H/'PREFLIGHT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
