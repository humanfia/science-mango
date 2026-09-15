"""Full import gate: exact proof provenance, module compilation and dependency axiom audit."""
from pathlib import Path
import sys,subprocess,json,hashlib,re
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H.parents[4]))
from pipelines.quantum_formalize.dag_runner import load_graph
P=Path('/home/jing/m5-lean-polynomial-indicator-formalization')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
g,nodes=load_graph(H/'graph.json')
assert len(nodes)==3 and all(x.spec and not x.spec['context'] for x in nodes)
proof=json.loads((H/'STAGE16_DEPENDENCY_IMPORT.json').read_text())
assert proof['accepted'] and proof['theorem_count']==6
assert sha(H/'lean/M5PolynomialExclusionAccepted.lean')==proof['source_sha256']
b=subprocess.run(['/home/jing/.elan/bin/lake','build','M5PolynomialIndicator','M5PolynomialExclusionAccepted'],cwd=P,capture_output=True,text=True,timeout=600)
(H/'build.log').write_text(b.stdout+b.stderr);assert b.returncode==0,b.stdout+b.stderr
r=subprocess.run(['/home/jing/.elan/bin/lake','env','lean','GraphPreflight.lean'],cwd=P,capture_output=True,text=True,timeout=180)
(H/'preflight.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stdout+r.stderr
lines=['import M5PolynomialIndicator','import M5PolynomialExclusionAccepted']
for entry in proof['theorems']:
 receipt=json.loads((H.parent/entry['receipt']).read_text())
 declaration=receipt['result']['artifacts'][entry['node']]['payload']['declaration']
 statement=declaration.split(' : ',1)[1].split(' := by\n',1)[0]
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
result={'accepted':True,'kind':'definitions_and_frozen_target_types_only','project':str(P),'graph_sha256':sha(H/'graph.json'),'preflight_source_sha256':sha(H/'lean/GraphPreflight.lean'),'definition_sha256':sha(H/'lean/M5PolynomialIndicator.lean'),'graph_loader_passed':True,'contexts_empty':True,'frozen_target_count':3,'pending_dependencies':[],'ready_for_full_experiment':True,'new_theorems_proved':0,'build_log_sha256':sha(H/'build.log'),'preflight_log_sha256':sha(H/'preflight.log'),'dependency_exact_type_axiom_audit_passed':True,'dependency_axiom_audit_sha256':sha(H/'dependency-audit.log'),'stage16_proof_provenance_sha256':sha(H/'STAGE16_DEPENDENCY_IMPORT.json'),'m5_formalized':False}
(H/'PREFLIGHT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
