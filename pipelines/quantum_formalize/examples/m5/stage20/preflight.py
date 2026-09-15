"""Compile definitions and the six exact target propositions; no new proofs."""
from pathlib import Path
import sys,subprocess,json,hashlib
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H.parents[4]))
from pipelines.quantum_formalize.dag_runner import load_graph
P=Path('/home/jing/m5-lean-arithmetic-subset-formalization')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
g,nodes=load_graph(H/'graph.json')
assert len(nodes)==6 and sum(x.spec is not None for x in nodes)==6
assert all(not x.spec['context'] for x in nodes if x.spec is not None)
b=subprocess.run(['/home/jing/.elan/bin/lake','build','M5ArithmeticSubset'],cwd=P,capture_output=True,text=True,timeout=600)
(H/'build.log').write_text(b.stdout+b.stderr)
assert b.returncode==0,b.stdout+b.stderr
r=subprocess.run(['/home/jing/.elan/bin/lake','env','lean','GraphPreflight.lean'],cwd=P,capture_output=True,text=True,timeout=180)
(H/'preflight.log').write_text(r.stdout+r.stderr)
assert r.returncode==0,r.stdout+r.stderr
audit='import M5ArithmeticSubset\n\n' + '\n'.join('#print axioms M5.SubsetCharacter.'+name for name in ['value_zero','character_subset_sum','signed_product_expansion','signed_product_coefficient','subset_character_count'])+'\n'
(P/'DependencyAudit.lean').write_text(audit)
(H/'lean/DependencyAudit.lean').write_text(audit)
a=subprocess.run(['/home/jing/.elan/bin/lake','env','lean','DependencyAudit.lean'],cwd=P,capture_output=True,text=True,timeout=180)
(H/'dependency-audit.log').write_text(a.stdout+a.stderr)
assert a.returncode==0,a.stdout+a.stderr
import re
axioms=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',a.stdout)
assert len(axioms)==5
assert all(set(x.strip() for x in line.split(',')) <= {'propext','Classical.choice','Quot.sound'} for line in axioms)
result={'accepted':True,'kind':'definitions_and_frozen_target_types_only','project':str(P),'graph_sha256':sha(H/'graph.json'),'preflight_source_sha256':sha(H/'lean/GraphPreflight.lean'),'definition_sha256':sha(H/'lean/M5ArithmeticSubset.lean'),'graph_loader_passed':True,'contexts_empty':True,'frozen_target_count':6,'pending_dependencies':[],'ready_for_full_experiment':True,'new_theorems_proved':0,'build_log_sha256':sha(H/'build.log'),'preflight_log_sha256':sha(H/'preflight.log'),'dependency_axiom_audit_passed':True,'dependency_axiom_audit_sha256':sha(H/'dependency-audit.log'),'stage14_proof_provenance_sha256':sha(H/'STAGE14_DEPENDENCY_IMPORT.json'),'m5_formalized':False}
(H/'PREFLIGHT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
