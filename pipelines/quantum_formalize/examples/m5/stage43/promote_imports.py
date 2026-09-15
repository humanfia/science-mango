"""Import only complete accepted batches; recheck exact bodies, hashes, types and axioms."""
from pathlib import Path
import sys,json,hashlib,shutil,subprocess
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H.parents[4]))
from pipelines.quantum_formalize.engine import Spec,digest,render,check_axiom_output
from pipelines.quantum_formalize.dag_runner import portable_declaration,load_graph
P=Path('/home/jing/m5-lean-arithmetic-workflow-formalization')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records={}
audit='import M5ArithmeticWorkflowReady\n'
for n,module in [(27,'M5OrderCountAccepted'),(39,'M5GlobalCriterionAccepted')]:
 E=H.parent/f'stage{n}'/'experiment'
 result=json.loads((E/'result.json').read_text())
 assert all(result[k] is True for k in ['experiment_passed','assembly_accepted','environment_unchanged'])
 graph,nodes=load_graph(E/'graph.json')
 assert digest(graph)==result['graph_sha256']
 items={}
 for node in nodes:
  if node.spec is None:continue
  d=E/'nodes'/node.id
  receipt=json.loads((d/'receipt.json').read_text());r=receipt['result'];assert receipt['accepted'] and r['accepted']
  last=r['attempts'][-1];assert last['accepted']
  proof=Path(last['proof_path']);target=Path(last['target_path'])
  assert sha(proof)==last['source_sha256'] and sha(target)==last['target_sha256']
  assert sha(proof.with_suffix('.olean'))==last['olean_sha256']
  assert sha(target.with_suffix('.olean'))==last['target_olean_sha256']
  spec=Spec.model_validate(json.loads((d/'resolved-spec.json').read_text()))
  assert spec.statement==node.spec['statement'] and spec.name==node.spec['name']
  draft=json.loads((proof.parent/'draft.json').read_text())['proof']
  assert render(spec,draft,target.stem)==proof.read_text()
  artifact=r['artifacts'][node.id]
  assert digest(artifact['payload'])==artifact['sha256']
  assert portable_declaration(spec,draft)==artifact['payload']['declaration']
  assert artifact['payload']['declaration'] in (E/'AcceptedExperiment.lean').read_text()
  items[node.id]={'source_sha256':sha(proof),'target_sha256':sha(target),'payload_sha256':artifact['sha256']}
  audit+='example : '+spec.statement+' := @'+spec.name+'\n#print axioms '+spec.name+'\n'
 dst=P/(module+'.lean');shutil.copy2(E/'AcceptedExperiment.lean',dst);shutil.copy2(dst,H/'lean'/dst.name)
 records[str(n)]={'result_sha256':sha(E/'result.json'),'assembly_sha256':sha(dst),'nodes':items}
(P/'M5ArithmeticWorkflowReady.lean').write_text('import M5ArithmeticWorkflow\nimport M5OrderCountAccepted\nimport M5GlobalCriterionAccepted\n')
config=(P/'lakefile.toml').read_text()
for module in ['M5OrderCountAccepted','M5GlobalCriterionAccepted']:
 if 'name = "'+module+'"' not in config:config+='\n[[lean_lib]]\nname = "'+module+'"\n'
(P/'lakefile.toml').write_text(config)
(P/'PromotedAudit.lean').write_text(audit)
r=subprocess.run(['/home/jing/.elan/bin/lake','build'],cwd=P,capture_output=True,text=True,timeout=300)
(H/'promoted-build.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stdout+r.stderr
r=subprocess.run(['/home/jing/.elan/bin/lake','env','lean','PromotedAudit.lean'],cwd=P,capture_output=True,text=True,timeout=180)
(H/'promoted-audit.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stdout+r.stderr
for n in [27,39]:
 for node in json.loads((H.parent/f'stage{n}/experiment/graph.json').read_text())['nodes']:
  if node.get('spec'):assert check_axiom_output(r.stdout,node['spec']['name'])[0]
for name in ['M5ArithmeticWorkflowReady.lean','lakefile.toml','PromotedAudit.lean']:shutil.copy2(P/name,H/'lean'/name)
g=json.loads((H/'graph.json').read_text());shutil.copy2(H/'graph.json',H/'graph.before_imports.json');g['nodes']=[n for n in g['nodes'] if n['spec'] is not None]
for n in g['nodes']:n['dependencies']=[d for d in n['dependencies'] if not d.startswith('imports')]
(H/'graph.json').write_text(json.dumps(g,indent=2)+'\n')
(H/'ACCEPTED_IMPORTS.json').write_text(json.dumps(records,indent=2)+'\n')
print('Accepted batches27/39 imported and independently audited; gates removed.')
