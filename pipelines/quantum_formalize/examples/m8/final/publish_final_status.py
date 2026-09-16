from pathlib import Path
import json,hashlib,subprocess,datetime
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');b=repo/'pipelines/quantum_formalize/examples/m8';f=b/'final'
a=json.loads((f/'ROOT_ACCEPTANCE.json').read_text());assert a['status']=='accepted' and a['m8_formalized'] is True
assert hashlib.sha256((f/'experiment/result.json').read_bytes()).hexdigest()==a['root_result_sha256']
assert hashlib.sha256((f/'lean/M8Final.lean').read_bytes()).hexdigest()==a['claims_sha256']
assert hashlib.sha256((b/'SOURCE.json').read_bytes()).hexdigest()==a['source_metadata_sha256']
subprocess.run(['python3','/home/jing/m8_update_rollup.py'],check=True)
d=json.loads((b/'COMPONENT_STATUS.json').read_text())
p=b/'README.md';s=p.read_text().replace('In progress. The frozen natural-language acceptance is distinct from Lean acceptance; no complete M8 Lean root has passed.','The complete accepted M8 Lean root has passed: `M8.Final.original_m8`. See the [source-bound root acceptance](final/ROOT_ACCEPTANCE.json), [compiled root proof](final/experiment/AcceptedExperiment.lean), [exact claim definitions](final/lean/M8Final.lean), and [reproduction instructions](final/README.md).');p.write_text(s)
p=f/'README.md';s=p.read_text().replace('Root acceptance is pending. A successful component or natural-language review is not the complete Lean result.','The complete original-scope root `M8.Final.original_m8` has passed normal Lean acceptance. The [root evidence audit](ROOT_ACCEPTANCE.json) binds '+str(a['verified_clause_count'])+' exact clauses to the frozen natural-language claim, and the [canonical experiment](experiment/result.json) records successful root compilation and environment checks.').replace('The gated [preparer]','The [preparer]');p.write_text(s)
p=repo/'research/quantum_m8/README.md';s=p.read_text().replace('Lean 形式化进行中，尚无完整总定理验收。','Lean 完整总定理 `M8.Final.original_m8` 已通过验收。\n\n- [完整 Lean 验收记录](../../pipelines/quantum_formalize/examples/m8/final/ROOT_ACCEPTANCE.json)\n- [总定理证明](../../pipelines/quantum_formalize/examples/m8/final/experiment/AcceptedExperiment.lean)\n- [精确命题与全部原要求](../../pipelines/quantum_formalize/examples/m8/final/lean/M8Final.lean)');p.write_text(s)
p=f/'SCOPE_MAP.json';m=json.loads(p.read_text());m['status']='Original-scope root accepted; see ROOT_ACCEPTANCE.json'
for row in m['sections']:
 row['formally_closed']=True;row['evidence']='ROOT_ACCEPTANCE.json' if row['number'] in [1,10]else'lean/M8Final.lean and experiment/AcceptedExperiment.lean'
p.write_text(json.dumps(m,indent=2)+'\n')
(f/'PUBLICATION_STATUS.json').write_text(json.dumps({'status':'complete original M8 accepted','updated_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'root':'M8.Final.original_m8','canonical_targets':d['completed_targets'],'canonical_batches':len(d['completed_modules']),'root_acceptance_sha256':hashlib.sha256((f/'ROOT_ACCEPTANCE.json').read_bytes()).hexdigest(),'time_exponent':12,'space_exponent':4,'scope_increased':False},indent=2)+'\n')
print('M8 accepted status published:',d['completed_targets'],len(d['completed_modules']))
