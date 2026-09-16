from pathlib import Path
import json,time,subprocess,datetime
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');base=repo/'pipelines/quantum_formalize/examples/m8';b=base/'weighted_sum';b.mkdir(exist_ok=True);names=['weighted_search','p3_family'];last=None
while True:
 ready=[]
 for n in names:
  p=base/n/'experiment'
  try:
   r=json.loads((p/'result.json').read_text());m=json.loads((p/'MANIFEST.json').read_text());m=m.get('files',m)
   if all(r.get(k)is True for k in ['assembly_accepted','environment_unchanged','experiment_passed']) and m and all((p/f).is_file() for f in m):ready.append(n)
  except (OSError,ValueError):pass
 pending=[n for n in names if n not in ready]
 if pending!=last:
  (b/'WAITING_FOR_CANONICAL.json').write_text(json.dumps({'checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'ready':ready,'pending':pending,'proof_launched':False,'rule':'Prepare, hash-verify, compile definitions and closed exact target types only after every parent has a canonical acceptance receipt.'},indent=2)+'\n');last=pending
 if not pending:break
 time.sleep(20)
with (b/'prepare.log').open('w') as log:
 r=subprocess.run(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python','/home/jing/m8_prepare_weighted_sum.py'],cwd=repo,stdout=log,stderr=subprocess.STDOUT)
(b/'PREPARE_RESULT.json').write_text(json.dumps({'exit_code':r.returncode,'note':'A successful prepare starts separate definition/type preflight; no theorem acceptance is implied.'},indent=2)+'\n')
