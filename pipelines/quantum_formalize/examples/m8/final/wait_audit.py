from pathlib import Path
import subprocess,time,json,datetime
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');b=repo/'pipelines/quantum_formalize/examples/m8/final'
while not(b/'experiment/MANIFEST.json').exists():time.sleep(20)
with(b/'audit.log').open('a')as f:
 p=subprocess.run(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(b/'audit_root.py'),'--repo',str(repo)],cwd=repo,stdout=f,stderr=subprocess.STDOUT)
(b/'AUDIT_RUN.json').write_text(json.dumps({'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'returncode':p.returncode,'status':'accepted' if p.returncode==0 else 'pending or evidence mismatch; inspect audit.log'},indent=2)+'\n')
if p.returncode==0:subprocess.run(['python3','/home/jing/m8_update_rollup.py'],check=True)
raise SystemExit(p.returncode)
