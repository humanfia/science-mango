from pathlib import Path
import subprocess,os,json,hashlib,time
p=Path('/home/jing/m7-lean-quotient-auto-formalization')
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914')
b=repo/'pipelines/quantum_formalize/examples/m7/quotient_auto'
env=dict(os.environ);env['PATH']='/home/jing/.elan/bin:'+env['PATH'];env['PYTHONPATH']=str(repo);env['M7_COMPILE_TIMEOUT']='600';env['M7_BROAD_RETRIEVAL']='1'
# Wait only for an already running build in this exact isolated project.
for _ in range(120):
 active=False
 for d in Path('/proc').iterdir():
  if not d.name.isdigit():continue
  try:
   args=(d/'cmdline').read_bytes().split(b'\0')
   if args and Path(args[0].decode()).name=='lake' and b'build' in args and (d/'cwd').resolve()==p:active=True
  except (OSError,ValueError):pass
 if not active:break
 time.sleep(10)
r={'phase':'preflight','graph_sha256':hashlib.sha256((b/'graph.json').read_bytes()).hexdigest(),'source_sha256':hashlib.sha256((p/'M7QuotientAuto.lean').read_bytes()).hexdigest(),'accepted':False}
for label,cmd in [('build',['lake','build']),('types',['lake','env','lean','Preflight.lean'])]:
 with (b/(label+'.log')).open('w') as log:
  try:code=subprocess.run(cmd,cwd=p,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=1800).returncode
  except subprocess.TimeoutExpired:code=124
 r[label+'_exit_code']=code;(b/'PREFLIGHT.json').write_text(json.dumps(r,indent=2)+'\n')
 if code:raise SystemExit(code)
r.update(accepted=True,phase='definitions and 8 exact target types compiled; proofs pending');(b/'PREFLIGHT.json').write_text(json.dumps(r,indent=2)+'\n')
subprocess.run(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python','/home/jing/m7_launch_batch.py','quotient_auto','quotient-auto','2'],cwd=repo,env=env,check=True)
