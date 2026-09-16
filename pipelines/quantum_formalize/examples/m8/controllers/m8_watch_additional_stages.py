from pathlib import Path
import json,time,subprocess,hashlib,datetime
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');base=repo/'pipelines/quantum_formalize/examples/m8'
names=['orbit_span','weighted_search'];done=set()
while len(done)<len(names):
 for name in names:
  if name in done:continue
  b=base/name
  if (b/'experiment/MANIFEST.json').exists():done.add(name);continue
  try:
   launch=json.loads((b/'LAUNCH.json').read_text());r=Path(launch['launcher']);result=json.loads((r/'result.json').read_text())
  except (OSError,ValueError,KeyError):continue
  if result.get('status')!='finished':continue
  if not all(result.get(k)is True for k in ['assembly_accepted','environment_unchanged','experiment_passed']):continue
  with (b/'auto_archive.log').open('a') as log:
   proc=subprocess.run(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python','-c','exec(open("/tmp/m5_archive_batch.py").read().replace("examples/m5","examples/m8"))',name,str(r)],cwd=repo,stdout=log,stderr=subprocess.STDOUT)
  if proc.returncode!=0:raise RuntimeError((name,'archive failed',proc.returncode))
  m=json.loads((b/'experiment/MANIFEST.json').read_text());m=m.get('files',m)
  for p,h in m.items():assert hashlib.sha256((b/'experiment'/p).read_bytes()).hexdigest()==h,(name,p)
  (b/'AUTO_ARCHIVE.json').write_text(json.dumps({'verified_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'launcher':str(r),'canonical_files':len(m),'all_hashes_verified':True,'note':'Only complete normal batch acceptance promoted; no full-M8 status inferred from a component'},indent=2)+'\n')
  done.add(name)
 time.sleep(20)
