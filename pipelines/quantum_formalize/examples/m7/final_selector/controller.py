from pathlib import Path
import json,time,subprocess,hashlib,sys,traceback
H=Path(__file__).resolve().parent
parents=['generated_family','streaming_indices','query_sectors','global_query','query_rebase']
def status(phase,**kw):(H/'CONTROLLER_STATUS.json').write_text(json.dumps({'phase':phase,**kw},indent=2)+'\n')
def run(script):
 r=subprocess.run([sys.executable,str(H/script)],cwd=H.parents[4],capture_output=True,text=True)
 (H/(script.removesuffix('.py')+'.controller.log')).write_text(r.stdout+r.stderr)
 if r.returncode:raise RuntimeError(script+': '+(r.stdout+r.stderr)[-4000:])
try:
 while True:
  pending=[s for s in parents if not (H.parent/s/'experiment/MANIFEST.json').exists()]
  status('waiting_canonical_parents',pending=pending)
  if not pending:break
  time.sleep(20)
 run('prepare.py');status('closed_type_and_build_preflight');run('preflight.py')
 sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
 (H/'FREEZE.json').write_text(json.dumps({'definition_sha256':sha(H/'lean/M7FinalSelector.lean'),'graph_sha256':sha(H/'graph.json'),'frozen_target_count':8,'closed_Prop_target_preflight':True,'pending_verified_imports':[],'not_launched':False},indent=2)+'\n')
 run('launch.py');status('live',**json.loads((H/'LAUNCH.json').read_text()))
except Exception as exc:status('failed',error=str(exc));traceback.print_exc();raise
