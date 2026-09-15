from pathlib import Path
import subprocess,sys,json,time,hashlib,traceback
H=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def status(phase,**kw):
 (H/'CONTROLLER_STATUS.json').write_text(json.dumps({'phase':phase,**kw},indent=2)+'\n');print(phase,flush=True)
def run(script):
 r=subprocess.run([sys.executable,str(H/script)],cwd=H.parents[4],capture_output=True,text=True)
 (H/(script.removesuffix('.py')+'.controller.log')).write_text(r.stdout+r.stderr)
 if r.returncode:raise RuntimeError(script+' failed: '+(r.stdout+r.stderr)[-3000:])
try:
 status('waiting_initial_closed_type_preflight')
 while not (H/'PREFLIGHT.json').exists():time.sleep(20)
 pf=json.loads((H/'PREFLIGHT.json').read_text());assert pf['accepted']
 frozen={'definition_sha256':sha(H/'lean/M7RecoveryInstance.lean'),'graph_sha256':sha(H/'graph.json'),'frozen_target_count':7,'closed_Prop_target_preflight':True,'pending_verified_imports':['prefix_orbit','recovery_prefix'],'not_launched':True}
 (H/'FREEZE.json').write_text(json.dumps(frozen,indent=2)+'\n')
 status('waiting_canonical_parent_proof_gates')
 while not all((H.parent/s/'experiment/MANIFEST.json').exists() for s in ['prefix_orbit','recovery_prefix']):time.sleep(20)
 run('promote_parents.py');run('preflight.py')
 assert sha(H/'lean/M7RecoveryInstance.lean')==frozen['definition_sha256'] and sha(H/'graph.json')==frozen['graph_sha256']
 assert json.loads((H/'PREFLIGHT.json').read_text())['ready_for_live_experiment']
 frozen['pending_verified_imports']=[];frozen['not_launched']=False;(H/'FREEZE.json').write_text(json.dumps(frozen,indent=2)+'\n')
 run('launch.py');launch=json.loads((H/'LAUNCH.json').read_text());status('live',**launch)
except Exception as exc:
 status('failed',error=str(exc));traceback.print_exc();raise
