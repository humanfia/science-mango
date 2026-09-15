from pathlib import Path
import json,hashlib,time,subprocess,sys
H=Path(__file__).resolve().parent
while not (H/'PREFLIGHT.json').exists():time.sleep(15)
r=json.loads((H/'PREFLIGHT.json').read_text());assert r['accepted'] and r['ready_for_live_experiment']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
f={'definition_sha256':sha(H/'lean/M7QuerySectors.lean'),'graph_sha256':sha(H/'graph.json'),'frozen_target_count':5,'pending_verified_imports':[],'closed_Prop_target_preflight':True,'not_launched':False}
(H/'FREEZE.json').write_text(json.dumps(f,indent=2)+'\n')
subprocess.run([sys.executable,str(H/'launch.py')],cwd=H.parents[4],check=True)
