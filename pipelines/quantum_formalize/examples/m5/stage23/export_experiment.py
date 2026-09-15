"""Export completed stage23 receipts and source evidence, without altering live projects."""
from pathlib import Path
import json,shutil,hashlib,sys
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H.parents[4]))
from pipelines.quantum_formalize.dag_view import render
S=Path('/home/jing/m5-lean-polynomial-indicator-formalization/.humanize-formal-runs/dag-launcher-m0os98qm/experiment')
D=H/'experiment'
r=json.loads((S/'result.json').read_text())
assert r['experiment_passed'] and r['assembly_accepted']
assert not D.exists()
shutil.copytree(S,D)
state=json.loads((D/'nodes/state.json').read_text())
for node,record in state['nodes'].items():
 work=record.get('result',{}).get('work')
 if not work:continue
 work=Path(work)
 for p in work.rglob('*'):
  if p.is_file() and p.suffix in {'.json','.lean'}:
   target=D/'node_runs'/node/p.relative_to(work);target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,target)
(D/'GRAPH.md').write_text(render(D/'graph.json',D/'nodes/state.json'))
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
files={str(p.relative_to(D)):sha(p) for p in sorted(D.rglob('*')) if p.is_file() and p.name!='MANIFEST.json'}
(D/'MANIFEST.json').write_text(json.dumps({'file_count':len(files),'files':files},indent=2)+'\n')
rows=[]
for name,record in state['nodes'].items():
 rows.append(f"| {record['result']['target']} | {len(record['result']['attempts'])} | accepted |")
(H/'RESULTS.md').write_text('# Stage23 accepted: exact polynomial signature indicator\n\nAll three frozen targets and their combined assembly passed. The imported stage16 proof closure was checked against exact original types and permitted axioms before launch. The experiment also recorded local imported source interfaces as untrusted references, without changing target or acceptance checks.\n\n| Target | Attempts | Result |\n|---|---:|---|\n'+'\n'.join(rows)+'\n\nThe final theorem identifies the factor-subset exclusion sum with the exact complete-signature indicator under N>0, monic F and F dividing M_N. Divisibility into both blocks is handled inside the sum; zero blocks and repeated factors are retained. Literal squarefree-divisor reindexing is optional representation correspondence, not an extra M5 acceptance gate. Complete C/A assembly and the full M5 theorem are not claimed by this experiment.\n\nSee [experiment result](experiment/result.json), [combined source](experiment/AcceptedExperiment.lean), [import audit](PREFLIGHT.json), and [provenance manifest](experiment/MANIFEST.json).\n')
print(json.dumps({'accepted':3,'files':len(files),'experiment_passed':True}))
