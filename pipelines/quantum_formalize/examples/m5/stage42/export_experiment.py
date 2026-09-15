"""Export completed stage42 receipts and source evidence, without altering live projects."""
from pathlib import Path
import json,shutil,hashlib,sys
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H.parents[4]))
from pipelines.quantum_formalize.dag_view import render
S=Path('/home/jing/m5-lean-conditional-residue-count-formalization/.humanize-formal-runs/expansion-repair-so5zrm3v/experiment')
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
(H/'RESULTS.md').write_text('# Stage42 accepted: exact conditional arithmetic residue count\n\nAll six frozen targets and their combined assembly passed. The selected-prefix lists preserve repetition and cancellation, and overfull prefixes are explicitly guarded to zero. Imported original types and permitted axioms were audited before launch.\n\n| Target | Attempts | Result |\n|---|---:|---|\n'+'\n'.join(rows)+'\n\nThe divisor/factor arithmetic conditionalAAt equals the exact guarded completion-pair cardinality. At the signature period, conditionalA is nonnegative and positive exactly when the prefixes fit and a feasible completion exists. Remaining lengths and selected polynomials can differ between the two blocks. No distinctness, weight upper bound, squarefree or nonzero-block assumption is added. Literal squarefree-divisor reindexing is not an acceptance gate. The concrete recovery connection is subsequent work.\n\nSee [result](experiment/result.json), [combined source](experiment/AcceptedExperiment.lean), [preflight/import audit](PREFLIGHT.json), and [manifest](experiment/MANIFEST.json).\n')
print(json.dumps({'accepted':6,'files':len(files),'experiment_passed':True}))
