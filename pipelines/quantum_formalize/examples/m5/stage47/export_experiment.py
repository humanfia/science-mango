"""Export completed concrete residue recovery with every source/acceptance receipt."""
from pathlib import Path
import json,shutil,hashlib,sys
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H.parents[4]))
from pipelines.quantum_formalize.dag_view import render
S=Path(json.loads((H/'PARTITION_REPAIR_LAUNCH.json').read_text())['launcher'])/'experiment'
D=H/'experiment'
r=json.loads((S/'result.json').read_text())
assert r['experiment_passed'] and r['assembly_accepted'] and r['environment_unchanged']
assert len(r['accepted_nodes'])==8 and not D.exists()
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
rows=[f"| {rec['result']['target']} | {len(rec['result']['attempts'])} | accepted |" for rec in state['nodes'].values()]
(H/'RESULTS.md').write_text('# Stage47 accepted: concrete arithmetic residue recovery\n\nAll eight frozen targets, combined assembly and unchanged-environment checks passed. The concrete oracle is conditionalA applied to the take/drop split of the selected residue prefix; it contains the actual divisor/factor/character arithmetic.\n\n| Target | Final-run attempts | Result |\n|---|---:|---|\n'+'\n'.join(rows)+'\n\nA completion-pair/full-word bijection and exact conditional count establish the concrete oracle prefix count. Accepted finite prefix partition and terminal identities therefore apply, and the initial oracle value equals actual A. The final recovery_correct theorem instantiates the finite residue algorithm with no abstract oracle-correctness premise: positive A yields a returned word of length 2*(w−1), raw-coordinate gcd1, exact full signature F, and at most 2*(w−1)*signaturePeriod(F) arithmetic candidate tests. Repetitions, cancellations and empty completion lengths remain allowed. This test-count bound does not claim a separate executable-runtime refinement.\n\nThe two generic helper drafts were independently checked and then submitted through the same frozen acceptance as the live concrete links; their original checks remain in root_helpers. The initial live oracle_initial and prefix_algebra proofs each succeeded on attempt2 and were preserved unchanged. Local repairs of completion_feasible, oracle_prefix_count and oracle_partition_terminal kept every target, definition and default kernel limit unchanged. In the partition node, live candidates alternated between a missing finite-word type annotation and a missing matching DecidableEq instance, reverting the earlier correction in successive attempts; the verified repair retained both. This is recorded as evidence for future harness feedback retention, not as another M5 completion gate. All prior experiments and successful proofs remain archived under experiments, with repair details in repair/README.md. See [result](experiment/result.json), [combined source](experiment/AcceptedExperiment.lean), [preflight](PREFLIGHT.json) and [manifest](experiment/MANIFEST.json).\n')
print(json.dumps({'accepted':8,'files':len(files),'experiment_passed':True}))
