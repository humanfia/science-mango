from pathlib import Path
import json,hashlib,sys
H=Path(__file__).resolve().parent;A=H/'experiment';sys.path.insert(0,str(H.parents[4]))
from pipelines.quantum_formalize.dag_view import render
from pipelines.quantum_formalize.engine import Spec,digest,render as render_candidate
from pipelines.quantum_formalize.dag_runner import load_graph,portable_declaration
r=json.loads((A/'result.json').read_text());assert all(r[k] for k in ['experiment_passed','assembly_accepted','environment_unchanged'])
s=json.loads((A/'nodes/state.json').read_text());assert len(s['nodes'])==8 and all(n['accepted'] for n in s['nodes'].values())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((A/'MANIFEST.json').read_text());assert all(sha(A/n)==h for n,h in m.get('files',m).items())
g,nodes=load_graph(A/'graph.json');proofs={}
for n in nodes:
 rec=s['nodes'][n.id];assert rec==json.loads((A/'nodes'/n.id/'receipt.json').read_text());r=rec['result'];a=r['attempts'][-1];f=A/'node_runs'/n.id/Path(a['proof_path']).parent.name
 spec=Spec.model_validate(json.loads((A/'nodes'/n.id/'resolved-spec.json').read_text()));d=json.loads((f/'draft.json').read_text());assert spec.statement==n.spec['statement']
 assert sha(f/Path(a['proof_path']).name)==a['source_sha256'] and sha(f/Path(a['target_path']).name)==a['target_sha256']
 assert (f/Path(a['proof_path']).name).read_text()==render_candidate(spec,d['proof'],Path(a['target_path']).stem)
 art=r['artifacts'][n.id];assert digest(art['payload'])==art['sha256'] and digest(n.spec)==art['payload']['spec_sha256'];assert portable_declaration(spec,d['proof'])==art['payload']['declaration'];proofs[n.id]=art['sha256']
(H/'PORTABLE_AUDIT.json').write_text(json.dumps({'verified_count':len(proofs),'original_source_target_receipt_render_and_payload':True,'nodes':proofs},indent=2)+'\n')
(H/'ATTEMPTS.json').write_text(json.dumps({k:len(v['result']['attempts'])for k,v in s['nodes'].items()},indent=2)+'\n')
(H/'GRAPH.md').write_text(render(H/'graph.json',A/'nodes/state.json'))
(H/'RESULTS.md').write_text('The actual generated family at effective query sectors and streamed index predicate are exactly the full raw-domain optimum semantics. The frozen targets establish every feasible raw presentation is realizable, actual index feasibility is equivalent to raw feasibility, streamed winners are exactly all raw optima, every raw optimum appears, and actual leastAction presentations appear exactly once across generated classes. Empty output and winning strict-dominator behavior are exact; invalid signatures preserve the original error. All ties, both sector modes, empty objectives and NoLogical policies remain unchanged.\n\nProduction uses actual GeneratedFamily, StreamingIndices and factorized leastAction; RawFeasible and RawWinner occur only in the semantic claims. No free transversal, sector set, label or count correctness assumption remains. This is the selector correspondence component, not an independent declaration of complete M7 resource/replay acceptance.\n\nAll frozen targets passed normal independent exact-type and axiom checks, full assembly and unchanged-environment checks. Original candidate/target hashes, receipts and portable declarations were reverified on archive. Parent source ordering reconciliations, if any, preserve exact theorem bodies and imports and are recorded separately. Full candidate histories are retained.\n')
m={str(p.relative_to(H)):sha(p)for p in H.rglob('*')if p.is_file()and p!=H/'MANIFEST.json'and'__pycache__'not in p.parts};(H/'MANIFEST.json').write_text(json.dumps({'file_count':len(m),'files':m},indent=2)+'\n');print('canonical verified',len(proofs),'full files',len(m))
