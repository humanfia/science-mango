"""Recheck accepted drafts and two independently compiled finite-filter repairs."""
from pathlib import Path
import asyncio,json,hashlib,sys,tempfile,shutil
H=Path(__file__).resolve().parent
sys.path.insert(0,str(H.parents[4]))
from pipelines.quantum_formalize.dag_runner import load_graph,run_graph
from pipelines.quantum_formalize.engine import Spec,render,digest
P=Path('/home/jing/m5-lean-prefix-partition-formalization')
E=H/'experiments/initial_tactic_failure'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
g,nodes=load_graph(H/'graph.json');assert g==json.loads((E/'graph.json').read_text())
for f,value in json.loads((E/'MANIFEST.json').read_text()).items():assert sha(E/f)==value
proofs={};origins={}
for n in nodes:
 receipt=json.loads((E/'nodes'/n.id/'receipt.json').read_text())
 if receipt['accepted']:
  r=receipt['result'];last=r['attempts'][-1];folder=E/'node_runs'/n.id/Path(last['proof_path']).parent.name
  candidate=folder/Path(last['proof_path']).name;target=folder/Path(last['target_path']).name
  spec=Spec.model_validate(json.loads((E/'nodes'/n.id/'resolved-spec.json').read_text()))
  d=json.loads((folder/'draft.json').read_text())
  assert sha(candidate)==last['source_sha256'] and sha(target)==last['target_sha256']
  assert render(spec,d['proof'],target.stem)==candidate.read_text()
  assert digest(r['artifacts'][n.id]['payload'])==r['artifacts'][n.id]['sha256']
  origins[n.id]={'kind':'unchanged accepted draft','draft_sha256':sha(folder/'draft.json')}
 else:
  folder=H/'repairs'/n.id
  log=(folder/'compile.log').read_text();assert 'error:' not in log and 'sorryAx' not in log and 'depends on axioms: [propext, Classical.choice, Quot.sound]' in log
  d=json.loads((folder/'draft.json').read_text())
  origins[n.id]={'kind':'independently compiled explicit finite-filter congruence repair','draft_sha256':sha(folder/'draft.json'),'compile_log_sha256':sha(folder/'compile.log')}
 proofs[n.id]=d
historical=E/'node_runs/count_empty/attempt-001/retrieval.json';receipts=json.loads(historical.read_text())
assert all(r['status']=='ok' for r in receipts) and {r['library'] for r in receipts}=={'Mathlib','Physlib'}
async def propose(node,prompt,attempt):return proofs[node.id]
async def search(queries):
 assert list(queries)==['list prefix get length equality','finset cardinality sum fibers']
 return receipts
async def main():
 launcher=Path(tempfile.mkdtemp(prefix='prefix-repair-',dir=P/'.humanize-formal-runs'))
 print(json.dumps({'launcher':str(launcher),'kind':'deterministic proof recheck','concurrency':16}),flush=True)
 r=await run_graph(H/'graph.json',P,launcher/'experiment',propose,concurrency=16,rounds=1,timeout=180,search=search)
 (H/'REPAIR_REPLAY.json').write_text(json.dumps({'origins':origins,'retrieval_replay':{'path':str(historical),'sha256':sha(historical),'fresh_search':False},'mathematical_statements_changed':False,'result':r},indent=2)+'\n')
 print(json.dumps(r),flush=True)
asyncio.run(main())
