"""Replay two accepted proofs and kernel-check a one-line repair of the third."""
import asyncio, hashlib, json, os, sys, tempfile
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parents[4]))
from pipelines.quantum_formalize.engine import Spec,render,digest
from pipelines.quantum_formalize.dag_runner import run_graph,load_graph
ARCHIVE=HERE/'experiments/initial_tactic_failure'
PROJECT=Path('/home/jing/m5-lean-finite-exclusion-formalization')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
async def main():
 graph,nodes=load_graph(HERE/'graph.json')
 assert graph==json.loads((ARCHIVE/'graph.json').read_text())
 for name,value in json.loads((ARCHIVE/'MANIFEST.json').read_text()).items():assert sha(ARCHIVE/name)==value
 drafts={};sources={};historical={}
 for node in nodes:
  if not node.spec:continue
  r=json.loads((ARCHIVE/'nodes'/node.id/'receipt.json').read_text())['result']
  spec=Spec.model_validate(json.loads((ARCHIVE/'nodes'/node.id/'resolved-spec.json').read_text()))
  assert spec.statement==node.spec['statement']
  if node.id=='exclusion_indicator':
   folder=ARCHIVE/'node_runs'/node.id/'attempt-004'
   draft=json.loads((folder/'draft.json').read_text())
   assert draft['proof'].endswith('rw [he]')
   draft['proof']=draft['proof'][:-len('rw [he]')]+'simpa only [he]'
   origin='Repair failed fourth attempt: rewrite final iff with simp to handle dependent Decidable instances.'
  else:
   assert r['accepted'];last=r['attempts'][-1];folder=ARCHIVE/'node_runs'/node.id/Path(last['proof_path']).parent.name
   draft=json.loads((folder/'draft.json').read_text());candidate=folder/Path(last['proof_path']).name;target=folder/Path(last['target_path']).name
   assert sha(candidate)==last['source_sha256'] and sha(target)==last['target_sha256']
   assert candidate.read_text()==render(spec,draft['proof'],target.stem)
   assert digest(r['artifacts'][node.id]['payload'])==r['artifacts'][node.id]['sha256']
   origin='Unchanged previously accepted proof.'
  sources[node.id]={'origin':origin,'source_draft_sha256':sha(folder/'draft.json'),'new_proof_sha256':hashlib.sha256(draft['proof'].encode()).hexdigest()}
  drafts[node.id]=draft
  receipts_path=ARCHIVE/'node_runs'/node.id/'attempt-001/retrieval.json';receipts=json.loads(receipts_path.read_text())
  assert all(x['status']=='ok' for x in receipts) and {x['library'] for x in receipts}=={'Mathlib','Physlib'}
  historical.setdefault(tuple(node.spec['queries']),(receipts,receipts_path))
 parent=Path(tempfile.mkdtemp(prefix='repair-replay-',dir=PROJECT/'.humanize-formal-runs'));calls=[];searches=[]
 async def propose(node,prompt,attempt):
  assert node.id not in calls;calls.append(node.id);return drafts[node.id]
 async def search(queries):
  receipts,path=historical[tuple(queries)];searches.append({'source':str(path.relative_to(HERE)),'sha256':sha(path),'fresh_search':False});return receipts
 os.environ['PATH']='/home/jing/.elan/bin:'+os.environ.get('PATH','')
 print(json.dumps({'work':str(parent/'experiment'),'model_calls':0}),flush=True)
 result=await run_graph(HERE/'graph.json',PROJECT,parent/'experiment',propose,concurrency=16,rounds=1,search=search)
 report={'sources':sources,'retrieval_replays':searches,'model_calls':0,'network_search_calls':0,'math_statements_changed':False,'controller_sha256':sha(HERE.parents[4]/'pipelines/quantum_formalize/dag_runner.py'),'result':result}
 (HERE/'REPAIR_REPLAY.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(result));assert result['experiment_passed']
if __name__=='__main__':asyncio.run(main())
