"""Replay one accepted draft and one checked bridge repair, then continue live."""
import asyncio,json,hashlib,sys
from pathlib import Path
H=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(H.parents[4]))
from hmz.flows import flow
from pipelines.quantum_formalize_dag import Agents,Config
from pipelines.quantum_formalize.engine import Draft,Spec,render,digest,save
from pipelines.quantum_formalize.dag_runner import run_graph,load_graph
E=H/'experiments/initial_order_bridge_failure'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
@flow
async def repair_dag(agents:Agents,task:str,config:Config|None=None)->None:
 assert config is not None
 graph,nodes=load_graph(config.graph);assert graph==json.loads((E/'graph.json').read_text())
 for f,v in json.loads((E/'MANIFEST.json').read_text()).items():assert sha(E/f)==v
 drafts={};origins={};calls=[];replays=[]
 for n in nodes:
  if n.id not in ['order_count_iff','order_count_nonnegative']:continue
  if n.id=='order_count_nonnegative':
   r=json.loads((E/'nodes'/n.id/'receipt.json').read_text())['result'];assert r['accepted'];last=r['attempts'][-1]
   folder=E/'node_runs'/n.id/Path(last['proof_path']).parent.name
   spec=Spec.model_validate(json.loads((E/'nodes'/n.id/'resolved-spec.json').read_text()))
   candidate=folder/Path(last['proof_path']).name;target=folder/Path(last['target_path']).name
   d=json.loads((folder/'draft.json').read_text())
   assert sha(candidate)==last['source_sha256'] and sha(target)==last['target_sha256']
   assert render(spec,d['proof'],target.stem)==candidate.read_text()
   assert digest(r['artifacts'][n.id]['payload'])==r['artifacts'][n.id]['sha256']
   origin='unchanged accepted proof'
  else:
   folder=H/'repairs'/n.id;d=json.loads((folder/'draft.json').read_text());log=(folder/'compile.log').read_text()
   assert 'error:' not in log and 'sorryAx' not in log and 'depends on axioms: [propext, Classical.choice, Quot.sound]' in log
   exact='theorem '+n.spec['name']+' : '+n.spec['statement']+' := by\n'+''.join('  '+line+'\n' for line in d['proof'].splitlines())
   assert exact in (folder/'Checked.lean').read_text()
   origin='explicit conjunction transport and qualified polynomial gcd; unchanged target, default heartbeat kernel check'
  drafts[n.id]=d;origins[n.id]={'kind':origin,'draft_sha256':sha(folder/'draft.json')}
 async def propose(node,prompt,attempt):
  if node.id in drafts:
   assert node.id not in replays,'Deterministic repair failed; inspect it before retrying'
   replays.append(node.id);return drafts[node.id]
  calls.append({'node':node.id,'attempt':attempt.name})
  worker=agents.prover.clone(name=f'{node.id}-{attempt.name}',skills=[]);session=worker.new(attempt);session.loads([])
  turn=asyncio.create_task(session.aturn(prompt,schema=Draft))
  try:return await asyncio.wait_for(turn,timeout=config.turn_timeout)
  finally:
   try:session.close()
   finally:worker.stop()
   if not turn.done():turn.cancel()
   await asyncio.gather(turn,return_exceptions=True)
 historical=E/'node_runs/order_count_nonnegative/attempt-001/retrieval.json';receipts=json.loads(historical.read_text())
 assert all(r['status']=='ok' for r in receipts) and {r['library'] for r in receipts}=={'Mathlib','Physlib'}
 async def search(queries):
  if list(queries)==['finite minimum member lower bound','integer nonnegative positive zero iff']:return receipts
  from pipelines.quantum_formalize.search import search_both
  return await search_both(queries)
 r=await run_graph(config.graph,config.project,config.output,propose,concurrency=config.concurrency,rounds=config.rounds,timeout=config.compile_timeout,search=search)
 save(Path(config.result_path),r)
 save(H/'REPAIR_REPLAY.json',{'origins':origins,'replayed_nodes':replays,'live_model_attempts':calls,'retrieval_replay':{'path':str(historical),'sha256':sha(historical),'fresh_search':False},'mathematical_statements_changed':False,'result':r})
 print(json.dumps(r),flush=True)
