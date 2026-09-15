"""Replay accepted drafts, repair the explicit period-control proof, then prove downstream targets."""
import asyncio,hashlib,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(HERE.parents[4]))
from hmz.flows import flow
from pipelines.quantum_formalize_dag import Agents,Config
from pipelines.quantum_formalize.engine import Spec,Draft,render,digest,save
from pipelines.quantum_formalize.dag_runner import run_graph,load_graph
ARCHIVE=HERE/'experiments/initial_tactic_failure'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
@flow
async def repair_dag(agents:Agents,task:str,config:Config|None=None)->None:
 if config is None:raise ValueError('config required')
 graph,nodes=load_graph(config.graph)
 assert graph==json.loads((ARCHIVE/'graph.json').read_text())
 for name,value in json.loads((ARCHIVE/'MANIFEST.json').read_text()).items():assert sha(ARCHIVE/name)==value
 drafts={};sources={};calls=[];replays=[]
 for node in nodes:
  if not node.spec or node.id != 'period_control':continue
  r=json.loads((ARCHIVE/'nodes'/node.id/'receipt.json').read_text())['result']
  spec=Spec.model_validate(json.loads((ARCHIVE/'nodes'/node.id/'resolved-spec.json').read_text()))
  assert spec.statement==node.spec['statement']
  if node.id=='period_control':
   folder=ARCHIVE/'node_runs'/node.id/'attempt-005'
   draft=json.loads((HERE/'PERIOD_REPAIR.json').read_text())
   origin='Replace failed automatic search with explicit accepted coefficient, gcd and period theorem applications; exact target unchanged. Scratch compilation passed before replay.'
  else:
   assert r['accepted'];last=r['attempts'][-1];folder=ARCHIVE/'node_runs'/node.id/Path(last['proof_path']).parent.name
   draft=json.loads((folder/'draft.json').read_text());candidate=folder/Path(last['proof_path']).name;target=folder/Path(last['target_path']).name
   assert sha(candidate)==last['source_sha256'] and sha(target)==last['target_sha256']
   assert candidate.read_text()==render(spec,draft['proof'],target.stem)
   assert digest(r['artifacts'][node.id]['payload'])==r['artifacts'][node.id]['sha256']
   origin='Unchanged previously accepted proof, independently recompiled and audited.'
  drafts[node.id]=draft;sources[node.id]={'origin':origin,'source_draft_sha256':sha(folder/'draft.json'),'new_proof_sha256':hashlib.sha256(draft['proof'].encode()).hexdigest()}
 async def propose(node,prompt,attempt):
  if node.id in drafts:
   assert node.id not in replays,'Deterministic repair failed; inspect before retrying'
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
 result=await run_graph(config.graph,config.project,config.output,propose,concurrency=config.concurrency,rounds=config.rounds,timeout=config.compile_timeout)
 save(Path(config.result_path),result)
 save(HERE/'REPAIR_REPLAY.json',{'sources':sources,'replayed_nodes':replays,'live_model_attempts':calls,'retrieval':'fresh dual-library retrieval through unchanged run_graph','math_statements_changed':False,'result':result})
 print(json.dumps(result,indent=2),flush=True)
