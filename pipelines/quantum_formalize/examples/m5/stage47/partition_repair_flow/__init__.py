"""Replay accepted concrete-recovery ancestors and verified feasible correspondence repair."""
import asyncio,hashlib,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(HERE.parents[4]))
from hmz.flows import flow
from pipelines.quantum_formalize_dag import Agents,Config
from pipelines.quantum_formalize.engine import Spec,Draft,render,digest,save
from pipelines.quantum_formalize.dag_runner import run_graph,load_graph
ARCHIVE=HERE/'experiments/partition_instance_failure'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
@flow
async def repair_dag(agents:Agents,task:str,config:Config|None=None)->None:
 if config is None:raise ValueError('config required')
 graph,nodes=load_graph(config.graph)
 assert graph==json.loads((ARCHIVE/'graph.json').read_text())
 for name,value in json.loads((ARCHIVE/'MANIFEST.json').read_text()).items():assert sha(ARCHIVE/name)==value
 drafts={};sources={};calls=[];replays=[]
 for replay_id in ['completion_word_split','completion_prefix_card','oracle_initial','prefix_algebra','completion_feasible','oracle_prefix_count']:
  node=next(n for n in nodes if n.id==replay_id)
  r=json.loads((ARCHIVE/'nodes'/node.id/'receipt.json').read_text())['result'];assert r['accepted']
  last=r['attempts'][-1];folder=ARCHIVE/'node_runs'/node.id/Path(last['proof_path']).parent.name
  spec=Spec.model_validate(json.loads((ARCHIVE/'nodes'/node.id/'resolved-spec.json').read_text()))
  draft=json.loads((folder/'draft.json').read_text());candidate=folder/Path(last['proof_path']).name;target=folder/Path(last['target_path']).name
  assert sha(candidate)==last['source_sha256'] and sha(target)==last['target_sha256']
  assert candidate.read_text()==render(spec,draft['proof'],target.stem)
  assert digest(r['artifacts'][node.id]['payload'])==r['artifacts'][node.id]['sha256']
  drafts[node.id]=draft;sources[node.id]={'origin':'Unchanged accepted proof; recompiled and audited','source_draft_sha256':sha(folder/'draft.json')}
 node=next(n for n in nodes if n.id=='oracle_partition_terminal');spec=Spec.model_validate(json.loads((ARCHIVE/'nodes'/node.id/'resolved-spec.json').read_text()))
 draft=json.loads((HERE/'repair/oracle_partition_terminal.json').read_text())
 check=json.loads((HERE/'repair/oracle_partition_terminal.debug.json').read_text());assert check['accepted']
 candidate=Path(check['proof_path']);target=Path(check['target_path'])
 assert sha(candidate)==check['source_sha256'] and sha(target)==check['target_sha256']
 assert candidate.read_text()==render(spec,draft['proof'],target.stem)
 drafts[node.id]=draft;sources[node.id]={'origin':'Exact original target; deterministic local DecidableEq instance repair already kernel checked','source_draft_sha256':sha(HERE/'repair/oracle_partition_terminal.json'),'debug_source_sha256':check['source_sha256']}
 guidance='Use narrow simp only and explicit rewrites to avoid expanding unrelated large definitions. When comparing classical finite filters, prove equality by extensional membership before rewriting cardinalities; avoid change across different Decidable instances. Keep the original frozen statement and default limits.'
 async def propose(node,prompt,attempt):
  if node.id in drafts:
   assert node.id not in replays,'Deterministic replay failed; inspect before retry'
   replays.append(node.id);return drafts[node.id]
  calls.append({'node':node.id,'attempt':attempt.name})
  worker=agents.prover.clone(name=f'{node.id}-{attempt.name}',skills=[]);session=worker.new(attempt);session.loads([])
  supplemented=prompt+'\n'+guidance
  (attempt/'supplemented-prompt.txt').write_text(supplemented)
  turn=asyncio.create_task(session.aturn(supplemented,schema=Draft))
  try:return await asyncio.wait_for(turn,timeout=config.turn_timeout)
  finally:
   try:session.close()
   finally:worker.stop()
   if not turn.done():turn.cancel()
   await asyncio.gather(turn,return_exceptions=True)
 result=await run_graph(config.graph,config.project,config.output,propose,concurrency=config.concurrency,rounds=config.rounds,timeout=config.compile_timeout)
 save(Path(config.result_path),result)
 save(HERE/'PARTITION_REPAIR_REPLAY.json',{'sources':sources,'replayed_nodes':replays,'live_model_attempts':calls,'supplemental_guidance':guidance,'math_statements_changed':False,'result':result})
 print(json.dumps(result,indent=2),flush=True)
