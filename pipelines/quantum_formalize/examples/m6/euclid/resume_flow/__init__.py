"""Preserve accepted finite-pin proofs; normally recheck a local coefficient repair."""
import asyncio,hashlib,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(HERE.parents[4]))
from hmz.flows import flow
from pipelines.quantum_formalize_dag import Agents,Config
from pipelines.quantum_formalize.engine import Spec,Draft,render,digest,save
from pipelines.quantum_formalize.dag_runner import run_graph,load_graph,portable_declaration
ARCHIVE=HERE/'experiments/user_interrupted_after18'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
@flow
async def repair_dag(agents:Agents,task:str,config:Config|None=None)->None:
 if config is None:raise ValueError('config required')
 graph,nodes=load_graph(config.graph)
 assert graph==json.loads((ARCHIVE/'graph.json').read_text())
 for name,value in json.loads((ARCHIVE/'MANIFEST.json').read_text()).items():assert sha(ARCHIVE/name)==value
 state=json.loads((ARCHIVE/'nodes/state.json').read_text());drafts={};sources={};calls=[];replays=[]
 for node in nodes:
  record=state['nodes'][node.id]
  if not record.get('accepted'):continue
  assert record==json.loads((ARCHIVE/'nodes'/node.id/'receipt.json').read_text())
  r=record['result'];last=r['attempts'][-1];folder=ARCHIVE/'node_runs'/node.id/Path(last['proof_path']).parent.name
  spec=Spec.model_validate(json.loads((ARCHIVE/'nodes'/node.id/'resolved-spec.json').read_text()))
  assert spec.statement==node.spec['statement']
  draft=json.loads((folder/'draft.json').read_text());candidate=folder/Path(last['proof_path']).name;target=folder/Path(last['target_path']).name
  assert sha(candidate)==last['source_sha256'] and sha(target)==last['target_sha256']
  assert candidate.read_text()==render(spec,draft['proof'],target.stem)
  artifact=r['artifacts'][node.id];assert digest(artifact['payload'])==artifact['sha256']
  assert digest(node.spec)==artifact['payload']['spec_sha256']
  assert portable_declaration(spec,draft['proof'])==artifact['payload']['declaration']
  drafts[node.id]=draft;sources[node.id]={'origin':'Unchanged accepted proof recompiled and audited','source_draft_sha256':sha(folder/'draft.json'),'payload_sha256':artifact['sha256']}
 node=next(n for n in nodes if n.id=='euclid_correct');spec=Spec.model_validate(json.loads((ARCHIVE/'nodes'/node.id/'resolved-spec.json').read_text()))
 draft=json.loads((HERE/'repair/euclid_correct.json').read_text());check=json.loads((HERE/'repair/euclid_correct.debug.json').read_text());assert check['accepted']
 candidate=Path(check['proof_path']);target=Path(check['target_path'])
 assert sha(candidate)==check['source_sha256'] and sha(target)==check['target_sha256']
 assert candidate.read_text()==render(spec,draft['proof'],target.stem)
 drafts[node.id]=draft;sources[node.id]={'origin':'Original frozen original interrupted Euclid wrapper target; local unchanged original live proof, interrupted before acceptance repair passed independent exact-target/axiom audit','source_draft_sha256':sha(HERE/'repair/euclid_correct.json')}
 async def propose(node,prompt,attempt):
  if node.id in drafts:
   assert node.id not in replays,'Deterministic proof did not replay; inspect before retry'
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
 save(HERE/'REPAIR_REPLAY.json',{'sources':sources,'replayed_nodes':replays,'live_model_attempts':calls,'statements_changed':False,'normal_dual_retrieval_preserved':True,'result':result})
 print(json.dumps(result,indent=2),flush=True)
