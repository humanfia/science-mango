import asyncio,hashlib,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(HERE.parents[4]))
from hmz.flows import flow
from pipelines.quantum_formalize_dag import Agents,Config
from pipelines.quantum_formalize.engine import Spec,Draft,render,save
from pipelines.quantum_formalize.dag_runner import run_graph,load_graph
ARCHIVE=HERE/'experiments/target_compiler_timeout'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
@flow
async def resume_original_drafts(agents:Agents,task:str,config:Config|None=None)->None:
 if config is None:raise ValueError('config required')
 graph,nodes=load_graph(config.graph);assert graph==json.loads((ARCHIVE/'graph.json').read_text())
 for name,h in json.loads((ARCHIVE/'MANIFEST.json').read_text()).items():assert sha(ARCHIVE/name)==h
 state=json.loads((ARCHIVE/'nodes/state.json').read_text());drafts={};sources={};replays=[];calls=[]
 for node in nodes:
  rec=state['nodes'][node.id];r=rec.get('result',{})
  if not r.get('attempts'):continue
  assert not rec['accepted'] and r['attempts'][0]['stage']=='compiler_timeout'
  spec=Spec.model_validate(json.loads((ARCHIVE/'nodes'/node.id/'resolved-spec.json').read_text()));assert spec.statement==node.spec['statement']
  folder=ARCHIVE/'node_runs'/node.id/'attempt-001';draft=json.loads((folder/'draft.json').read_text());cand=next(folder.glob('Candidate_*.lean'));target=next(folder.glob('FrozenTarget_*.lean'))
  assert cand.read_text()==render(spec,draft['proof'],target.stem)
  drafts[node.id]=draft;sources[node.id]={'origin':'Unchanged first live draft; previous frozen-target compilation timed out before proof checking; no inherited acceptance claimed','draft_sha256':sha(folder/'draft.json'),'source_sha256':sha(cand),'target_sha256':sha(target)}
 async def propose(node,prompt,attempt):
  if node.id in drafts and node.id not in replays:
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
 save(Path(config.result_path),result);save(HERE/'REPLAY.json',{'sources':sources,'replayed_original_drafts':replays,'live_model_attempts':calls,'statements_changed':False,'normal_dual_retrieval_preserved':True,'result':result});print(json.dumps(result,indent=2),flush=True)
