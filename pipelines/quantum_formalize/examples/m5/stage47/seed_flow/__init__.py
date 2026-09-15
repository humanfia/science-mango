"""Replay checked generic helpers through frozen acceptance; prove concrete links live."""
import asyncio,hashlib,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(HERE.parents[4]))
from hmz.flows import flow
from pipelines.quantum_formalize_dag import Agents,Config
from pipelines.quantum_formalize.engine import Draft,save
from pipelines.quantum_formalize.dag_runner import run_graph,load_graph

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
@flow
async def seeded_dag(agents:Agents,task:str,config:Config|None=None)->None:
 if config is None:raise ValueError('config required')
 graph,nodes=load_graph(config.graph)
 assert json.loads((HERE/'PREFLIGHT.json').read_text())['ready_for_full_experiment']
 seeds=HERE/'root_helpers';checks=json.loads((seeds/'CHECKS.json').read_text())
 assert sha(HERE/'graph.json')==checks['target_graph_sha256']
 assert graph==json.loads((HERE/'graph.json').read_text())
 for name,digest in checks['files'].items():assert sha(seeds/name)==digest
 original=(seeds/'Definitions.txt').read_text();actual=(HERE/'lean/M5ArithmeticResidueRecovery.lean').read_text()
 original=original[original.index('/-- Generic'):original.index('end M5.ArithmeticResidueRecovery')].strip()
 actual=actual[actual.index('/-- Generic'):actual.index('noncomputable def wordValid')].strip()
 assert original==actual,'Generic mathematical definitions must match checked seed source exactly'
 draftpaths={'completion_word_split':seeds/'split.draft.json','completion_prefix_card':seeds/'card.draft.json'}
 drafts={n:json.loads(p.read_text()) for n,p in draftpaths.items()}
 replayed=[];calls=[]
 async def propose(node,prompt,attempt):
  if node.id in drafts:
   assert node.id not in replayed,'Checked seed failed frozen acceptance; inspect before retry'
   replayed.append(node.id);return drafts[node.id]
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
 save(HERE/'SEED_REPLAY.json',{'seed_checks_sha256':sha(seeds/'CHECKS.json'),'draft_sha256':{n:sha(p) for n,p in draftpaths.items()},'replayed_nodes':replayed,'live_model_attempts':calls,'statements_changed':False,'result':result})
 print(json.dumps(result,indent=2),flush=True)
