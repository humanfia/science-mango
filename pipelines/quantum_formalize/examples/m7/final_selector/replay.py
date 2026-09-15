from pathlib import Path
import json,os,sys,tempfile,subprocess,shutil,hashlib
H=Path(__file__).resolve().parent;R=H.parents[4];P=Path('/home/jing/m7-lean-final-selector-formalization');sys.path.insert(0,str(R))
from pipelines.quantum_formalize.dag_runner import load_graph
old=P/'.humanize-formal-runs/dag-launcher-vegter9r';oldr=json.loads((old/'result.json').read_text());assert oldr['status']=='finished'
state=json.loads((old/'experiment/nodes/state.json').read_text());assert all(row['accepted'] for k,row in state['nodes'].items() if k!='presentation_exact')
repair=Path(sys.argv[1]);v=json.loads((repair/'verification.json').read_text());assert v['accepted'] and set(v['axioms']) <= {'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# Archive every original receipt, draft, source, retrieval failure and successful late live proof.
A=H/'experiments/initial_retrieval_failure';shutil.copytree(old/'experiment',A);shutil.copy2(old/'result.json',A/'result.json');shutil.copy2(old/'config.json',A/'config.json');shutil.copy2(old/'graph.json',A/'graph.json');shutil.copy2(old/'launcher.log',A/'launcher.log')
seeds={};origins=[]
for node,row in state['nodes'].items():
 work=Path(row['result']['work'])
 for f in work.rglob('*'):
  if f.is_file() and f.suffix in {'.lean','.json'}:
   dest=A/'node_runs'/node/f.relative_to(work);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,dest)
 if row['accepted']:
  d=Path(row['result']['attempts'][-1]['proof_path']).parent/'draft.json';seeds[node]=json.loads(d.read_text());origins.append({'node':node,'source':'unchanged original live accepted draft','draft_sha256':sha(d)})
m={str(f.relative_to(A)):sha(f)for f in A.rglob('*')if f.is_file()};(A/'MANIFEST.json').write_text(json.dumps({'file_count':len(m),'files':m},indent=2)+'\n')
D=H/'repairs/presentation_exact';D.mkdir(parents=True,exist_ok=True)
for f in repair.iterdir():
 if f.suffix in {'.lean','.json'}:shutil.copy2(f,D/f.name)
seeds['presentation_exact']=json.loads((repair/'draft.json').read_text());origins.append({'node':'presentation_exact','source':'original first draft plus explicit Boolean/decide rewrites and definitional equality, exact target normal-verified; original loop interrupted by retrieval_unavailable','draft_sha256':sha(repair/'draft.json'),'verification':v})
flow=P/'.humanize-formal-runs/replay_flow';flow.mkdir(exist_ok=True);shutil.copy2(R/'pipelines/quantum_formalize/examples/m6/transfer/trace/replay_flow/__init__.py',flow/'__init__.py')
C=Path(tempfile.mkdtemp(prefix='repaired-replay-',dir=P/'.humanize-formal-runs'));shutil.copy2(H/'graph.json',C/'graph.json');(C/'humanize-home').mkdir()
config={'project':str(P),'graph':str(C/'graph.json'),'output':str(C/'experiment'),'result_path':str(C/'result.json'),'concurrency':2,'rounds':5,'compile_timeout':600,'turn_timeout':600,'seed_proofs':seeds};(C/'config.json').write_text(json.dumps(config,indent=2)+'\n')
env=dict(os.environ,HUMANIZE_HOME=str(C/'humanize-home'),HUMANIZE_SENTRY='off',PYTHONDONTWRITEBYTECODE='1');env['PYTHONPATH']=str(R)+os.pathsep+env.get('PYTHONPATH','');env['PATH']='/home/jing/.elan/bin:'+env.get('PATH','')
with(C/'launcher.log').open('wb')as f:p=subprocess.Popen([str(Path(sys.executable).parent/'hmz'),'exec','-f',str(flow),'-c',str(C/'config.json'),'-a','cli=codex,model=gpt-6-astra,effort=medium,permission=read-only,web_search=false','Replay original live successes and the exact minimal presentation repair through normal frozen acceptance. Preserve all exact definitions and targets.'],cwd=C,env=env,stdin=subprocess.DEVNULL,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
record={'launcher':str(C),'pid':p.pid,'detached':True,'original_launcher':str(old),'targets_unchanged':True,'seeds':origins};(H/'REPLAY.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({'launcher':str(C),'pid':p.pid,'seeds':list(seeds)}))
