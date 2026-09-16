from pathlib import Path
import json,hashlib,shutil,subprocess,sys,os,tempfile,time
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');h=repo/'pipelines/quantum_formalize/examples/m8/whole_resources';p=Path('/home/jing/m8-lean-whole-resources-formalization');old=p/'.humanize-formal-runs/dag-launcher-kzrr8zro'
while not(old/'result.json').exists():time.sleep(15)
r=json.loads((old/'result.json').read_text());assert not r['experiment_passed']
a=h/'experiments/initial_five_proof_failures';shutil.copytree(old/'experiment',a);shutil.copy2(old/'result.json',a/'result.json');shutil.copy2(h/'graph.json',a/'graph.json')
s=json.loads((a/'nodes/state.json').read_text());seeds={};origins={}
for n,rec in s['nodes'].items():
 result=rec.get('result',{});work=result.get('work')
 if work:
  for f in Path(work).rglob('*'):
   if f.is_file()and f.suffix in ['.json','.lean']:
    d=a/'node_runs'/n/f.relative_to(work);d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,d)
 if rec['accepted']:
  att=result['attempts'][-1];draft=Path(att['proof_path']).parent/'draft.json';seeds[n]=json.loads(draft.read_text());origins[n]={'draft':str(draft),'sha256':hashlib.sha256(draft.read_bytes()).hexdigest(),'source':'accepted live candidate, unchanged'}
for node,folder in [('charge_length','charge-length-repair-v9h9axdi'),('original_preprocess_bound','original-cost-repair-y79hre26')]:
 backup=p/'.humanize-formal-runs'/folder
 assert json.loads((backup/'verification.json').read_text())['accepted']
 failed=s['nodes'][node]['result'];assert len(failed['attempts'])==5 and all(not row['accepted'] for row in failed['attempts'])
 seeds[node]=json.loads((backup/'draft.json').read_text());origins[node]={'draft':str(backup/'draft.json'),'sha256':hashlib.sha256((backup/'draft.json').read_bytes()).hexdigest(),'source':'exact verifier accepted narrow tactic repair, only after five actual live proof drafts failed'}
 repair=h/'repairs'/node;repair.mkdir(parents=True,exist_ok=True)
 for file in backup.iterdir():
  if file.is_file() and file.suffix in ['.json','.lean']:shutil.copy2(file,repair/file.name)
 (repair/'USE.json').write_text(json.dumps({'five_live_drafts_exhausted':True,'new_normal_replay_required':True,'no_target_or_definition_change':True},indent=2)+'\n')
files={str(f.relative_to(a)):hashlib.sha256(f.read_bytes()).hexdigest()for f in a.rglob('*')if f.is_file()};(a/'MANIFEST.json').write_text(json.dumps({'file_count':len(files),'files':files},indent=2)+'\n')
flow=p/'.humanize-formal-runs/resume_flow';flow.mkdir(exist_ok=True);code=(repo/'pipelines/quantum_formalize/examples/m6/transfer/trace/replay_flow/__init__.py').read_text().replace('from pipelines.quantum_formalize.dag_runner import run_graph','from pipelines.quantum_formalize.dag_runner import run_graph\nfrom pipelines.quantum_formalize.search import search_with_fallback').replace('timeout=config.compile_timeout)', 'timeout=config.compile_timeout, search=lambda queries: search_with_fallback(queries, fallback_queries=["algebra"]))');(flow/'__init__.py').write_text(code)
c=Path(tempfile.mkdtemp(prefix='repair-replay-',dir=p/'.humanize-formal-runs'));shutil.copy2(h/'graph.json',c/'graph.json');cfg={'project':str(p),'graph':str(c/'graph.json'),'output':str(c/'experiment'),'result_path':str(c/'result.json'),'concurrency':2,'rounds':5,'compile_timeout':600,'turn_timeout':600,'seed_proofs':seeds};(c/'config.json').write_text(json.dumps(cfg,indent=2)+'\n');(c/'humanize-home').mkdir();env=dict(os.environ,HUMANIZE_HOME=str(c/'humanize-home'),HUMANIZE_SENTRY='off',PYTHONDONTWRITEBYTECODE='1');env['PYTHONPATH']=str(repo)+os.pathsep+env.get('PYTHONPATH','');env['PATH']='/home/jing/.elan/bin:'+env.get('PATH','')
with(c/'launcher.log').open('wb')as log:proc=subprocess.Popen([str(Path(sys.executable).parent/'hmz'),'exec','-f',str(flow),'-c',str(c/'config.json'),'-a','cli=codex,model=gpt-6-astra,effort=medium,permission=read-only,web_search=false','Resume the unchanged exact whole-resource goals after five actual proof drafts failed for two helper targets. Preserve all live successes; prove unresolved goals normally, no definition changes.'],cwd=c,env=env,stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
record={'launcher':str(c),'pid':proc.pid,'detached':True,'config':cfg,'seed_origins':origins,'reason':'all five remaining normal live proof drafts exhausted; preserve original live successes and replay exact verified narrow repair through normal independent acceptance','original_archive':str(a)};(h/'REPAIR_REPLAY.json').write_text(json.dumps(record,indent=2)+'\n');shutil.copy2(h/'LAUNCH.json',h/'INITIAL_LAUNCH.json');(h/'LAUNCH.json').write_text(json.dumps(record,indent=2)+'\n');shutil.copy2(__file__,h/'repair_replay.py');shutil.copytree(flow,h/'resume_flow',dirs_exist_ok=True);print(json.dumps({'launcher':str(c),'pid':proc.pid,'seeds':list(seeds),'original_files':len(files)}),flush=True)
