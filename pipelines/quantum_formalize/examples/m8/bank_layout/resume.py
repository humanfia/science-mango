from pathlib import Path
import json,hashlib,shutil,subprocess,sys,os,tempfile,time
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');h=repo/'pipelines/quantum_formalize/examples/m8/bank_layout';p=Path('/home/jing/m8-lean-bank-layout-formalization');old=p/'.humanize-formal-runs/dag-launcher-afvf4bhq'
while not(old/'result.json').exists():time.sleep(15)
r=json.loads((old/'result.json').read_text());assert not r['experiment_passed']
a=h/'experiments/initial_retrieval_failure';shutil.copytree(old/'experiment',a);shutil.copy2(old/'result.json',a/'result.json');shutil.copy2(h/'graph.json',a/'graph.json')
s=json.loads((a/'nodes/state.json').read_text());seeds={};origins={}
for n,rec in s['nodes'].items():
 result=rec.get('result',{});work=result.get('work')
 if work:
  for f in Path(work).rglob('*'):
   if f.is_file()and f.suffix in ['.json','.lean']:
    d=a/'node_runs'/n/f.relative_to(work);d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(f,d)
 if rec['accepted']:
  att=result['attempts'][-1];draft=Path(att['proof_path']).parent/'draft.json';seeds[n]=json.loads(draft.read_text());origins[n]={'draft':str(draft),'sha256':hashlib.sha256(draft.read_bytes()).hexdigest(),'source':'accepted live candidate, unchanged'}
files={str(f.relative_to(a)):hashlib.sha256(f.read_bytes()).hexdigest()for f in a.rglob('*')if f.is_file()};(a/'MANIFEST.json').write_text(json.dumps({'file_count':len(files),'files':files},indent=2)+'\n')
flow=p/'.humanize-formal-runs/resume_flow';flow.mkdir(exist_ok=True);code=(repo/'pipelines/quantum_formalize/examples/m6/transfer/trace/replay_flow/__init__.py').read_text().replace('from pipelines.quantum_formalize.dag_runner import run_graph','from pipelines.quantum_formalize.dag_runner import run_graph\nfrom pipelines.quantum_formalize.search import search_with_fallback').replace('timeout=config.compile_timeout)', 'timeout=config.compile_timeout, search=lambda queries: search_with_fallback(queries, fallback_queries=["algebra"]))');(flow/'__init__.py').write_text(code)
c=Path(tempfile.mkdtemp(prefix='live-resume-',dir=p/'.humanize-formal-runs'));shutil.copy2(h/'graph.json',c/'graph.json');cfg={'project':str(p),'graph':str(c/'graph.json'),'output':str(c/'experiment'),'result_path':str(c/'result.json'),'concurrency':2,'rounds':5,'compile_timeout':600,'turn_timeout':600,'seed_proofs':seeds};(c/'config.json').write_text(json.dumps(cfg,indent=2)+'\n');(c/'humanize-home').mkdir();env=dict(os.environ,HUMANIZE_HOME=str(c/'humanize-home'),HUMANIZE_SENTRY='off',PYTHONDONTWRITEBYTECODE='1');env['PYTHONPATH']=str(repo)+os.pathsep+env.get('PYTHONPATH','');env['PATH']='/home/jing/.elan/bin:'+env.get('PATH','')
with(c/'launcher.log').open('wb')as log:proc=subprocess.Popen([str(Path(sys.executable).parent/'hmz'),'exec','-f',str(flow),'-c',str(c/'config.json'),'-a','cli=codex,model=gpt-6-astra,effort=medium,permission=read-only,web_search=false','Resume the unchanged exact bank-layout goals after external retrieval interruption. Preserve all live successes; prove unresolved goals normally, no definition changes.'],cwd=c,env=env,stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
record={'launcher':str(c),'pid':proc.pid,'detached':True,'config':cfg,'seed_origins':origins,'reason':'external retrieval unavailable after one failed workspace draft; only genuinely accepted live candidates replayed; no local repair seeded','original_archive':str(a)};(h/'RESUME.json').write_text(json.dumps(record,indent=2)+'\n');shutil.copy2(h/'LAUNCH.json',h/'INITIAL_LAUNCH.json');(h/'LAUNCH.json').write_text(json.dumps(record,indent=2)+'\n');shutil.copy2(__file__,h/'resume.py');shutil.copytree(flow,h/'resume_flow',dirs_exist_ok=True);print(json.dumps({'launcher':str(c),'pid':proc.pid,'seeds':list(seeds),'original_files':len(files)}),flush=True)
