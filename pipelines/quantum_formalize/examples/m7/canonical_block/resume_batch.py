from pathlib import Path
import json,os,tempfile,subprocess,sys,shutil,hashlib
from pipelines.quantum_humanize._runtime import runtime_pin
from pipelines.quantum_formalize.dag_runner import load_graph
runtime_pin()
module,project,previous=sys.argv[1:];repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');out=repo/'pipelines/quantum_formalize/examples/m7'/module;p=Path('/home/jing/m7-lean-'+project+'-formalization');old=Path(previous);result=json.loads((old/'result.json').read_text());assert result['status']=='finished' and not result['experiment_passed']
history='experiments/replay_history/'+old.name
if not(out/history).exists():
 subprocess.run([sys.executable,'-c','exec(open("/tmp/m5_archive_batch.py").read().replace("examples/m5","examples/m7"))',module,str(old),history],cwd=repo,check=True)
archive=out/history
for name,h in json.loads((archive/'MANIFEST.json').read_text()).items():assert hashlib.sha256((archive/name).read_bytes()).hexdigest()==h,name
load_graph(old/'graph.json');seeds={};sources={};state=json.loads((old/'experiment/nodes/state.json').read_text())
for name,node in state['nodes'].items():
 work=node.get('result',{}).get('work')
 if not work:continue
 drafts=sorted(Path(work).glob('attempt-*/draft.json'))
 if not drafts:continue
 draft=drafts[-1];seeds[name]=json.loads(draft.read_text());sources[name]={'draft_path':str(draft),'sha256':hashlib.sha256(draft.read_bytes()).hexdigest(),'previously_accepted':bool(node.get('accepted')),'replay_requires_full_acceptance':True}
for receipt_path in json.loads(os.environ.get('M7_REPAIR_RECEIPTS','[]')):
 repair=json.loads(Path(receipt_path).read_text());a=Path(repair['directory']);v=repair['verdict'];assert v['accepted'] and v.get('environment_unchanged',True)
 spec=json.loads((a/'spec.json').read_text());draft=json.loads((a/'draft.json').read_text());node=next(n for n in json.loads((old/'graph.json').read_text())['nodes'] if n['spec']['name']==spec['name']);assert node['spec']['statement']==spec['statement']
 for field,key in [('proof_path','source_sha256'),('target_path','target_sha256')]:assert hashlib.sha256(Path(v[field]).read_bytes()).hexdigest()==v[key]
 dest=out/'repairs'/node['id'];dest.mkdir(parents=True,exist_ok=True)
 for f in a.iterdir():
  if f.suffix in ['.json','.lean']:shutil.copy2(f,dest/f.name)
 seeds[node['id']]=draft;sources[node['id']]={'origin':'Independently verified exact tactic repair; must pass normal replay','repair_receipt':receipt_path,'draft_sha256':hashlib.sha256((a/'draft.json').read_bytes()).hexdigest(),'replay_requires_full_acceptance':True}
runs=p/'.humanize-formal-runs';flow=runs/'retrieval_recovery_flow';flow.mkdir(exist_ok=True);code=(repo/'pipelines/quantum_formalize/examples/m6/transfer/trace/replay_flow/__init__.py').read_text();code=code.replace('from pipelines.quantum_formalize.dag_runner import run_graph','from pipelines.quantum_formalize.dag_runner import run_graph\nfrom pipelines.quantum_formalize.search import search_with_fallback');code=code.replace('timeout=config.compile_timeout)','timeout=config.compile_timeout,\n                             search=lambda queries: search_with_fallback(queries, fallback_queries=["algebra"]))');(flow/'__init__.py').write_text(code);(out/'retrieval_recovery_flow').mkdir(exist_ok=True);shutil.copy2(flow/'__init__.py',out/'retrieval_recovery_flow/__init__.py')
c=Path(tempfile.mkdtemp(prefix='retrieval-resume-',dir=runs));shutil.copy2(old/'graph.json',c/'graph.json');home=c/'humanize-home';home.mkdir();config={'project':str(p),'graph':str(c/'graph.json'),'output':str(c/'experiment'),'result_path':str(c/'result.json'),'concurrency':2,'rounds':5,'compile_timeout':600,'turn_timeout':600,'seed_proofs':seeds};(c/'config.json').write_text(json.dumps(config,indent=2));env=dict(os.environ,HUMANIZE_HOME=str(home),HUMANIZE_SENTRY='off',PYTHONDONTWRITEBYTECODE='1');env['PYTHONPATH']=str(repo)+os.pathsep+env.get('PYTHONPATH','');env['PATH']='/home/jing/.elan/bin:'+env['PATH']
with(c/'launch.log').open('w')as log:
 proc=subprocess.Popen([str(Path(sys.executable).parent/'hmz'),'exec','-f',str(flow),'-c',str(c/'config.json'),'-a','cli=codex,model=gpt-6-astra,effort=medium,permission=read-only,web_search=false','Resume the unchanged original M7 component targets. Replayed drafts require full normal acceptance. Preserve failures and successful late proofs; no changed definitions or added premises.'],cwd=c,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
r={'launcher':str(c),'pid':proc.pid,'detached':True,'original_launcher':str(old),'unchanged_graph_sha256':hashlib.sha256((old/'graph.json').read_bytes()).hexdigest(),'concurrency':2,'compile_timeout':600,'fallback_query':'algebra','sources':sources};(out/'RETRIEVAL_RESUME.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'launcher':str(c),'pid':proc.pid,'replayed_drafts':len(seeds)}))
