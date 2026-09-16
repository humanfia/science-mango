from pathlib import Path
import json,os,tempfile,subprocess,sys,shutil
from pipelines.quantum_humanize._runtime import runtime_pin
from pipelines.quantum_formalize.dag_runner import load_graph
runtime_pin()
module,project,concurrency=sys.argv[1:];repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');out=repo/'pipelines/quantum_formalize/examples/m8'/module;p=Path('/home/jing/m8-lean-'+project+'-formalization');load_graph(out/'graph.json');runs=p/'.humanize-formal-runs';runs.mkdir(exist_ok=True);flow=runs/'batch_flow';flow.mkdir(exist_ok=True);shutil.copy2(repo/'pipelines/quantum_formalize/examples/m6/transfer/trace/replay_flow/__init__.py',flow/'__init__.py');
if os.environ.get('M8_BROAD_RETRIEVAL') == '1':
 code=(flow/'__init__.py').read_text().replace('from pipelines.quantum_formalize.dag_runner import run_graph','from pipelines.quantum_formalize.dag_runner import run_graph\nfrom pipelines.quantum_formalize.search import search_with_fallback').replace('timeout=config.compile_timeout)', 'timeout=config.compile_timeout, search=lambda queries: search_with_fallback(queries, fallback_queries=["algebra"]))')
 (flow/'__init__.py').write_text(code)
c=Path(tempfile.mkdtemp(prefix=module.replace('/','-')+'-',dir=runs));shutil.copy2(out/'graph.json',c/'graph.json');home=c/'humanize-home';home.mkdir();config={'project':str(p),'graph':str(c/'graph.json'),'output':str(c/'experiment'),'result_path':str(c/'result.json'),'concurrency':int(concurrency),'rounds':5,'compile_timeout':int(os.environ.get('M8_COMPILE_TIMEOUT','180')),'turn_timeout':600};(c/'config.json').write_text(json.dumps(config,indent=2));env=dict(os.environ,HUMANIZE_HOME=str(home),HUMANIZE_SENTRY='off',PYTHONDONTWRITEBYTECODE='1');env['PYTHONPATH']=str(repo)+os.pathsep+env.get('PYTHONPATH','');env['PATH']='/home/jing/.elan/bin:'+env['PATH']
with(c/'launch.log').open('w') as log:
 proc=subprocess.Popen([str(Path(sys.executable).parent/'hmz'),'exec','-f',str(flow),'-c',str(c/'config.json'),'-a','cli=codex,model=gpt-6-astra,effort=medium,permission=read-only,web_search=false','Prove exactly the frozen revised M8 component targets. Preserve all successes and original scope; no changed definitions or additional premises.'],cwd=c,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
r={'launcher':str(c),'pid':proc.pid,'detached':True,'config':config};(out/'LAUNCH.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({'launcher':str(c),'pid':proc.pid}))
