from pathlib import Path
import json,os,subprocess,sys,tempfile
H=Path(__file__).resolve().parent;repo=H.parents[4];P=Path('/home/jing/m7-lean-global-query-formalization')
assert json.loads((H.parent/'default_query/experiment/result.json').read_text())['experiment_passed'], 'Run after default8 completes to retain shared concurrency'
(P/'.humanize-formal-runs').mkdir(exist_ok=True)
C=Path(tempfile.mkdtemp(prefix='dag-launcher-',dir=P/'.humanize-formal-runs'));(C/'graph.json').write_bytes((H/'graph.json').read_bytes())
c={'project':str(P),'graph':str(C/'graph.json'),'output':str(C/'experiment'),'result_path':str(C/'result.json'),'concurrency':2,'rounds':5,'compile_timeout':600,'turn_timeout':600};(C/'config.json').write_text(json.dumps(c,indent=2)+'\n');(C/'humanize-home').mkdir()
env=dict(os.environ,HUMANIZE_HOME=str(C/'humanize-home'),HUMANIZE_SENTRY='off',PYTHONDONTWRITEBYTECODE='1');env['PYTHONPATH']=str(repo)+os.pathsep+env.get('PYTHONPATH','');env['PATH']='/home/jing/.elan/bin:'+env.get('PATH','')
argv=[str(Path(sys.executable).parent/'hmz'),'exec','-f',str(repo/'pipelines/quantum_formalize_dag'),'-c',str(C/'config.json'),'-a','cli=codex,model=gpt-6-astra,effort=medium,permission=read-only,web_search=false','Prove the frozen M7 global finite-family selector: all class/action comparisons, every tied class and action, and exact distinct physical presentations via the accepted factorized least-preimage algorithm. Preserve literal default query and all targets.']
with (C/'launcher.log').open('wb') as log:run=subprocess.Popen(argv,cwd=C,env=env,stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
record={'launcher':str(C),'pid':run.pid,'detached':True,'config':c};(H/'LAUNCH.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
