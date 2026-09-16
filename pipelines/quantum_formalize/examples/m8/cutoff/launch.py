from pathlib import Path
import json,os,subprocess,sys,tempfile
H=Path(__file__).resolve().parent;repo=H.parents[4];P=Path('/home/jing/m8-lean-cutoff-formalization')
assert json.loads((H/'PREFLIGHT.json').read_text())['accepted']
(P/'.humanize-formal-runs').mkdir(exist_ok=True)
C=Path(tempfile.mkdtemp(prefix='dag-launcher-',dir=P/'.humanize-formal-runs'));(C/'graph.json').write_bytes((H/'graph.json').read_bytes())
c={'project':str(P),'graph':str(C/'graph.json'),'output':str(C/'experiment'),'result_path':str(C/'result.json'),'concurrency':2,'rounds':5,'compile_timeout':600,'turn_timeout':600};(C/'config.json').write_text(json.dumps(c,indent=2)+'\n');(C/'humanize-home').mkdir()
env=dict(os.environ,HUMANIZE_HOME=str(C/'humanize-home'),HUMANIZE_SENTRY='off',PYTHONDONTWRITEBYTECODE='1');env['PYTHONPATH']=str(repo)+os.pathsep+env.get('PYTHONPATH','');env['PATH']='/home/jing/.elan/bin:'+env.get('PATH','')
argv=[str(Path(sys.executable).parent/'hmz'),'exec','-f',str(repo/'pipelines/quantum_formalize_dag'),'-c',str(C/'config.json'),'-a','cli=codex,model=gpt-6-astra,effort=medium,permission=read-only,web_search=false','Prove the eight frozen revised M8 cutoff arithmetic targets. Preserve fixed min(N-1,floor(log2(N+1))) and all exact statements; no arbitrary resource oracle or stronger M9 scope. Return tactic lines only.']
with (C/'launcher.log').open('wb') as log:run=subprocess.Popen(argv,cwd=C,env=env,stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
record={'launcher':str(C),'pid':run.pid,'detached':True,'config':c};(H/'LAUNCH.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
