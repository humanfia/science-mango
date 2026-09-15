from pathlib import Path
import json,os,subprocess,sys,tempfile
H=Path(__file__).resolve().parent;repo=H.parents[4];P=Path('/home/jing/m7-lean-query-sectors-formalization')
assert all(json.loads((H.parent/s/'experiment/result.json').read_text())['experiment_passed'] for s in ['prefix_bits','residue_prefix'])
(P/'.humanize-formal-runs').mkdir(exist_ok=True)
C=Path(tempfile.mkdtemp(prefix='dag-launcher-',dir=P/'.humanize-formal-runs'));(C/'graph.json').write_bytes((H/'graph.json').read_bytes())
c={'project':str(P),'graph':str(C/'graph.json'),'output':str(C/'experiment'),'result_path':str(C/'result.json'),'concurrency':2,'rounds':5,'compile_timeout':600,'turn_timeout':600};(C/'config.json').write_text(json.dumps(c,indent=2)+'\n');(C/'humanize-home').mkdir()
env=dict(os.environ,HUMANIZE_HOME=str(C/'humanize-home'),HUMANIZE_SENTRY='off',PYTHONDONTWRITEBYTECODE='1');env['PYTHONPATH']=str(repo)+os.pathsep+env.get('PYTHONPATH','');env['PATH']='/home/jing/.elan/bin:'+env.get('PATH','')
argv=[str(Path(sys.executable).parent/'hmz'),'exec','-f',str(repo/'pipelines/quantum_formalize_dag'),'-c',str(C/'config.json'),'-a','cli=codex,model=gpt-6-astra,effort=medium,permission=read-only,web_search=false','Prove the five frozen concrete M7 query-sector targets. Multiset factor powerset must retain repeated factors; none means all monic divisors, some E is unchanged. Preserve actual full signature and exact query semantics. Return tactic lines only.']
with (C/'launcher.log').open('wb') as log:run=subprocess.Popen(argv,cwd=C,env=env,stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
record={'launcher':str(C),'pid':run.pid,'detached':True,'config':c};(H/'LAUNCH.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
