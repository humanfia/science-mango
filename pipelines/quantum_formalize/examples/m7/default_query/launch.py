from pathlib import Path
import json,os,subprocess,sys,tempfile
H=Path(__file__).resolve().parent;repo=H.parents[4];P=Path('/home/jing/m7-lean-default-query-formalization')
assert json.loads((H/'DEPENDENCY_GATE.json').read_text())['resolved'], 'actual_presentation9 proof gate is pending'
(P/'.humanize-formal-runs').mkdir(exist_ok=True)
C=Path(tempfile.mkdtemp(prefix='dag-launcher-',dir=P/'.humanize-formal-runs'));(C/'graph.json').write_bytes((H/'graph.json').read_bytes())
c={'project':str(P),'graph':str(C/'graph.json'),'output':str(C/'experiment'),'result_path':str(C/'result.json'),'concurrency':2,'rounds':5,'compile_timeout':600,'turn_timeout':600};(C/'config.json').write_text(json.dumps(c,indent=2)+'\n');(C/'humanize-home').mkdir()
env=dict(os.environ,HUMANIZE_HOME=str(C/'humanize-home'),HUMANIZE_SENTRY='off',PYTHONDONTWRITEBYTECODE='1');env['PYTHONPATH']=str(repo)+os.pathsep+env.get('PYTHONPATH','');env['PATH']='/home/jing/.elan/bin:'+env.get('PATH','')
argv=[str(Path(sys.executable).parent/'hmz'),'exec','-f',str(repo/'pipelines/quantum_formalize_dag'),'-c',str(C/'config.json'),'-a','cli=codex,model=gpt-6-astra,effort=medium,permission=read-only,web_search=false','Prove frozen actual M7 default query semantics using literal signature/locality and actual M6 quantum distance, including NoLogical policy, explicit invalid-signature rejection, all Pareto/lex ties, and unique actual presentations. Preserve targets and definitions.']
with (C/'launcher.log').open('wb') as log:run=subprocess.Popen(argv,cwd=C,env=env,stdin=subprocess.DEVNULL,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
record={'launcher':str(C),'pid':run.pid,'detached':True,'config':c};(H/'LAUNCH.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record))
