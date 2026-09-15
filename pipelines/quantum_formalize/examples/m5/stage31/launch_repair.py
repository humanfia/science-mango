from pathlib import Path
import json,os,subprocess,sys,tempfile
H=Path(__file__).resolve().parent
repo=H.parents[4]
P=Path('/home/jing/m5-lean-residue-count-formalization')
C=Path(tempfile.mkdtemp(prefix='cardinality-repair-',dir=P/'.humanize-formal-runs'))
g=json.loads((H/'graph.json').read_text());(C/'graph.json').write_text(json.dumps(g,indent=2)+'\n')
c={'project':str(P),'graph':str(C/'graph.json'),'output':str(C/'experiment'),'result_path':str(C/'result.json'),'concurrency':16,'rounds':5,'compile_timeout':180,'turn_timeout':600}
(C/'config.json').write_text(json.dumps(c,indent=2)+'\n');(C/'humanize-home').mkdir()
env=dict(os.environ,HUMANIZE_HOME=str(C/'humanize-home'),HUMANIZE_SENTRY='off',PYTHONDONTWRITEBYTECODE='1')
env['PYTHONPATH']=str(repo)+os.pathsep+env.get('PYTHONPATH','')
(H/'REPAIR_LAUNCH.json').write_text(json.dumps({'launcher':str(C),'config':c},indent=2)+'\n')
print('launcher '+str(C),flush=True)
r=subprocess.run([str(Path(sys.executable).parent/'hmz'),'exec','-f',str(H/'repair_flow'),'-c',str(C/'config.json'),'-a','cli=codex,model=gpt-6-astra,effort=medium,permission=read-only,web_search=false','Continue original frozen A DAG, replay verified proofs and prove downstream targets.'],cwd=C,env=env)
sys.exit(r.returncode)
