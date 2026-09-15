from pathlib import Path
import os,sys,json,tempfile,subprocess,shutil
H=Path(__file__).resolve().parent
P=Path('/home/jing/m5-lean-arithmetic-workflow-formalization')
L=Path(tempfile.mkdtemp(prefix='order-bridge-repair-',dir=P/'.humanize-formal-runs'))
shutil.copy2(H/'graph.json',L/'graph.json')
config={'project':str(P),'graph':str(L/'graph.json'),'output':str(L/'experiment'),'result_path':str(L/'result.json'),'concurrency':16,'rounds':5,'compile_timeout':180,'turn_timeout':600}
(L/'config.json').write_text(json.dumps(config,indent=2)+'\n');(L/'humanize-home').mkdir()
env=dict(os.environ,HUMANIZE_HOME=str(L/'humanize-home'),HUMANIZE_SENTRY='off',PYTHONDONTWRITEBYTECODE='1')
env['PYTHONPATH']=str(H.parents[4])+os.pathsep+env.get('PYTHONPATH','')
argv=[str(Path(sys.executable).parent/'hmz'),'exec','-f',str(H/'repair_flow'),'-c',str(L/'config.json'),'-a','cli=codex,model=gpt-6-astra,effort=medium,permission=read-only,web_search=false','Prove the original M5 arithmetic birth and arbitrary-order targets. Preserve exact statements.']
print(json.dumps({'launcher':str(L),'concurrency':16,'model':'gpt-6-astra','effort':'medium'}),flush=True)
sys.exit(subprocess.run(argv,cwd=L,env=env).returncode)
