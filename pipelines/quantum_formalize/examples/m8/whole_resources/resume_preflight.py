from pathlib import Path
import subprocess,json,hashlib
b=Path(__file__).resolve().parent
repo=b.parents[4]
py='/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python'
subprocess.run([py,str(b/'preflight.py')],cwd=repo,check=True)
(b/'FREEZE.json').write_text(json.dumps({'graph_sha256':hashlib.sha256((b/'graph.json').read_bytes()).hexdigest(),'definition_sha256':hashlib.sha256((b/'lean/M8WholeResources.lean').read_bytes()).hexdigest(),'targets':8,'contexts_empty':True,'parent_canonical_gates_resolved':True},indent=2)+'\n')
subprocess.run([py,str(b/'launch.py')],cwd=repo,check=True)
