from pathlib import Path
import time,subprocess,json
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914')
parent=repo/'pipelines/quantum_formalize/examples/m8/diagonal/experiment'
while not (parent/'MANIFEST.json').exists(): time.sleep(30)
r=json.loads((parent/'result.json').read_text())
assert all(r[k] for k in ['assembly_accepted','environment_unchanged','experiment_passed'])
subprocess.run(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python','/home/jing/m8_prepare_diagonal_polynomial.py'],cwd=repo,check=True)
