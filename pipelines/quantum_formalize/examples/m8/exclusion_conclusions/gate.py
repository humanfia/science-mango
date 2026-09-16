from pathlib import Path
import json,time,subprocess
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914')
base=repo/'pipelines/quantum_formalize/examples/m8'
parents=['solver','antipodal_family','exclusion_geometry','diagonal_polynomial']
while not all((base/n/'experiment/MANIFEST.json').exists() for n in parents): time.sleep(30)
for n in parents:
 r=json.loads((base/n/'experiment/result.json').read_text())
 assert all(r[k] for k in ['assembly_accepted','environment_unchanged','experiment_passed']),n
subprocess.run(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python','/home/jing/m8_prepare_exclusion_conclusions.py'],cwd=repo,check=True)
