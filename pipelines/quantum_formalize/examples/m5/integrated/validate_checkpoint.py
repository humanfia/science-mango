"""Build the integrated module and independently import every frozen statement."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

BASE = Path(__file__).resolve().parent
PROJECT = Path('/home/jing/m5-lean-integrated52-formalization')
provenance = json.loads((BASE / 'PROVENANCE.json').read_text())

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

build = subprocess.run(['/home/jing/.elan/bin/lake', 'build', 'M5Accepted'], cwd=PROJECT, capture_output=True, text=True, timeout=300)
(BASE / 'build.log').write_text(build.stdout + build.stderr)
assert build.returncode == 0, build.stdout + build.stderr
lines = ['import M5Accepted']
for entry in provenance['theorems']:
    receipt = json.loads((BASE.parent / entry['receipt']).read_text())
    declaration = receipt['result']['artifacts'][entry['node']]['payload']['declaration']
    statement = declaration.split(' : ', 1)[1].split(' := by\n', 1)[0]
    lines += [f'example : {statement} := {entry["name"]}', f'#print axioms {entry["name"]}']
source = '\n\n'.join(lines) + '\n'
(PROJECT / 'Acceptance.lean').write_text(source)
(BASE / 'lean/Acceptance.lean').write_text(source)
result = subprocess.run(['/home/jing/.elan/bin/lake', 'env', 'lean', 'Acceptance.lean'], cwd=PROJECT, capture_output=True, text=True, timeout=180)
output = result.stdout + result.stderr
(BASE / 'acceptance.log').write_text(output)
assert result.returncode == 0, output
axioms = {}
for entry in provenance['theorems']:
    name = entry['name']
    matches = re.findall("'" + re.escape(name) + r"' depends on axioms:\s*\[([^\]]*)\]", output)
    empty = f"'{name}' does not depend on any axioms" in output
    assert len(matches) + int(empty) == 1
    axioms[name] = [] if empty else [item.strip() for item in matches[0].split(',')]
    assert set(axioms[name]) <= {'propext', 'Classical.choice', 'Quot.sound'}
validation = {'accepted': True, 'theorem_count': len(axioms), 'combined_compile': True, 'independent_exact_type_import': True, 'axioms': axioms, 'source_sha256': sha(PROJECT / 'M5Accepted.lean'), 'olean_sha256': sha(PROJECT / '.lake/build/lib/lean/M5Accepted.olean'), 'acceptance_log_sha256': sha(BASE / 'acceptance.log'), 'm5_formalized': False}
(BASE / 'VALIDATION.json').write_text(json.dumps(validation, indent=2) + '\n')
print(f'{len(axioms)} exact imported types and axiom checks passed')
