"""Prepare conditional-A project from accepted31/40 closures and unchanged definitions."""
from pathlib import Path
import json,hashlib,shutil
H=Path(__file__).resolve().parent;B=H.parent;P=Path('/home/jing/m5-lean-conditional-residue-count-formalization')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name,digest in json.loads((B/'stage31/MANIFEST.json').read_text())['files'].items():assert sha(B/'stage31'/name)==digest
assert json.loads((H/'ACCEPTED_IMPORTS.json').read_text())['accepted']
P.mkdir(exist_ok=True);files={}
for p in (B/'stage31/lean').iterdir():
 if p.is_file() and p.name not in {'GraphPreflight.lean','DependencyAudit.lean','Acceptance.lean'}:
  shutil.copy2(p,H/'lean'/p.name);files[p.name]=sha(p)
for name in ['M5AnchoredTupleCount.lean','M5ArithmeticTuple.lean']:
 assert (H/'lean'/name).read_bytes()==(B/'stage40/lean'/name).read_bytes()
p=B/'stage40/lean/M5TupleCompletion.lean';shutil.copy2(p,H/'lean'/p.name);files[p.name]=sha(p)
lake=(H/'lean/lakefile.toml').read_text().replace('defaultTargets = ["M5ResidueCount"]','defaultTargets = ["M5ConditionalResidueCount"]')
for name in ['M5ResidueCountAccepted','M5TupleCompletion','M5TupleCompletionAccepted','M5ConditionalResidueCount']:
 lake+='\n[[lean_lib]]\nname = '+json.dumps(name)+'\n'
(H/'lean/lakefile.toml').write_text(lake)
for p in (H/'lean').iterdir():
 if p.is_file():shutil.copy2(p,P/p.name)
(P/'.lake').mkdir(exist_ok=True)
if not (P/'.lake/packages').exists():(P/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
(H/'DEPENDENCY_IMPORT.json').write_text(json.dumps({'accepted_imports':'ACCEPTED_IMPORTS.json','accepted_imports_sha256':sha(H/'ACCEPTED_IMPORTS.json'),'copied_files':files,'source_definition_equivalence_checked':['M5AnchoredTupleCount.lean','M5ArithmeticTuple.lean'],'pending_dependencies':[],'proofs_changed':False},indent=2)+'\n')
