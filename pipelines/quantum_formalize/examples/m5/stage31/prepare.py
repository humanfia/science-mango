"""Definitions and accepted imports only; stage29 remains a proof dependency gate."""
from pathlib import Path
import hashlib,json,shutil
H=Path(__file__).resolve().parent;B=H.parent;P=Path('/home/jing/m5-lean-residue-count-formalization')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
# stage23 portable tree contains unchanged90 plus verified16 and indicator definitions.
for stage in ['integrated90','stage23']:
 for name,digest in json.loads((B/stage/'MANIFEST.json').read_text())['files'].items():assert sha(B/stage/name)==digest
assert json.loads((H/'ACCEPTED_IMPORTS.json').read_text())['accepted']
P.mkdir(exist_ok=True)
files={}
for p in (B/'stage23/lean').iterdir():
 if p.is_file() and p.name not in {'GraphPreflight.lean','DependencyAudit.lean','Acceptance.lean'}:
  shutil.copy2(p,H/'lean'/p.name);files[p.name]=sha(p)
for stage,name in [('stage24','M5ArithmeticTuple.lean'),('stage29','M5AnchoredTupleCount.lean')]:
 p=B/stage/'lean'/name;shutil.copy2(p,H/'lean'/name);files[name]=sha(p)
lake=(H/'lean/lakefile.toml').read_text().replace('defaultTargets = ["M5PolynomialIndicator"]','defaultTargets = ["M5ResidueCount"]')
for name in ['M5PolynomialIndicatorAccepted','M5ArithmeticTuple','M5ArithmeticTupleAccepted','M5AnchoredTupleCount','M5ResidueCount']:
 lake+='\n[[lean_lib]]\nname = '+json.dumps(name)+'\n'
(H/'lean/lakefile.toml').write_text(lake)
for p in (H/'lean').iterdir():
 if p.is_file():shutil.copy2(p,P/p.name)
(P/'.lake').mkdir(exist_ok=True)
if not (P/'.lake/packages').exists():(P/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
(H/'DEPENDENCY_IMPORT.json').write_text(json.dumps({'accepted_imports':'ACCEPTED_IMPORTS.json','accepted_imports_sha256':sha(H/'ACCEPTED_IMPORTS.json'),'copied_files':files,'stage29_definitions_sha256':sha(H/'lean/M5AnchoredTupleCount.lean'),'stage29_proof_imported':False,'pending_dependencies':['stage29'],'proofs_changed':False},indent=2)+'\n')
