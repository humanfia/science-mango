"""Assemble exact accepted42 source closure plus accepted37/44 for concrete recovery."""
from pathlib import Path
import json,hashlib,shutil
H=Path(__file__).resolve().parent;B=H.parent;P=Path('/home/jing/m5-lean-arithmetic-residue-recovery-formalization')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert json.loads((H/'ACCEPTED_IMPORTS.json').read_text())['accepted']
for name,digest in json.loads((B/'stage42/MANIFEST.json').read_text())['files'].items():assert sha(B/'stage42'/name)==digest
P.mkdir(exist_ok=True);files={}
for p in (B/'stage42/lean').iterdir():
 if p.is_file() and p.name not in {'GraphPreflight.lean','DependencyAudit.lean','Acceptance.lean'}:
  shutil.copy2(p,H/'lean'/p.name);files[p.name]=sha(p)
for stage,name in [('stage37','M5ResidueRecovery.lean'),('stage44','M5PrefixPartition.lean')]:
 p=B/stage/'lean'/name;shutil.copy2(p,H/'lean'/name);files[name]=sha(p)
lake=(H/'lean/lakefile.toml').read_text().replace('defaultTargets = ["M5ConditionalResidueCount"]','defaultTargets = ["M5ArithmeticResidueRecovery"]')
for name in ['M5ConditionalResidueCountAccepted','M5ResidueRecovery','M5ResidueRecoveryAccepted','M5PrefixPartition','M5PrefixPartitionAccepted','M5ArithmeticResidueRecovery']:
 lake+='\n[[lean_lib]]\nname = '+json.dumps(name)+'\n'
(H/'lean/lakefile.toml').write_text(lake)
for p in (H/'lean').iterdir():
 if p.is_file():shutil.copy2(p,P/p.name)
(P/'.lake').mkdir(exist_ok=True)
if not (P/'.lake/packages').exists():(P/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
(H/'DEPENDENCY_IMPORT.json').write_text(json.dumps({'accepted_imports':'ACCEPTED_IMPORTS.json','accepted_imports_sha256':sha(H/'ACCEPTED_IMPORTS.json'),'copied_files':files,'pending_dependencies':[],'proofs_changed':False},indent=2)+'\n')
