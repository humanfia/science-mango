"""Prepare definition-only stage20 project from hash-verified immutable checkpoint72."""
from pathlib import Path
import hashlib,json,shutil
HERE=Path(__file__).resolve().parent
BASE=HERE.parent
PROJECT=Path('/home/jing/m5-lean-arithmetic-subset-formalization')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
save=lambda p,x:p.write_text(json.dumps(x,indent=2)+'\n')
checkpoint=BASE/'integrated72'
manifest=json.loads((checkpoint/'MANIFEST.json').read_text())
for name,h in manifest['files'].items():assert sha(checkpoint/name)==h
validation=json.loads((checkpoint/'VALIDATION.json').read_text())
assert validation['accepted'] and validation['theorem_count']==72
PROJECT.mkdir(exist_ok=True)
files={}
for p in (checkpoint/'lean').iterdir():
 if p.is_file() and p.name!='Acceptance.lean':
  shutil.copy2(p,PROJECT/p.name);shutil.copy2(p,HERE/'lean'/p.name);files[p.name]=sha(p)
p=BASE/'stage14/lean/M5SubsetCharacter.lean'
shutil.copy2(p,PROJECT/p.name);shutil.copy2(p,HERE/'lean'/p.name);files[p.name]=sha(p)
shutil.copy2(HERE/'lean/M5ArithmeticSubset.lean',PROJECT/'M5ArithmeticSubset.lean')
shutil.copy2(HERE/'lean/M5SubsetCountAccepted.lean',PROJECT/'M5SubsetCountAccepted.lean')
lake=(PROJECT/'lakefile.toml').read_text().replace('defaultTargets = ["M5Checkpoint72"]','defaultTargets = ["M5ArithmeticSubset"]')
for name in ['M5SubsetCharacter','M5SubsetCountAccepted','M5ArithmeticSubset']:
 lake+='\n[[lean_lib]]\nname = '+json.dumps(name)+'\n'
(PROJECT/'lakefile.toml').write_text(lake);(HERE/'lean/lakefile.toml').write_text(lake)
(PROJECT/'.lake').mkdir(exist_ok=True)
cache=PROJECT/'.lake/packages'
if not cache.exists():cache.symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
save(HERE/'DEPENDENCY_IMPORT.json',{'checkpoint':'../integrated72','checkpoint_validation_sha256':sha(checkpoint/'VALIDATION.json'),'checkpoint_manifest_sha256':sha(checkpoint/'MANIFEST.json'),'accepted_theorems':72,'copied_files':files,'stage14_definitions_sha256':sha(p),'pending_proof':None,'stage14_proof_imported':True,'stage14_proof_provenance':'STAGE14_DEPENDENCY_IMPORT.json','stage14_proof_provenance_sha256':sha(HERE/'STAGE14_DEPENDENCY_IMPORT.json'),'proofs_changed':False})
