#!/usr/bin/env python3
"""Rebuild the accepted original M8 proof in a fresh, pinned Lean project.

This tool runs only after canonical root acceptance. It never invokes a model.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repo',type=Path,default=Path(__file__).resolve().parents[5])
parser.add_argument('--project',type=Path,required=True,help='New or empty directory')
parser.add_argument('--lake',default='lake')
parser.add_argument('--cache',action='store_true',help='Download the pinned Mathlib build cache before compilation')
args=parser.parse_args()
repo=args.repo.resolve();stage=repo/'pipelines/quantum_formalize/examples/m8/final';project=args.project.resolve()
subprocess.run([sys.executable,str(stage/'audit_root.py'),'--repo',str(repo),'--check-only'],check=True)
assert not project.exists() or (project.is_dir() and not any(project.iterdir())), 'Refusing to overwrite a populated project'
project.mkdir(parents=True,exist_ok=True)
env=json.loads((stage/'experiment/environment.json').read_text())
for name,digest in env.items():
 src=stage/'lean'/name if name.endswith('.lean') else stage/name
 assert src.is_file(), (name,'missing frozen project source')
 assert hashlib.sha256(src.read_bytes()).hexdigest()==digest,(name,'frozen source changed')
 shutil.copy2(src,project/name)
shutil.copy2(stage/'experiment/AcceptedExperiment.lean',project/'M8FinalAccepted.lean')
s=(project/'lakefile.toml').read_text();s=re.sub(r'^defaultTargets = .*','defaultTargets = ["M8FinalAccepted"]',s,flags=re.M)
s+='\n[[lean_lib]]\nname = "M8FinalAccepted"\n';(project/'lakefile.toml').write_text(s)
(project/'CheckRoot.lean').write_text('import M8FinalAccepted\nexample : M8.Final.OriginalM8 := M8.Final.original_m8\n#print axioms M8.Final.original_m8\n')
if args.cache:subprocess.run([args.lake,'exe','cache','get'],cwd=project,check=True)
subprocess.run([args.lake,'build'],cwd=project,check=True)
subprocess.run([args.lake,'env','lean','CheckRoot.lean'],cwd=project,check=True)
print('Fresh Lean root rebuild passed:',project)
