from pathlib import Path
import json,shutil,hashlib,sys
H=Path(__file__).resolve().parent
C=Path(sys.argv[1]); A=H/'experiment'
r=json.loads((C/'result.json').read_text())
assert r['experiment_passed'] and r['assembly_accepted'] and r['environment_unchanged']
assert len(r['accepted_nodes'])==2
shutil.copytree(C/'experiment',A)
shutil.copy2(C/'result.json',A/'result.json');shutil.copy2(H/'graph.json',A/'graph.json')
s=json.loads((A/'nodes/state.json').read_text())
for n,record in s['nodes'].items():
 assert record['accepted']
 w=Path(record['result']['work'])
 for p in w.rglob('*'):
  if p.is_file() and p.suffix in ['.json','.lean']:
   dest=A/'node_runs'/n/p.relative_to(w);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dest)
m={str(p.relative_to(A)):hashlib.sha256(p.read_bytes()).hexdigest() for p in A.rglob('*') if p.is_file()}
(A/'MANIFEST.json').write_text(json.dumps({'file_count':len(m),'files':m},indent=2)+'\n')
print(json.dumps({'accepted_nodes':r['accepted_nodes'],'canonical_files':len(m),'canonical':str(A)}))
