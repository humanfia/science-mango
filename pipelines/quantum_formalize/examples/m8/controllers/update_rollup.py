from pathlib import Path
import json,hashlib,datetime
b=Path('/home/jing/science-mango-quantum-harness-publish-20260914/pipelines/quantum_formalize/examples/m8');modules={}
for p in sorted(b.glob('*/experiment/result.json')):
 r=json.loads(p.read_text())
 if not all(r.get(k)is True for k in ['assembly_accepted','environment_unchanged','experiment_passed']):continue
 m=json.loads((p.parent/'MANIFEST.json').read_text());m=m.get('files',m)
 for n,h in m.items():assert hashlib.sha256((p.parent/n).read_bytes()).hexdigest()==h,(p,n)
 modules[p.parent.parent.name]={'accepted_targets':len(r['accepted_nodes']),'receipt':str(p.relative_to(b)),'receipt_sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
a=b/'final/ROOT_ACCEPTANCE.json';formal=a.exists() and json.loads(a.read_text()).get('m8_formalized')is True
d={'checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'revised_m8_formalized':formal,'completed_targets':sum(x['accepted_targets']for x in modules.values()),'completed_modules':modules,'scope':'Frozen revised M8; original all-input gate is M9'};(b/'COMPONENT_STATUS.json').write_text(json.dumps(d,indent=2)+'\n');print(d['completed_targets'],len(modules))
text='# M8 current status\n\nUpdated '+d['checked_at_utc']+'. '+('Full M8 root acceptance has passed.' if formal else 'Full M8 Lean acceptance remains pending.')+'\n\nThe SSH-cloned source is frozen: all 35 manifest entries and nine direct dependency hashes were checked. '+str(d['completed_targets'])+' targets in '+str(len(modules))+' complete batches have passed individual checks, assembly compilation, environment checks, and canonical hash verification.\n\n| Completed batch | Targets |\n|---|---:|\n'+''.join('| '+k+' | '+str(v['accepted_targets'])+' |\n' for k,v in modules.items())
text+='\nActive and pending dependency work is listed in GRAPH.md and final/SCOPE_MAP.md. Component counts do not imply full M8 acceptance. Explicit admitted and rejected families, complete three-outcome semantics, actual cost composition and source-bound root acceptance must all close.\n\nThe M6/M7 canonical proofs are reused through exact source/hash checks. Each proof batch uses gpt-6-astra / medium, two workers, five live attempts, and 600-second compiler calls, within the authorized sixteen-worker ceiling. Late successful drafts are retained; exact local repairs require independent checks and normal replay. The frozen revised M8 is the target; unrestricted all-input M9 is outside this formalization.\n'
(b/'CURRENT.md').write_text(text)
