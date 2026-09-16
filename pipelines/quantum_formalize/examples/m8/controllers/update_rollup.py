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
if formal:
 acceptance=json.loads(a.read_text());assert acceptance['status']=='accepted'
 assert hashlib.sha256((b/'final/experiment/result.json').read_bytes()).hexdigest()==acceptance['root_result_sha256']
 assert hashlib.sha256((b/'final/experiment/MANIFEST.json').read_bytes()).hexdigest()==acceptance['root_manifest_sha256']
d={'checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'revised_m8_formalized':formal,'completed_targets':sum(x['accepted_targets']for x in modules.values()),'completed_modules':modules,'scope':'Frozen revised M8; original all-input gate is M9'}
if formal:d.update(root_theorem='M8.Final.original_m8',root_acceptance='final/ROOT_ACCEPTANCE.json',root_acceptance_sha256=hashlib.sha256(a.read_bytes()).hexdigest())
(b/'COMPONENT_STATUS.json').write_text(json.dumps(d,indent=2)+'\n');print(d['completed_targets'],len(modules))
text='# M8 current status\n\nUpdated '+d['checked_at_utc']+'. '+('Full M8 root acceptance has passed.' if formal else 'Full M8 Lean acceptance remains pending.')+'\n\nThe SSH-cloned source is frozen: all 35 manifest entries and nine direct dependency hashes were checked. '+str(d['completed_targets'])+' targets in '+str(len(modules))+' complete batches have passed individual checks, assembly compilation, environment checks, and canonical hash verification.\n\n| Completed batch | Targets |\n|---|---:|\n'+''.join('| '+k+' | '+str(v['accepted_targets'])+' |\n' for k,v in modules.items())
text+=('\nThe full source-bound root and all original obligations have passed. See final/ROOT_ACCEPTANCE.json and final/experiment/AcceptedExperiment.lean.\n' if formal else '\nActive and pending dependency work is listed in GRAPH.md and final/SCOPE_MAP.md. Component counts do not imply full M8 acceptance. Explicit admitted and rejected families, complete three-outcome semantics, actual cost composition and source-bound root acceptance must all close.\n')
text+='\nThe M6/M7 canonical proofs are reused through exact source/hash checks. Each proof batch uses gpt-6-astra / medium, two workers, five live attempts, and 600-second compiler calls, within the authorized sixteen-worker ceiling. Late successful drafts are retained; exact local repairs require independent checks and normal replay. The frozen revised M8 is the target; unrestricted all-input M9 is outside this formalization.\n'
(b/'CURRENT.md').write_text(text)

gpath=b/'graph.json'
if gpath.exists():
 g=json.loads(gpath.read_text())
 for x in g['nodes']:
  stage=b/x['id'];x['metadata']['status']='canonical accepted' if x['id'] in modules else 'proof experiment or preflight active' if(stage/'LAUNCH.json').exists()or(stage/'PREFLIGHT.json').exists()else'planned or waiting for canonical parents'
  x['metadata']['module_graph']=str((stage/'graph.json').relative_to(b)) if(stage/'graph.json').exists()else None
  if x['id']=='final':x['dependencies']=['solver','raw_parameters','sequential_resources','sequential_store','whole_resources','coverage','exclusion_conclusions']
 gpath.write_text(json.dumps(g,indent=2)+'\n')
 lines=['# M8 formalization dependencies','','Full M8 acceptance: '+('passed' if formal else 'pending')+'. Component status comes from verified canonical receipts.','','```mermaid','graph TD']
 for x in g['nodes']:
  lines.append('  '+x['id']+'["'+x['id']+(' ✓' if x['id'] in modules else '')+'"]')
  for parent in x['dependencies']:lines.append('  '+parent+' --> '+x['id'])
  for parent in x['metadata'].get('scheduling_dependencies',[]):lines.append('  '+parent+' -. slot gate .-> '+x['id'])
 lines+=['```','','Model workers are capped at 16; individual batches use two. Solid edges are mathematical dependencies; dotted edges only govern worker reuse. The unstarted sharper weighted-sum follow-up is not a completion gate.','']
 (b/'GRAPH.md').write_text('\n'.join(lines))
