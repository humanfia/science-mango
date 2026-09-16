from pathlib import Path
import json,hashlib,shutil,subprocess,re,sys
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');sys.path.insert(0,str(repo))
base=repo/'pipelines/quantum_formalize/examples';b=base/'m8/actual_optimizer_resources';p=Path('/home/jing/m8-lean-actual-optimizer-resources-formalization')
parents=[('m8/cutoff','M8CutoffAccepted'),('m6/transfer/solve_resources','M6SolveResourcesAccepted'),('m6/transfer/solve_storage','M6SolveStorageAccepted'),('m6/transfer/weight_resources','M6WeightResourcesAccepted'),('m6/transfer/partial_resources','M6TransferPartialResourcesAccepted')]
# Canonical proofs, never pending interfaces, authorize promotion.
for name,_ in parents:
 r=json.loads((base/name/'experiment/result.json').read_text());assert all(r.get(k) is True for k in ['assembly_accepted','environment_unchanged','experiment_passed']),name
from pipelines.quantum_formalize.engine import Spec,digest,render as render_candidate
from pipelines.quantum_formalize.dag_runner import load_graph,portable_declaration
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for name,_ in parents:
 A=base/name/'experiment';state=json.loads((A/'nodes/state.json').read_text());_,ns=load_graph(A/'graph.json')
 for n in ns:
  rec=state['nodes'][n.id];assert rec==json.loads((A/'nodes'/n.id/'receipt.json').read_text()) and rec['accepted']
  result=rec['result'];att=result['attempts'][-1];f=A/'node_runs'/n.id/Path(att['proof_path']).parent.name
  spec=Spec.model_validate(json.loads((A/'nodes'/n.id/'resolved-spec.json').read_text()));d=json.loads((f/'draft.json').read_text());assert spec.statement==n.spec['statement']
  assert sha(f/Path(att['proof_path']).name)==att['source_sha256'] and sha(f/Path(att['target_path']).name)==att['target_sha256']
  assert (f/Path(att['proof_path']).name).read_text()==render_candidate(spec,d['proof'],Path(att['target_path']).stem)
  art=result['artifacts'][n.id];assert digest(art['payload'])==art['sha256'] and digest(n.spec)==art['payload']['spec_sha256'];assert portable_declaration(spec,d['proof'])==art['payload']['declaration']
p.mkdir(exist_ok=True);(b/'lean').mkdir(parents=True,exist_ok=True);prov=[]
for name,accepted in parents:
 src=base/name;r=json.loads((src/'experiment/result.json').read_text());assert all(r.get(k)is True for k in ['assembly_accepted','environment_unchanged','experiment_passed']),name
 m=json.loads((src/'experiment/MANIFEST.json').read_text());m=m.get('files',m);env=json.loads((src/'experiment/environment.json').read_text())
 for n,h in m.items():assert hashlib.sha256((src/'experiment'/n).read_bytes()).hexdigest()==h,(name,n)
 for f in (src/'lean').glob('*.lean'):
  if f.name not in env:continue
  assert hashlib.sha256(f.read_bytes()).hexdigest()==env[f.name],(name,f.name)
  if f.name in {'GraphPreflight.lean','Preflight.lean'}:
   frozen_sources=[q for q in (src/'lean').glob('*.lean') if q.name in env]+[src/'experiment/AcceptedExperiment.lean']
   for q in frozen_sources:
    imports=[token for line in re.findall(r'(?m)^\s*import\s+([^\n]+)',q.read_text()) for token in line.split()]
    assert f.stem not in imports,('cannot omit imported preflight module',name,f.name,q.name)
   prov.append({'parent':name,'excluded_unimported_preflight':f.name,'verified_sha256':env[f.name],'reason':'closed target preflight only; not imported by any frozen source or accepted module'})
   continue
  if (p/f.name).exists() and (p/f.name).read_bytes()!=f.read_bytes():
   from pipelines.quantum_formalize.accepted_order import order_only_equivalent
   assert f.name.endswith('Accepted.lean') and order_only_equivalent((p/f.name).read_text(),f.read_text()),('source collision',name,f.name)
   prov.append({'parent':name,'order_only_accepted_module':f.name,'kept_sha256':hashlib.sha256((p/f.name).read_bytes()).hexdigest(),'incoming_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'rule':'identical import multisets and exact declaration-name/body mapping; optional axiom prints reference declared names only; child closure rebuilt'})
   shutil.copy2(p/f.name,b/'lean'/f.name)
   continue
  shutil.copy2(f,p/f.name);shutil.copy2(f,b/'lean'/f.name)
 a=src/'experiment/AcceptedExperiment.lean'
 dest=p/(accepted+'.lean')
 if dest.exists() and dest.read_bytes()!=a.read_bytes():
  from pipelines.quantum_formalize.accepted_order import order_only_equivalent
  assert order_only_equivalent(dest.read_text(),a.read_text()),('accepted collision',accepted)
  prov.append({'parent':name,'order_only_accepted_module':dest.name,'kept_sha256':hashlib.sha256(dest.read_bytes()).hexdigest(),'incoming_sha256':hashlib.sha256(a.read_bytes()).hexdigest(),'rule':'identical import multisets and exact declaration-name/body mapping; optional local axiom prints; explicitly selected parent canonical module replaces inherited order variant before child closure rebuild'})
 shutil.copy2(a,dest)
 shutil.copy2(dest,b/'lean'/dest.name);prov.append({'parent':name,'canonical_files_verified':len(m),'all_sources_match_environment':True,'accepted_source_sha256':hashlib.sha256(a.read_bytes()).hexdigest()})

source='''import M8CutoffAccepted
import M6SolveResourcesAccepted
import M6SolveStorageAccepted
import M6WeightResourcesAccepted
import M6TransferPartialResourcesAccepted

namespace M8.OptimizerResources
noncomputable def weight (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP)
    (pins : M6.Pinned.Pins (2*N)) (character : Bool) :
    ℕ → M6.Transfer.Memory (M6.ActualTransfer.span a b) → M6.Transfer.Bit → Polynomial ℤ :=
  if character then
    M6.ActualTransfer.characterWeight (M6.ActualTransfer.span a b) N a b pins
  else M6.ActualTransfer.boundaryWeight (M6.ActualTransfer.span a b) N a b pins
end M8.OptimizerResources
'''
(p/'M8OptimizerResources.lean').write_text(source);(b/'lean/M8OptimizerResources.lean').write_text(source)
src=base/'m8/cutoff'
for n in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n,p/n);shutil.copy2(src/n,b/n)
s=(src/'lakefile.toml').read_text();s=re.sub(r'^name = ".*?"','name = "M8OptimizerResources"',s,count=1,flags=re.M);s=re.sub(r'^defaultTargets = .*','defaultTargets = ["M8OptimizerResources"]',s,flags=re.M)
for f in sorted(p.glob('*.lean')):
 if ('[[lean_lib]]\nname = "'+f.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+f.stem+'"\n'
(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
f='∀ (N : ℕ) [NeZero N] (a b : M6.ActualTransfer.BP), '
r='M6.ActualTransfer.span a b';h=r+' ≤ M8.Cutoff.limit N → ';v='M6.Pinned.Vector (2*N)';weight='M8.OptimizerResources.weight N a b pins character';ws='∀ (pins : M6.Pinned.Pins (2*N)) (character : Bool), '
cap='2^('+r+') * 8^N';bits='2^(4*(N+1))'
trace='((M6.Transfer.arrayTrace ('+weight+') N).coeff d).natAbs'
partial='(((((Finset.univ : Finset (M6.Transfer.Memory ('+r+'))).toList.take k).map (fun start => M6.Transfer.scalarLayers (N:=N) ('+weight+') start N (start,d))).sum)).natAbs'
scatter='((M6.Transfer.scatterEventList ('+r+') N).take k).foldl (M6.Transfer.scatterUpdate (('+weight+') i) (M6.Transfer.scalarLayers (N:=N) ('+weight+') start i)) (fun _ => 0) addr'
event='M6.Transfer.eventTerm (('+weight+') i) (M6.Transfer.scalarLayers (N:=N) ('+weight+') start i) e'
items=[
('distance_work',[],f+h+'M6.ActualTransfer.actualDistanceWork N a b ≤ 50000*(N+1)^5'),
('witness_work',[],f+'∀ (d : ℕ) (v : '+v+') (k : ℕ), '+h+'M6.ActualTransfer.solve N a b = some (d,v,k) → M6.ActualTransfer.actualWitnessWork N a b k ≤ 200000*(N+1)^6'),
('solve_storage',[],f+h+'M6.ActualTransfer.actualSolveStorage N a b ≤ 16384*(N+1)^3'),
('weight_bounds',[],f+ws+'∀ i m t, M6.Transfer.polynomialMass (('+weight+') i m t) ≤ 4 ∧ (('+weight+') i m t).natDegree ≤ 2'),
('indexed_guarantee',[],f+ws+h+'M6.Transfer.IndexedArrayGuarantee ('+r+') N ('+weight+')'),
('trace_capacity',['weight_bounds'],f+ws+h+'∀ d : ℕ, '+trace+' ≤ '+cap+' ∧ '+trace+' < '+bits),
('trace_prefix_capacity',['weight_bounds'],f+ws+h+'∀ (k : ℕ) (d : Fin (2*N+1)), '+partial+' ≤ '+cap+' ∧ '+partial+' < '+bits),
('scatter_capacity',['weight_bounds'],f+ws+h+'∀ (start : M6.Transfer.Memory ('+r+')) (i : ℕ), i < N → ∀ (k : ℕ) (addr : M6.Transfer.CoefficientAddress ('+r+') N), ('+scatter+').natAbs < '+bits+' ∧ ∀ e : M6.Transfer.ScatterEvent ('+r+') N, ('+event+').natAbs < '+bits)
]
guide='''Bind every resource conclusion to the actual M6 optimizer or its actual boundary/character transfer, not a free evaluator. The Bool selects precisely the two actual physical weights. Cutoff.limit_bounds gives span<N using NeZero.pos N. Use accepted actual_distance_work/actual_witness_work/actual_solve_storage then cutoff indexed_work_envelopes/indexed_storage_envelope. Weight bounds: cases character; unfold weight, boundaryWeight/characterWeight and use Transfer.boundary_edge_bounds/character_edge_bounds. Indexed guarantee directly uses corresponding ActualTransfer.*_indexed_resources. Trace and prefix capacity use Transfer.trace_coefficient_bound and actual_trace_intermediates with weight_bounds projections, then Cutoff.coefficient_capacity. Scatter/event: actual_layer_intermediates gives ≤8^(i+1); i<N gives ≤8^N≤2^span*8^N and hence strict capacity. Preserve arbitrary pins, negative character coefficients, all partial updates and N=1/R=0. Return tactic lines only.\n'''+source
g={'title':'M8 actual optimizer cutoff resources and signed intermediate capacity','nodes':[{'id':i,'dependencies':deps,'spec':{'name':'M8.OptimizerResources.'+i,'statement':st,'imports':['M8OptimizerResources'],'context':'','queries':['polynomial coefficient bounds'],'guidance':guide},'metadata':{'fallback_queries':['algebra']}}for i,deps,st in items]}
(b/'graph.json').write_text(json.dumps(g,indent=2)+'\n');pre='import M8OptimizerResources\n'+''.join('def M8.OptimizerTarget.'+i+' : Prop := '+st+'\n'for i,_,st in items);(p/'GraphPreflight.lean').write_text(pre);(b/'lean/GraphPreflight.lean').write_text(pre)
(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n')
(b/'SCOPE.md').write_text('Eight targets instantiate accepted M6 resource counters and actual physical pinned boundary/character transfer coefficients at the revised fixed M8 cutoff. No actual work counter is redefined. Prefix sums, scatter prefixes and event products retain negative intermediate values and arbitrary pins. These prove indexed optimizer costs and signed magnitudes only; actual discovery/rejection costs and the common sequential-store simulation are separate original-M8 obligations.\n')
for file in ['preflight.py','launch.py','export.py','finish.py']:
 text=(src/file).read_text().replace('m8-lean-cutoff-formalization','m8-lean-actual-optimizer-resources-formalization').replace('M8Cutoff','M8OptimizerResources').replace('revised M8 cutoff arithmetic targets','revised M8 actual optimizer resource targets')
 if file=='finish.py':
  a=text.index("(H/'RESULTS.md').write_text(");end=text.index('\nm={',a);text=text[:a]+"(H/'RESULTS.md').write_text('Actual M6 optimizer counters and physical transfer trace/scatter intermediates satisfy the fixed-cutoff resource and signed-capacity bounds. Every exact frozen target passed normal type/axiom acceptance, full assembly and unchanged-environment checks. All original candidate histories and portable source receipts were rechecked. Discovery and common sequential simulation remain separate obligations.\\n')"+text[end:]
 (b/file).write_text(text)
print(json.dumps({'prepared':8,'project':str(p),'parents_verified':len(parents)}))
