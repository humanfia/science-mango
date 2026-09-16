from pathlib import Path
import json,hashlib,shutil,subprocess,re,sys,os,time
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');sys.path.insert(0,str(repo));base=repo/'pipelines/quantum_formalize/examples';b=base/'m8/whole_resources';p=Path('/home/jing/m8-lean-whole-resources-formalization');parents=[('m8/solver','M8SolverAccepted'),('m8/discovery_resources','M8DiscoveryResourcesAccepted'),('m8/actual_optimizer_resources','M8OptimizerResourcesAccepted'),('m8/bank_layout','M8BankLayoutAccepted')]
# This gate also prevents starting another worker batch while bank_layout runs.
while True:
 pending=[]
 for name,_ in parents:
  f=base/name/'experiment/result.json';m=base/name/'experiment/MANIFEST.json'
  if not f.exists() or not m.exists() or not all(json.loads(f.read_text()).get(k) is True for k in ['assembly_accepted','environment_unchanged','experiment_passed']):pending.append(name)
 scheduling=[]
 for name in ['m8/sequential_store']:
  f=base/name/'experiment/result.json';m=base/name/'experiment/MANIFEST.json'
  if not f.exists() or not m.exists() or not all(json.loads(f.read_text()).get(k) is True for k in ['assembly_accepted','environment_unchanged','experiment_passed']):scheduling.append(name)
 (b/'DEPENDENCY_GATE.json').write_text(json.dumps({'pending_math':pending,'pending_scheduling':scheduling,'ready':not pending and not scheduling,'new_proofs_assumed':False,'scheduling_reason':'Reuse this agent two-worker slot; sequential_store is not a mathematical premise/import of whole'},indent=2)+'\n')
 if not pending and not scheduling:break
 time.sleep(20)
old=Path('/home/jing/m8_prepare_optimizer_resources.py').read_text();exec(old[old.index('# Canonical proofs'):old.index('common=Path(')])
common=Path('/home/jing/m7_prepare_prefix_orbit.py').read_text()
promotion=common[common.index('p.mkdir(exist_ok=True)'):common.index("source='''")]
helper=b/'packaged_definition_collision.py'
shutil.copy2('/home/jing/m8_packaged_definition_collision.py',helper)
exec(helper.read_text())
needle="   from pipelines.quantum_formalize.accepted_order import order_only_equivalent"
insert='   reconciliation=reconcile_packaged_definition(p/f.name,f,repo)\n   if reconciliation is not None:\n    chosen,audit=reconciliation\n    (p/f.name).write_bytes(chosen);(b/"lean"/f.name).write_bytes(chosen)\n    prov.append({"parent":name,"definition_import_reconciliation":audit})\n    continue\n'
promotion=promotion.replace(needle,insert+needle,1)
exec(promotion)
source=(b/'planned/M8WholeResources.lean').read_text();(p/'M8WholeResources.lean').write_text(source);(b/'lean/M8WholeResources.lean').write_text(source)
root=base/'m8/cutoff'
for name in ['lake-manifest.json','lean-toolchain']:shutil.copy2(root/name,p/name);shutil.copy2(root/name,b/name)
s=(root/'lakefile.toml').read_text().replace('M8Cutoff','M8WholeResources')
for file in sorted(p.glob('*.lean')):
 if ('[[lean_lib]]\nname = "'+file.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+file.stem+'"\n'
(p/'lakefile.toml').write_text(s);(b/'lakefile.toml').write_text(s);(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
cache_sources=['/home/jing/m8-lean-solver-formalization', '/home/jing/m8-lean-bank-layout-formalization']
cache_helper=b/'cache_reuse.py'
if not cache_helper.exists():shutil.copy2('/home/jing/m8_verified_cache.py',cache_helper)
exec(cache_helper.read_text())
(b/'CACHE_REUSE.json').write_text(json.dumps(reuse_verified_caches(p,cache_sources),indent=2)+'\n')
f='∀ (N : ℕ) [NeZero N] (c : M7.Action.Recipe N), ';ns='M8.WholeResources.';valid='∀ w : ℕ, 0 < w → M8.PhysicalBridge.Valid w c → ';rr=ns+'run c'
items=[('elementary_bounds',[],'∀ (N : ℕ) [NeZero N], '+ns+'setupWork N ≤ 21000*(N+1)^3 ∧ '+ns+'transformWork N ≤ 96*(N+1)^3 ∧ '+ns+'undoWork N ≤ 160*(N+1)^3'),('original_preprocess_bound',[],f+ns+'originalWork c ≤ 180*(N+1)^3'),('selected_span',[],f+valid+'∀ choice : M8.Discovery.Choice N, M8.Discovery.discover c = some choice → M6.ActualTransfer.span (M7.Supports.polynomial (M8.Discovery.transformed c choice).1) (M7.Supports.polynomial (M8.Discovery.transformed c choice).2) ≤ M8.Cutoff.limit N'),('projection',[],f+'('+rr+').outcome = M8.Solver.run c'),('charge_length',[],f+'('+rr+').charges.length ≤ 6'),('single_calls',[],f+'('+rr+').discoveryCalls ≤ 1 ∧ ('+rr+').optimizerCalls ≤ ('+rr+').discoveryCalls'),('noLogical_early',[],f+'M8.Solver.originalF c = 1 → ('+rr+').charges = ['+ns+'setupWork N,'+ns+'originalWork c] ∧ ('+rr+').discoveryCalls = 0 ∧ ('+rr+').optimizerCalls = 0'),('indexed_work_bound',['elementary_bounds','original_preprocess_bound','selected_span'],f+valid+ns+'indexedWork c ≤ 225000*(N+1)^6')]
guide='''Actual whole M8 run, not free cost oracle. Projection follows DiscoveryResources.projection; unfold both runs and split the same original gcd/selected/optimizer Option. Work accounting has at most six executed stage totals, never query/access history. The M6 witness counter already includes initial query and transformed preprocessing; do not add distance cost again. Elementary bounds: foldl of constant increments over range equals length*charge by a local general induction; combine actual BankLayout.payload_bound. Original preprocess uses accepted Supports.degree_lt and Euclid.preprocess_correct_cost, modulus natDegree bound. selected_span uses Solver.literal_span_le on the actual transformed recipe; Action.support_cards plus Connectivity.connected_action preserve Valid, then Discovery.cutoff. Indexed bound: split actual run; derive actual discover equation from DiscoveryResources.projection; use selected_span, OptimizerResources.distance_work/witness_work (actual solve=some) and DiscoveryResources.work_bound. Normalize List.sum append; N+1≥1 lets lower powers bound by n6. Return tactic lines only; no altered definitions or stronger validity assumptions.\n'''+source
g={'title':'M8 actual whole indexed algorithm resource composition','nodes':[{'id':i,'dependencies':deps,'spec':{'name':ns+i,'statement':st,'imports':['M8WholeResources'],'context':'','queries':['algebra'],'guidance':guide},'metadata':{'fallback_queries':['algebra']}}for i,deps,st in items]};(b/'graph.json').write_text(json.dumps(g,indent=2)+'\n');pre='import M8WholeResources\n'+''.join('def M8.WholeTarget.'+i+' : Prop := '+st+'\n'for i,_,st in items);(p/'GraphPreflight.lean').write_text(pre);(b/'lean/GraphPreflight.lean').write_text(pre);(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n')
for name in ['preflight.py','launch.py','export.py','finish.py']:
 s=(root/name).read_text().replace('m8-lean-cutoff-formalization','m8-lean-whole-resources-formalization').replace('M8Cutoff','M8WholeResources').replace('revised M8 cutoff arithmetic targets','revised M8 whole indexed resource targets')
 if name=='finish.py':
  a=s.index("(H/'RESULTS.md').write_text(");e=s.index('\nm={',a);s=s[:a]+"(H/'RESULTS.md').write_text('Actual whole three-branch indexed accounting projects to Solver.run and satisfies the original polynomial indexed bound, with once-only discovery/optimizer calls and constant-length executed stage totals. All exact target/axiom/assembly/environment/payload gates passed. The common sequential tagged-store composition remains downstream.\\n')"+s[e:]
 (b/name).write_text(s)
exec((b/'enable_broad_launch.py').read_text())
enable_broad_launch(b/'launch.py')
shutil.copy2(__file__,b/'prepare.py')
py='/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python'
subprocess.run([py,str(b/'preflight.py')],cwd=repo,check=True)
(b/'FREEZE.json').write_text(json.dumps({'graph_sha256':hashlib.sha256((b/'graph.json').read_bytes()).hexdigest(),'definition_sha256':hashlib.sha256((b/'lean/M8WholeResources.lean').read_bytes()).hexdigest(),'targets':8,'contexts_empty':True,'parent_canonical_gates_resolved':True},indent=2)+'\n')
subprocess.run([py,str(b/'launch.py')],cwd=repo,check=True)
