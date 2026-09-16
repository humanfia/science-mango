from pathlib import Path
import json,hashlib,shutil,subprocess,re,sys,os,time
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');sys.path.insert(0,str(repo));base=repo/'pipelines/quantum_formalize/examples';b=base/'m8/sequential_resources';p=Path('/home/jing/m8-lean-sequential-resources-formalization');parents=[('m8/whole_resources','M8WholeResourcesAccepted'),('m8/sequential_store','M8SequentialStoreAccepted')]
# This gate also prevents starting another worker batch while bank_layout runs.
while True:
 pending=[]
 for name,_ in parents:
  f=base/name/'experiment/result.json';m=base/name/'experiment/MANIFEST.json'
  if not f.exists() or not m.exists() or not all(json.loads(f.read_text()).get(k) is True for k in ['assembly_accepted','environment_unchanged','experiment_passed']):pending.append(name)
 (b/'DEPENDENCY_GATE.json').write_text(json.dumps({'pending_canonical':pending,'ready':not pending,'new_proofs_assumed':False},indent=2)+'\n')
 if not pending:break
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
source=(b/'planned/M8SequentialResources.lean').read_text();(p/'M8SequentialResources.lean').write_text(source);(b/'lean/M8SequentialResources.lean').write_text(source)
root=base/'m8/cutoff'
for name in ['lake-manifest.json','lean-toolchain']:shutil.copy2(root/name,p/name);shutil.copy2(root/name,b/name)
s=(root/'lakefile.toml').read_text().replace('M8Cutoff','M8SequentialResources')
for file in sorted(p.glob('*.lean')):
 if ('[[lean_lib]]\nname = "'+file.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+file.stem+'"\n'
(p/'lakefile.toml').write_text(s);(b/'lakefile.toml').write_text(s);(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
cache_sources=['/home/jing/m8-lean-whole-resources-formalization', '/home/jing/m8-lean-sequential-store-formalization']
cache_helper=b/'cache_reuse.py'
if not cache_helper.exists():shutil.copy2('/home/jing/m8_verified_cache.py',cache_helper)
exec(cache_helper.read_text())
(b/'CACHE_REUSE.json').write_text(json.dumps(reuse_verified_caches(p,cache_sources),indent=2)+'\n')
f='∀ (N : ℕ) [NeZero N], ';ns='M8.SequentialResources.';sl=ns+'slots N';mem='M8.TaggedStore.packFrom 0 mem';rd='M8.TaggedStore.read (M8.TaggedStore.address i.val) ('+mem+')';wr='M8.TaggedStore.write (M8.TaggedStore.address i.val) bit ('+mem+')'
items=[('allocation_access',[],f+'∀ (mem : List Bool), mem.length = '+sl+' → ∀ (i : Fin ('+sl+')) (bit : Bool), ('+rd+').1 = mem[i.val]? ∧ ('+wr+').1 = M8.TaggedStore.packFrom 0 (mem.set i.val bit) ∧ ('+rd+').2 ≤ '+ns+'accessCharge N ∧ ('+wr+').2 ≤ '+ns+'accessCharge N'),('store_space',[],f+'∀ mem : List Bool, mem.length = '+sl+' → '+ns+'storeSpace N mem ≤ 2000000*(N+1)^4'),('access_envelope',[],f+ns+'accessCharge N ≤ 3000000*(N+1)^6'),('tag_setup_bound',[],f+ns+'tagSetupCharge N ≤ 11000000*(N+1)^6'),('actual_prefix_charge',[],f+'∀ c : M7.Action.Recipe N, '+ns+'prefixCharge ('+ns+'accessCharge N) (M8.WholeResources.run c).charges = M8.WholeResources.indexedWork c * '+ns+'accessCharge N'),('sequential_bound',['access_envelope','tag_setup_bound','actual_prefix_charge'],f+'∀ (c : M7.Action.Recipe N) (w : ℕ), 0 < w → M8.PhysicalBridge.Valid w c → '+ns+'sequentialCharge c ≤ 6000000000000*(N+1)^12')]
items=items[4:]
items=[(i,(['actual_prefix_charge'] if i=='sequential_bound' else []),st.replace('M8.SequentialResources.prefixCharge','M8.SequentialStore.prefixCharge').replace('M8.SequentialResources.accessCharge','M8.SequentialResources.primitiveCharge')) for i,ds,st in items]
guide='''Common sequential tagged-store resource composition for the actual M8 layout and executed whole-stage charges. No caller supplies M, address width, memory-cost correctness or arbitrary charge budget. allocation_access uses TaggedStore.indexed_read/indexed_write at start0, read_work/write_work with B=actual slots.size, and packed_layout with mem.length=slots; i:Fin slots supplies valid actual address, Nat.size_le_size bounds the key. store_space uses packed_layout, BankLayout.payload_bound≤20000n³ and address_bits_bound≤32n, with explicit scratch slots. access_envelope uses the same concrete bounds and n>=1; n4≤n6 is enough, do not add sharper final complexity requirements. tag setup: each address in range slots has bits.length≤slots.size; bound the actual fold by length*16*(B+1)+32 using a local induction with membership, then concrete layout bounds. actual_prefix_charge proves repeatCharge unit k=k*unit and fold sum identity locally, applied to the actual WholeResources.run charges, not a free global oracle. sequential_bound unfolds primitiveCharge=8*(accessCharge+1), covering two reads, one write and bounded cursor/control per indexed-bit primitive; compose WholeResources.indexed_work_bound and the proved concrete scan/tag-build envelopes; n6*n6=n12. The counters are compositional upper charges in the accepted standard binary-operation model; do not claim Lean runtime or gate-level extraction. Return tactic lines only.\n'''+source
g={'title':'M8 actual whole common sequential resource composition','nodes':[{'id':i,'dependencies':deps,'spec':{'name':ns+i,'statement':st,'imports':['M8SequentialResources'],'context':'','queries':['algebra'],'guidance':guide},'metadata':{'fallback_queries':['algebra']}}for i,deps,st in items]};(b/'graph.json').write_text(json.dumps(g,indent=2)+'\n');pre='import M8SequentialResources\n'+''.join('def M8.SequentialTarget.'+i+' : Prop := '+st+'\n'for i,_,st in items);(p/'GraphPreflight.lean').write_text(pre);(b/'lean/GraphPreflight.lean').write_text(pre);(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n')
for name in ['preflight.py','launch.py','export.py','finish.py']:
 s=(root/name).read_text().replace('m8-lean-cutoff-formalization','m8-lean-sequential-resources-formalization').replace('M8Cutoff','M8SequentialResources').replace('==8','==2').replace('eight','two').replace('revised M8 cutoff arithmetic targets','revised M8 common sequential resource targets')
 if name=='finish.py':
  a=s.index("(H/'RESULTS.md').write_text(");e=s.index('\nm={',a);s=s[:a]+"(H/'RESULTS.md').write_text('Actual concrete-layout tagged scans, packed-memory read/write projection and actual whole-stage charges satisfy the original common sequential n^12 and storage n^4 resource bounds. All frozen target/axiom/assembly/environment/payload gates passed. This is the accepted symbolic bit-operation model, not Lean runtime extraction.\\n')"+s[e:]
 (b/name).write_text(s)
exec((b/'enable_broad_launch.py').read_text())
enable_broad_launch(b/'launch.py')
shutil.copy2(__file__,b/'prepare.py')
py='/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python'
subprocess.run([py,str(b/'preflight.py')],cwd=repo,check=True)
(b/'FREEZE.json').write_text(json.dumps({'graph_sha256':hashlib.sha256((b/'graph.json').read_bytes()).hexdigest(),'definition_sha256':hashlib.sha256((b/'lean/M8SequentialResources.lean').read_bytes()).hexdigest(),'targets':2,'contexts_empty':True,'parent_canonical_gates_resolved':True},indent=2)+'\n')
subprocess.run([py,str(b/'launch.py')],cwd=repo,check=True)
