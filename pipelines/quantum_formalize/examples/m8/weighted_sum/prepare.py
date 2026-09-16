from pathlib import Path
s=Path('/home/jing/m8_prepare_orbit_span.py').read_text();head=s.split("\nsource='''",1)[0].replace("b=base/'orbit_span'","b=base/'weighted_sum'").replace('m8-lean-orbit-span','m8-lean-weighted-sum').replace("parents=[('anchor','M8AnchorAccepted')]","parents=[('weighted_search','M8WeightedSearchAccepted')]")
exec(head)
source='''import M8WeightedSearchAccepted
'''

(p/'M8WeightedSum.lean').write_text(source);(b/'lean/M8WeightedSum.lean').write_text(source)
src=base/'weighted_search'
for n0 in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n0,p/n0);shutil.copy2(src/n0,b/n0)
s=(src/'lakefile.toml').read_text();s=re.sub(r'^name = ".*?"','name = "M8WeightedSum"',s,count=1,flags=re.M);s=re.sub(r'^defaultTargets = .*','defaultTargets = ["M8WeightedSum"]',s,flags=re.M)
for f0 in sorted(p.glob('*.lean')):
 if f0.stem!='Preflight' and ('[[lean_lib]]\nname = "'+f0.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+f0.stem+'"\n'
(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
f='∀ (n : ℕ) (α : Type) (test : Fin n → Option α × ℕ), '
items=[('tail_split',[],f+'∀ (start : ℕ) (h : start < n), (Finset.univ.sum (fun i : Fin n => if start ≤ i.val then (test i).2 else 0)) = (test ⟨start,h⟩).2 + Finset.univ.sum (fun i : Fin n => if start+1 ≤ i.val then (test i).2 else 0)'),('walk_sum_bound',['tail_split'],f+'∀ start fuel : ℕ, (M8.WeightedSearch.walk test start fuel).work ≤ Finset.univ.sum (fun i : Fin n => if start ≤ i.val then (test i).2 else 0)'),('find_sum_bound',['walk_sum_bound'],f+'(M8.WeightedSearch.find test).work ≤ Finset.univ.sum (fun i : Fin n => (test i).2)')]

guide='Additional actual finite-search charge bound by the full nonnegative callback sum, used to count eligible span trials rather than using uniform per-tuple bound. tail_split separates the unique Fin index with val=start (Fin.ext) from val>=start+1; prove sum of indicator singleton with Finset.sum_ite_eq then pointwise sum equality. walk_sum_bound induction fuel generalizing start: some result charges only current callback; none charges current plus suffix, tail_split and induction; start>=n and zero fuel give0. find sum uses start0. Exact original WeightedSearch definitions unchanged and all typecontexts closed. This is an intermediate lemma, no full M8 completion claim.\n'

nodes=[{'id':i,'dependencies':deps,'spec':{'name':'M8.WeightedSum.'+i,'statement':st,'imports':['M8WeightedSum'],'context':'','queries':['algebra'],'guidance':guide}}for i,deps,st in items]
(b/'graph.json').write_text(json.dumps({'title':'M8 exact nonnegative full callback sum envelope','nodes':nodes},indent=2)+'\n');(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n');(p/'Preflight.lean').write_text('import M8WeightedSum\n'+''.join('def target_'+str(i)+' : Prop := '+n['spec']['statement']+'\n'for i,n in enumerate(nodes)))
import runpy
cache_helper=runpy.run_path('/home/jing/m8_verified_cache.py')
(b/'BUILD_CACHE.json').write_text(json.dumps(cache_helper['reuse_verified_caches'](p,['/home/jing/m8-lean-weighted-search-formalization']),indent=2)+'\n')
shutil.copy2('/home/jing/m8_verified_cache.py',b/'cache_reuse.py')
ctl=Path('/home/jing/m8_anchor_preflight_launch.py').read_text().replace('m8-lean-anchor','m8-lean-weighted-sum').replace('examples/m8/anchor','examples/m8/weighted_sum').replace('M8Anchor','M8WeightedSum').replace('8 exact','3 exact').replace("'anchor','anchor','2'","'weighted_sum','weighted-sum','2'")
cp=Path('/home/jing/m8_weighted_sum_preflight_launch.py');cp.write_text(ctl);shutil.copy2(cp,b/'preflight_launch.py');shutil.copy2('/home/jing/m8_prepare_weighted_sum.py',b/'prepare.py');shutil.copy2('/home/jing/m8_launch_batch.py',b/'launch_batch.py');log=(b/'controller.log').open('a');proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);print({'targets':len(nodes),'controller_pid':proc.pid})
