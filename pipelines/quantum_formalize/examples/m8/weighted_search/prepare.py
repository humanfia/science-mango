from pathlib import Path
s=Path('/home/jing/m8_prepare_orbit_span.py').read_text();head=s.split("\nsource='''",1)[0].replace("b=base/'orbit_span'","b=base/'weighted_search'").replace('m8-lean-orbit-span','m8-lean-weighted-search').replace("parents=[('anchor','M8AnchorAccepted')]","parents=[('finite_search','M8FiniteSearchAccepted')]")
exec(head)
source='''import M8FiniteSearchAccepted

namespace M8.WeightedSearch
structure Run (n : ℕ) (α : Type) where
  selected : Option (Fin n × α)
  calls : ℕ
  work : ℕ
/-- Calls and callback charges are accumulated only along the executed prefix. -/
def walk {n : ℕ} {α : Type} (f : Fin n → Option α × ℕ) (start : ℕ) : ℕ → Run n α
  | 0 => ⟨none,0,0⟩
  | fuel+1 => if h : start < n then
      let q := f ⟨start,h⟩
      match q.1 with
      | some a => ⟨some (⟨start,h⟩,a),1,q.2⟩
      | none => let r := walk f (start+1) fuel; ⟨r.selected,r.calls+1,q.2+r.work⟩
    else ⟨none,0,0⟩
def find {n : ℕ} {α : Type} (f : Fin n → Option α × ℕ) := walk f 0 n
end M8.WeightedSearch
'''
(p/'M8WeightedSearch.lean').write_text(source);(b/'lean/M8WeightedSearch.lean').write_text(source)
src=base/'finite_search'
for n0 in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n0,p/n0);shutil.copy2(src/n0,b/n0)
s=(src/'lakefile.toml').read_text();s=re.sub(r'^name = ".*?"','name = "M8WeightedSearch"',s,count=1,flags=re.M);s=re.sub(r'^defaultTargets = .*','defaultTargets = ["M8WeightedSearch"]',s,flags=re.M)
for f0 in sorted(p.glob('*.lean')):
 if f0.stem!='Preflight' and ('[[lean_lib]]\nname = "'+f0.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+f0.stem+'"\n'
(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
f='∀ (n : ℕ) (α : Type) (test : Fin n → Option α × ℕ) (start fuel : ℕ), '
r='M8.WeightedSearch.walk test start fuel'
items=[('projection',[],f+'(('+r+').selected, ('+r+').calls) = M8.FiniteSearch.walk (fun i => (test i).1) start fuel'),('callback_bound',[],f+'∀ C : ℕ, (∀ i, (test i).2 ≤ C) → ('+r+').work ≤ ('+r+').calls*C'),('zero_cost',[],f+'(∀ i, (test i).2 = 0) → ('+r+').work = 0'),('find_projection',['projection'],'∀ (n : ℕ) (α : Type) (test : Fin n → Option α × ℕ), ((M8.WeightedSearch.find test).selected,(M8.WeightedSearch.find test).calls) = M8.FiniteSearch.find (fun i => (test i).1)'),('find_callback_bound',['callback_bound','find_projection'],'∀ (n : ℕ) (α : Type) (test : Fin n → Option α × ℕ) (C : ℕ), (∀ i, (test i).2 ≤ C) → (M8.WeightedSearch.find test).work ≤ n*C'),('total_bound',['find_callback_bound','find_projection'],'∀ (n : ℕ) (α : Type) (test : Fin n → Option α × ℕ) (C overhead : ℕ), (∀ i, (test i).2 ≤ C) → (M8.WeightedSearch.find test).calls*overhead + (M8.WeightedSearch.find test).work ≤ n*(overhead+C)')]
guide='Instrumented actual first-success cursor. Separate actual callback invocation count from accumulated callback charges. A later M8 discovery instance must supply real test cost and counter/comparison bit charge; this generic theorem alone is not an M8 resource bound. Structural induction fuel generalizing start, split actual Option result. projection includes both selected result and calls, proving actual evaluation schedule matches canonical FiniteSearch. Nat inequalities via monotonicity/nlinarith; no target edits or assumed total bounds. Tactic lines only.\n'+source
nodes=[{'id':i,'dependencies':deps,'spec':{'name':'M8.WeightedSearch.'+i,'statement':st,'imports':['M8WeightedSearch'],'context':'','queries':['algebra'],'guidance':guide}}for i,deps,st in items]
(b/'graph.json').write_text(json.dumps({'title':'M8 faithful first-success cursor cost instrumentation','nodes':nodes},indent=2)+'\n');(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n');(p/'Preflight.lean').write_text('import M8WeightedSearch\n'+''.join('def target_'+str(i)+' : Prop := '+n['spec']['statement']+'\n'for i,n in enumerate(nodes)))
ctl=Path('/home/jing/m8_anchor_preflight_launch.py').read_text().replace('m8-lean-anchor','m8-lean-weighted-search').replace('examples/m8/anchor','examples/m8/weighted_search').replace('M8Anchor','M8WeightedSearch').replace('8 exact','6 exact').replace("'anchor','anchor','2'","'weighted_search','weighted-search','2'")
cp=Path('/home/jing/m8_weighted_search_preflight_launch.py');cp.write_text(ctl);shutil.copy2(cp,b/'preflight_launch.py');shutil.copy2('/home/jing/m8_prepare_weighted_search.py',b/'prepare.py');shutil.copy2('/home/jing/m8_launch_batch.py',b/'launch_batch.py');log=(b/'controller.log').open('a');proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);print({'targets':len(nodes),'controller_pid':proc.pid})
