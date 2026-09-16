from pathlib import Path
s=Path('/home/jing/m8_prepare_anchor.py').read_text();head=s.split("\nsource='''",1)[0].replace("examples/m8/anchor","examples/m8/finite_search").replace('m8-lean-anchor','m8-lean-finite-search')
exec(head)
source='''import Mathlib

namespace M8.FiniteSearch
/-- Count actual tested indices; stop at the first value. No materialized index list. -/
def walk {n : ℕ} {α : Type} (f : Fin n → Option α) (start : ℕ) : ℕ → Option (Fin n × α) × ℕ
  | 0 => (none, 0)
  | fuel+1 => if h : start < n then
      match f ⟨start,h⟩ with
      | some a => (some (⟨start,h⟩,a), 1)
      | none => let r := walk f (start+1) fuel; (r.1, r.2+1)
    else (none, 0)
def find {n : ℕ} {α : Type} (f : Fin n → Option α) := walk f 0 n
def First {n : ℕ} {α : Type} (f : Fin n → Option α) (start fuel : ℕ) (i : Fin n) (a : α) : Prop :=
  start ≤ i.val ∧ i.val < start+fuel ∧ f i = some a ∧
    ∀ j : Fin n, start ≤ j.val → j.val < i.val → f j = none
end M8.FiniteSearch
'''
(p/'M8FiniteSearch.lean').write_text(source);(b/'lean/M8FiniteSearch.lean').write_text(source)
src=base/'action'
for n0 in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n0,p/n0);shutil.copy2(src/n0,b/n0)
s=(src/'lakefile.toml').read_text();s=re.sub(r'^name = ".*?"','name = "M8FiniteSearch"',s,count=1,flags=re.M);s=re.sub(r'^defaultTargets = .*','defaultTargets = ["M8FiniteSearch"]',s,flags=re.M)
for f0 in sorted(p.glob('*.lean')):
 if f0.stem!='Preflight' and ('[[lean_lib]]\nname = "'+f0.stem+'"')not in s:s+='\n[[lean_lib]]\nname = "'+f0.stem+'"\n'
(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
f='∀ (n : ℕ) (α : Type) (test : Fin n → Option α) (start fuel : ℕ), '
items=[('calls_bound',[],f+'(M8.FiniteSearch.walk test start fuel).2 ≤ fuel'),('none_iff',[],f+'((M8.FiniteSearch.walk test start fuel).1 = none ↔ ∀ i : Fin n, start ≤ i.val → i.val < start+fuel → test i = none)'),('some_iff',[],f+'∀ (i : Fin n) (a : α), (M8.FiniteSearch.walk test start fuel).1 = some (i,a) ↔ M8.FiniteSearch.First test start fuel i a'),('successful_calls',[],f+'∀ (i : Fin n) (a : α), (M8.FiniteSearch.walk test start fuel).1 = some (i,a) → (M8.FiniteSearch.walk test start fuel).2 = i.val-start+1'),('find_none',['none_iff'],'∀ (n : ℕ) (α : Type) (test : Fin n → Option α), (M8.FiniteSearch.find test).1 = none ↔ ∀ i, test i = none'),('find_some',['some_iff'],'∀ (n : ℕ) (α : Type) (test : Fin n → Option α) (i : Fin n) (a : α), (M8.FiniteSearch.find test).1 = some (i,a) ↔ test i = some a ∧ ∀ j : Fin n, j.val < i.val → test j = none'),('find_bound',['calls_bound'],'∀ (n : ℕ) (α : Type) (test : Fin n → Option α), (M8.FiniteSearch.find test).2 ≤ n'),('exhaustion_calls',[],f+'start+fuel ≤ n → (M8.FiniteSearch.walk test start fuel).1 = none → (M8.FiniteSearch.walk test start fuel).2 = fuel')]
guide='M8 concrete finite first-success counter loop. This is an operational cursor with counted actual callback invocations, not an assumed search oracle. Structural induction on fuel generalizing start; split start<n and actual Option test result. Fin index proof irrelevance via Fin.ext, arithmetic via omega. Later M8 discovery supplies actual eligibility/span tests with separate bit-work bounds. Preserve definitions and exact targets; tactic body only.\n'+source
nodes=[{'id':i,'dependencies':deps,'spec':{'name':'M8.FiniteSearch.'+i,'statement':st,'imports':['M8FiniteSearch'],'context':'','queries':['algebra'],'guidance':guide}}for i,deps,st in items]
(b/'graph.json').write_text(json.dumps({'title':'M8 explicit finite first-success cursor and measured visits','nodes':nodes},indent=2)+'\n');(b/'IMPORT_PROVENANCE.json').write_text(json.dumps(prov,indent=2)+'\n');(p/'Preflight.lean').write_text('import M8FiniteSearch\n'+''.join('def target_'+str(i)+' : Prop := '+n['spec']['statement']+'\n'for i,n in enumerate(nodes)))
ctl=Path('/home/jing/m8_anchor_preflight_launch.py').read_text().replace('m8-lean-anchor','m8-lean-finite-search').replace('examples/m8/anchor','examples/m8/finite_search').replace('M8Anchor','M8FiniteSearch').replace("'anchor','anchor','2'","'finite_search','finite-search','2'")
cp=Path('/home/jing/m8_finite_search_preflight_launch.py');cp.write_text(ctl);shutil.copy2(cp,b/'preflight_launch.py');shutil.copy2('/home/jing/m8_prepare_finite_search.py',b/'prepare.py');shutil.copy2('/home/jing/m8_launch_batch.py',b/'launch_batch.py');log=(b/'controller.log').open('a');proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);print({'targets':len(nodes),'controller_pid':proc.pid})
