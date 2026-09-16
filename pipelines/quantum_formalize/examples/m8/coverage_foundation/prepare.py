from pathlib import Path
import json,hashlib,shutil,subprocess
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');src=repo/'pipelines/quantum_formalize/examples/m7/connectivity';b=repo/'pipelines/quantum_formalize/examples/m8/coverage_foundation';p=Path('/home/jing/m8-lean-coverage-foundation-formalization');b.mkdir(exist_ok=True);(b/'lean').mkdir(exist_ok=True);p.mkdir(exist_ok=True)
r=json.loads((src/'experiment/result.json').read_text());assert all(r[k] for k in ['assembly_accepted','environment_unchanged','experiment_passed']);m=json.loads((src/'experiment/MANIFEST.json').read_text());m=m.get('files',m);env=json.loads((src/'experiment/environment.json').read_text());files=[]
for f,h in m.items():assert hashlib.sha256((src/'experiment'/f).read_bytes()).hexdigest()==h,f
for f in (src/'lean').glob('*.lean'):
 if f.name not in env:continue
 h=hashlib.sha256(f.read_bytes()).hexdigest();assert h==env[f.name],f
 shutil.copy2(f,p/f.name);shutil.copy2(f,b/'lean'/f.name);files.append({'file':f.name,'sha256':h})
a=src/'experiment/AcceptedExperiment.lean';shutil.copy2(a,p/'M7ConnectivityAccepted.lean');shutil.copy2(a,b/'lean/M7ConnectivityAccepted.lean')
source='''import M7ConnectivityAccepted
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

namespace M8.CoverageFoundation
noncomputable def direction {N : ℕ} (A : Finset (ZMod N)) : AddSubgroup (ZMod N) :=
  AddSubgroup.closure (M7.Connectivity.differences A)
def FullDirection {N : ℕ} (A : Finset (ZMod N)) : Prop := direction A = ⊤
def InCoset {N : ℕ} (A : Finset (ZMod N)) (H : AddSubgroup (ZMod N)) : Prop :=
  ∃ a : ZMod N, ∀ x ∈ A, x - a ∈ H
/-- Exactly the proper coprime separated directions of the revised M8 source. -/
def Separated {N : ℕ} (c : M7.Action.Recipe N) : Prop :=
  ∃ m q : ℕ, 2 ≤ m ∧ 2 ≤ q ∧ N = m*q ∧ Nat.Coprime m q ∧
    InCoset c.1 (AddSubgroup.zmultiples (q : ZMod N)) ∧
    InCoset c.2 (AddSubgroup.zmultiples (m : ZMod N))
end M8.CoverageFoundation
'''
(p/'M8CoverageFoundation.lean').write_text(source);(b/'lean/M8CoverageFoundation.lean').write_text(source)
ns='M8.CoverageFoundation.';pre='∀ (N : ℕ) [NeZero N], '
items=[
('coset_direction',[],pre+'∀ (A : Finset (ZMod N)) (H : AddSubgroup (ZMod N)), '+ns+'InCoset A H → '+ns+'direction A ≤ H'),
('consecutive_full',[],pre+'∀ (A : Finset (ZMod N)) (a : ZMod N), a ∈ A → a+1 ∈ A → '+ns+'FullDirection A'),
('affine_full',[],pre+'∀ (A : Finset (ZMod N)) (u : (ZMod N)ˣ) (s : ZMod N), '+ns+'FullDirection (A.image (M7.Action.affine u s)) ↔ '+ns+'FullDirection A'),
('proper_multiples',[],pre+'∀ q : ℕ, 2 ≤ q → q ∣ N → AddSubgroup.zmultiples (q : ZMod N) ≠ ⊤'),
('no_separated',['coset_direction','proper_multiples'],pre+'∀ c : M7.Action.Recipe N, ('+ns+'FullDirection c.1 ∨ '+ns+'FullDirection c.2) → ¬ '+ns+'Separated c'),
('orbit_no_separated',['affine_full','no_separated'],pre+'∀ (c : M7.Action.Recipe N) (g : M7.Action.Record N), ('+ns+'FullDirection c.1 ∨ '+ns+'FullDirection c.2) → ¬ '+ns+'Separated (M7.Action.act g c)')]
guide='''Revised original M8 §8 precise separated-direction obstruction, not Clifford inequivalence or arbitrary tensor inequivalence. direction uses the unique accepted M7 differences definition. coset_direction: closure_le, express x-y=(x-a)-(y-a) in H. consecutive_full: the difference (a+1)-a=1 belongs to closure, then accepted M7.Connectivity.one_mem_top. affine_full can use accepted M7.Connectivity.connected_action on the diagonal recipe (A,A) and Record ⟨u,false,s,s⟩: connected (A,A) simplifies to direction A=top since union_self; this avoids introducing an abstract/free automorphism. Or use difference_affine and explicit unit AddEquiv. proper_multiples: AddSubgroup.zmultiples_eq_closure and M7.Connectivity.finite_generation_gcd applied to singleton Finset {q}; Nat.gcd_eq_right from q|N gives q=1 contradiction. q=N is permitted and proper, no q<N assumption. no_separated: actual N=m*q yields q|N and m|N; full direction of either block forces corresponding subgroup top via coset_direction, contradict proper_multiples. orbit_no_separated: actual Action.act, split exchange, affine_full preserves the OR of full directions even if only one original block is full (the mixed two-term family). No squarefree/odd-order assumption, no stronger equivalence claim. Return tactic lines only, no leading by.\n'''+source
g={'title':'Revised M8 actual separated-direction coverage foundation','nodes':[{'id':i,'dependencies':d,'spec':{'name':ns+i,'statement':s,'imports':['M8CoverageFoundation'],'context':'','queries':['algebra'],'guidance':guide}}for i,d,s in items]};(b/'graph.json').write_text(json.dumps(g,indent=2)+'\n');pr='import M8CoverageFoundation\n'+''.join('def target_'+str(i)+' : Prop := ('+s+')\n'for i,(_,_,s)in enumerate(items));(p/'Preflight.lean').write_text(pr);(b/'GraphPreflight.lean').write_text(pr)
for n in ['lean-toolchain','lake-manifest.json']:
 f=src/n
 if not f.exists():f=Path('/home/jing/m7-lean-connectivity-formalization')/n
 assert hashlib.sha256(f.read_bytes()).hexdigest()==env[n],n
 shutil.copy2(f,p/n);shutil.copy2(f,b/n)
lake='''name = "M8CoverageFoundation"
version = "0.1.0"
defaultTargets = ["M8CoverageFoundation"]
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"
'''
for f in sorted(p.glob('*.lean')):
 if f.stem!='Preflight':lake+='\n[[lean_lib]]\nname = "'+f.stem+'"\n'
(p/'lakefile.toml').write_text(lake);(b/'lakefile.toml').write_text(lake);(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
(b/'IMPORT_PROVENANCE.json').write_text(json.dumps({'parent':'m7/connectivity','canonical_files_verified':len(m),'all_parent_gates':True,'accepted_source_sha256':hashlib.sha256(a.read_bytes()).hexdigest(),'source_files':files},indent=2)+'\n')
shutil.copy2(b.parent/'SOURCE.json',b/'SOURCE.json');(b/'SCOPE.md').write_text('Revised M8 §8: exact recipe-orbit separated-direction obstruction from a full within-block difference subgroup. One full block suffices and exchange is included. No Clifford or arbitrary tensor inequivalence claim. Actual diagonal CSS distance and explicit family arithmetic are downstream obligations, not assumed here.\n')
ctl=(b.parent/'anchor/preflight_launch.py').read_text().replace('m8-lean-anchor-formalization','m8-lean-coverage-foundation-formalization').replace("examples/m8/anchor'","examples/m8/coverage_foundation'").replace('M8Anchor','M8CoverageFoundation').replace('8 exact','6 exact').replace("'anchor','anchor','2'","'coverage_foundation','coverage-foundation','2'")
cp=Path('/home/jing/m8_coverage_foundation_preflight_launch.py');cp.write_text(ctl);(b/'preflight_launch.py').write_text(ctl);shutil.copy2('/home/jing/m8_launch_batch.py',b/'launch_batch.py');shutil.copy2('/home/jing/m8_prepare_coverage_foundation.py',b/'prepare.py')
with(b/'controller.log').open('a')as log:proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
print('preflight PID',proc.pid)
