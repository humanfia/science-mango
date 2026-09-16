from pathlib import Path
import hashlib,json,shutil,subprocess
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');src=repo/'pipelines/quantum_formalize/examples/m6/actual_css';b=repo/'pipelines/quantum_formalize/examples/m8/diagonal';p=Path('/home/jing/m8-lean-diagonal-formalization');b.mkdir(exist_ok=True);(b/'lean').mkdir(exist_ok=True);p.mkdir(exist_ok=True)
m=json.loads((src/'experiment/MANIFEST.json').read_text());m=m.get('files',m);env=json.loads((src/'experiment/environment.json').read_text());r=json.loads((src/'experiment/result.json').read_text());assert all(r[k]for k in ['assembly_accepted','environment_unchanged','experiment_passed'])
for n,h in m.items():assert hashlib.sha256((src/'experiment'/n).read_bytes()).hexdigest()==h,n
files=[]
for f in (src/'lean').glob('*.lean'):
 if f.name not in env:continue
 h=hashlib.sha256(f.read_bytes()).hexdigest();assert h==env[f.name],f
 for dest in [p/f.name,b/'lean'/f.name]:shutil.copy2(f,dest)
 files.append({'file':f.name,'sha256':h})
a=src/'experiment/AcceptedExperiment.lean'
for dest in [p/'M6ActualCSSAccepted.lean',b/'lean/M6ActualCSSAccepted.lean']:shutil.copy2(a,dest)
source='''import M6ActualCSSAccepted

namespace M8.Diagonal
/-- Actual CSS distance of the diagonal convolution code. -/
noncomputable def distance (N : ℕ) [NeZero N] (p : M6.Physical.Block N) : Option ℕ :=
  M6.CSS.quantumDistance (M6.Spaces.boundaryWords N p p)
    (M6.Spaces.cycleWords N p p)
    (M6.Character.subspaceWords (M6.Spaces.D N p p))
    (M6.Character.dualWords (M6.Spaces.B N p p))
/-- Algebraic intermediate obligation, discharged for each explicit source family. -/
def DeltaNotImage (N : ℕ) [NeZero N] (p : M6.Physical.Block N) : Prop :=
  ¬ ∃ h : M6.Physical.Block N, M6.Physical.conv N p h = M6.Physical.delta N 0
end M8.Diagonal
'''
for dest in [p/'M8Diagonal.lean',b/'lean/M8Diagonal.lean']:dest.write_text(source)
pre='∀ (N : ℕ) [NeZero N], ';P='M6.Physical.';D='M8.Diagonal.'
items=[
('weight_zero',[],pre+'∀ a : '+P+'Block N, '+P+'weight N a = 0 ↔ a = 0'),
('weight_one',[],pre+'∀ a : '+P+'Block N, '+P+'weight N a = 1 ↔ ∃ j : ZMod N, a = '+P+'delta N j'),
('conv_delta',[],pre+'∀ (p : '+P+'Block N) (j i : ZMod N), '+P+'conv N p ('+P+'delta N j) i = p (i-j)'),
('delta_weight',[],pre+'∀ j : ZMod N, '+P+'weight N ('+P+'delta N j) = 1'),
('small_cycle_zero',['weight_zero','weight_one','conv_delta'],pre+'∀ (p : '+P+'Block N) (z : '+P+'Word N), p ≠ 0 → '+P+'syndrome N p p z = 0 → '+P+'wordWeight N z < 2 → z = 0'),
('diagonal_witness',['delta_weight'],pre+'∀ p : '+P+'Block N, '+D+'DeltaNotImage N p → (M6.Flatten.flatten N ('+P+'delta N 0, '+P+'delta N 0) ∈ M6.Spaces.logicalWords N p p ∧ M6.Pinned.weight (M6.Flatten.flatten N ('+P+'delta N 0, '+P+'delta N 0)) = 2)'),
('logical_lower_bound',['small_cycle_zero'],pre+'∀ (p : '+P+'Block N) (v : M6.Pinned.Vector (2*N)), p ≠ 0 → v ∈ M6.Spaces.logicalWords N p p → 2 ≤ M6.Pinned.weight v'),
('distance_two',['diagonal_witness','logical_lower_bound'],pre+'∀ p : '+P+'Block N, p ≠ 0 → '+D+'DeltaNotImage N p → '+D+'distance N p = some 2')]
guide='''Original revised M8 §8/9 reusable actual diagonal CSS distance foundation. Actual M6 finite binary vectors, convolution, syndrome, boundary and union-support CSS quantumDistance; not a surrogate distance. DeltaNotImage is an intermediate algebraic condition that downstream explicit families MUST discharge from literal nontrivial gcd; no family is claimed accepted from free hypotheses. No squarefree or odd-N assumption.\nweight_zero uses Finset.card_eq_zero on univ.filter and function ext. weight_one uses Finset.card_eq_one to obtain exactly one nonzero coordinate and the fact a nonzero ZMod 2 element is 1 (fin_cases or ZMod.val bounds); converse direct singleton filter. conv_delta: sum p(r)*ite(i-r=j); the unique r=i-j; use Finset.sum_eq_single and additive arithmetic, or change variables via conv_comm to sum over delta in first factor. delta_weight direct singleton filter. small_cycle_zero: wordWeight=weight first+weight second <2; each block has weight0/1, split natural cases; weight0 gives zero, weight1 gives delta; convolution with delta is a translate of p, hence cannot vanish since p≠0. syndrome is sum of the two conv blocks. diagonal_witness: logical_words_iff; unflatten_flatten; identical conv cancels over ZMod2. If a boundary equals paired delta, project first block after unflatten to contradict DeltaNotImage. flatten_weight and delta_weight give2. logical_lower_bound: logical_words_iff gives actual syndrome zero; flatten_weight/unflatten roundtrip relate weights; small_cycle_zero contradicts zero_not_logical. distance_two: unfold distance; rw M6.ActualCSS.common_quantum_distance; use (M6.Pinned.distance_spec (2*N) (M6.Spaces.logicalWords N p p)).2 2, provide actual witness and universal lowerbound. Check local interfaces/theorem exact signatures before applying. Tactic lines only, no leading by.\n'''+source
g={'title':'M8 actual diagonal CSS distance two foundation','nodes':[{'id':i,'dependencies':d,'spec':{'name':D+i,'statement':s,'imports':['M8Diagonal'],'context':'','queries':['algebra'],'guidance':guide}}for i,d,s in items]};(b/'graph.json').write_text(json.dumps(g,indent=2)+'\n');pr='import M8Diagonal\n'+''.join('def target_'+str(i)+' : Prop := ('+s+')\n'for i,(_,_,s)in enumerate(items));(p/'Preflight.lean').write_text(pr);(b/'GraphPreflight.lean').write_text(pr)
for n in ['lean-toolchain','lake-manifest.json']:
 f=Path('/home/jing/m6-lean-actual-css-formalization')/n
 assert hashlib.sha256(f.read_bytes()).hexdigest()==env[n],n
 for dest in [p/n,b/n]:shutil.copy2(f,dest)
lake='''name = "M8Diagonal"
version = "0.1.0"
defaultTargets = ["M8Diagonal"]
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"
'''
for f in sorted(p.glob('*.lean')):
 if f.stem!='Preflight':lake+='\n[[lean_lib]]\nname = "'+f.stem+'"\n'
(p/'lakefile.toml').write_text(lake);(b/'lakefile.toml').write_text(lake);(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
(b/'IMPORT_PROVENANCE.json').write_text(json.dumps({'parent':'m6/actual_css','canonical_files_verified':len(m),'all_parent_gates':True,'accepted_source_sha256':hashlib.sha256(a.read_bytes()).hexdigest(),'source_files':files},indent=2)+'\n');shutil.copy2(b.parent/'SOURCE.json',b/'SOURCE.json')
(b/'SCOPE.md').write_text('Original revised M8 §§8–9 diagonal distance 2 reusable intermediate. The distance definition is actual M6 CSS distance. The nonzero convolution and delta-not-image conditions are concrete algebraic intermediate obligations and MUST be discharged for each literal admitted/rejected diagonal family downstream. This batch alone makes no coverage, rejection, or full M8 claim. No added squarefreeness, oddness, or lower order bound.\n')
ctl=(b.parent/'coverage_foundation/preflight_launch.py').read_text().replace('m8-lean-coverage-foundation-formalization','m8-lean-diagonal-formalization').replace("examples/m8/coverage_foundation'","examples/m8/diagonal'").replace('M8CoverageFoundation','M8Diagonal').replace('6 exact','8 exact').replace("'coverage_foundation','coverage-foundation','2'","'diagonal','diagonal','2'")
cp=Path('/home/jing/m8_diagonal_preflight_launch.py');cp.write_text(ctl);(b/'preflight_launch.py').write_text(ctl);shutil.copy2('/home/jing/m8_launch_batch.py',b/'launch_batch.py');shutil.copy2('/home/jing/m8_prepare_diagonal.py',b/'prepare.py')
with(b/'controller.log').open('a')as log:proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
print('preflight PID',proc.pid)
