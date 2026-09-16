from pathlib import Path
import hashlib,json,shutil,subprocess
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');src=repo/'pipelines/quantum_formalize/examples/m8/diagonal';b=repo/'pipelines/quantum_formalize/examples/m8/diagonal_polynomial';p=Path('/home/jing/m8-lean-diagonal-polynomial-formalization');b.mkdir(exist_ok=True);(b/'lean').mkdir(exist_ok=True);p.mkdir(exist_ok=True)
m=json.loads((src/'experiment/MANIFEST.json').read_text());m=m.get('files',m);env=json.loads((src/'experiment/environment.json').read_text());r=json.loads((src/'experiment/result.json').read_text());assert all(r[k]for k in ['assembly_accepted','environment_unchanged','experiment_passed'])
for n,h in m.items():assert hashlib.sha256((src/'experiment'/n).read_bytes()).hexdigest()==h,n
files=[]
for f in (src/'lean').glob('*.lean'):
 if f.name not in env:continue
 h=hashlib.sha256(f.read_bytes()).hexdigest();assert h==env[f.name],f
 for dest in [p/f.name,b/'lean'/f.name]:shutil.copy2(f,dest)
 files.append({'file':f.name,'sha256':h})
a=src/'experiment/AcceptedExperiment.lean'
for dest in [p/'M8DiagonalAccepted.lean',b/'lean/M8DiagonalAccepted.lean']:shutil.copy2(a,dest)
source='''import M8DiagonalAccepted

namespace M8.DiagonalPolynomial
abbrev BP := M6.Cyclic.BinaryPolynomial
end M8.DiagonalPolynomial
'''
for dest in [p/'M8DiagonalPolynomial.lean',b/'lean/M8DiagonalPolynomial.lean']:dest.write_text(source)
pre='∀ (N : ℕ) [NeZero N], ';P='M6.Physical.';D='M8.DiagonalPolynomial.';C='M6.Coordinates.';Y='M6.Cyclic.'
items=[
('encode_delta',[],pre+C+'encode N ('+P+'delta N 0) = 1'),
('common_divisor_of_inverse',[],pre+'∀ (p F q : '+D+'BP), F.Monic → F ∣ p → F ∣ '+Y+'modulus N → '+Y+'image N p * '+Y+'image N q = 1 → F = 1'),
('coefficients_nonzero',[],pre+'∀ p : '+D+'BP, p ≠ 0 → p.degree < (N : WithBot ℕ) → '+C+'coefficients N p ≠ 0'),
('delta_not_image',['encode_delta','common_divisor_of_inverse'],pre+'∀ (p F : '+D+'BP), p.degree < (N : WithBot ℕ) → F.Monic → F ≠ 1 → F ∣ p → F ∣ '+Y+'modulus N → M8.Diagonal.DeltaNotImage N ('+C+'coefficients N p)'),
('distance_two',['coefficients_nonzero','delta_not_image'],pre+'∀ (p F : '+D+'BP), p ≠ 0 → p.degree < (N : WithBot ℕ) → F.Monic → F ≠ 1 → F ∣ p → F ∣ '+Y+'modulus N → M8.Diagonal.distance N ('+C+'coefficients N p) = some 2')]
guide='''Original revised M8 actual diagonal code polynomial bridge. Discharge DeltaNotImage with concrete nontrivial common polynomial divisor, no free physical correctness or distance assumption. No squarefreeness/odd N. encode_delta: coefficients N 1 = delta N 0 by function ext, Polynomial.coeff_one and ZMod.val_eq_zero; use encode_polynomial N 1, degree 1 polynomial is 0 < N since NeZero N. Or direct blockPolynomial delta sum. common_divisor_of_inverse: rewrite image p*image q as AdjoinRoot.mk modulus (p*q), and 1 as mk modulus 1; AdjoinRoot.mk_eq_mk implies modulus ∣ p*q-1. F divides p*q and p*q-1, hence F divides 1; IsUnit F and monicity force F=1. coefficients_nonzero: apply block_reconstruct p degree-bound to zero coefficients; blockPolynomial zero =0 by simp definitions. delta_not_image: apply encode to hypothetical conv=delta, rewrite encode_conv and encode_polynomial p, encode_delta, unfold encode h to image of blockPolynomial h, invoke common_divisor_of_inverse. distance_two: directly apply accepted M8.Diagonal.distance_two with coefficients_nonzero and delta_not_image. The concrete families still need exact full gcd and recognition/span proofs; this bridge is not a replacement. Tactic lines only, no leading by.\n'''+source

g={'title':'M8 literal polynomial diagonal distance bridge','nodes':[{'id':i,'dependencies':d,'spec':{'name':D+i,'statement':s,'imports':['M8DiagonalPolynomial'],'context':'','queries':['algebra'],'guidance':guide}}for i,d,s in items]};(b/'graph.json').write_text(json.dumps(g,indent=2)+'\n');pr='import M8DiagonalPolynomial\n'+''.join('def target_'+str(i)+' : Prop := ('+s+')\n'for i,(_,_,s)in enumerate(items));(p/'Preflight.lean').write_text(pr);(b/'GraphPreflight.lean').write_text(pr)
for n in ['lean-toolchain','lake-manifest.json']:
 f=Path('/home/jing/m8-lean-diagonal-formalization')/n
 assert hashlib.sha256(f.read_bytes()).hexdigest()==env[n],n
 for dest in [p/n,b/n]:shutil.copy2(f,dest)
lake='''name = "M8DiagonalPolynomial"
version = "0.1.0"
defaultTargets = ["M8DiagonalPolynomial"]
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "de5ce8a9a66a4aa68a9bdbb35b63a06d34d9ca11"
'''
for f in sorted(p.glob('*.lean')):
 if f.stem!='Preflight':lake+='\n[[lean_lib]]\nname = "'+f.stem+'"\n'
(p/'lakefile.toml').write_text(lake);(b/'lakefile.toml').write_text(lake);(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
(b/'IMPORT_PROVENANCE.json').write_text(json.dumps({'parent':'m8/diagonal','canonical_files_verified':len(m),'all_parent_gates':True,'accepted_source_sha256':hashlib.sha256(a.read_bytes()).hexdigest(),'source_files':files},indent=2)+'\n');shutil.copy2(b.parent/'SOURCE.json',b/'SOURCE.json')
(b/'SCOPE.md').write_text('Original revised M8 §§8–9 diagonal distance 2 reusable intermediate. The distance definition is actual M6 CSS distance. The nonzero convolution and delta-not-image conditions are concrete algebraic intermediate obligations and MUST be discharged for each literal admitted/rejected diagonal family downstream. This batch alone makes no coverage, rejection, or full M8 claim. No added squarefreeness, oddness, or lower order bound.\n')
ctl=(b.parent/'coverage_foundation/preflight_launch.py').read_text().replace('m8-lean-coverage-foundation-formalization','m8-lean-diagonal-polynomial-formalization').replace("examples/m8/coverage_foundation'","examples/m8/diagonal_polynomial'").replace('M8CoverageFoundation','M8DiagonalPolynomial').replace('6 exact','5 exact').replace("'coverage_foundation','coverage-foundation','2'","'diagonal_polynomial','diagonal-polynomial','2'")
cp=Path('/home/jing/m8_diagonal_polynomial_preflight_launch.py');cp.write_text(ctl);(b/'preflight_launch.py').write_text(ctl);shutil.copy2('/home/jing/m8_launch_batch.py',b/'launch_batch.py');shutil.copy2('/home/jing/m8_prepare_diagonal_polynomial.py',b/'prepare.py')
with(b/'controller.log').open('a')as log:proc=subprocess.Popen(['/home/jing/quantum_code_discovery_proof/.venv-harness/bin/python',str(cp)],cwd=repo,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
print('preflight PID',proc.pid)
