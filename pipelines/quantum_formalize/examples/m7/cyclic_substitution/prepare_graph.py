from pathlib import Path
import json,hashlib,shutil
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');b=repo/'pipelines/quantum_formalize/examples/m7/cyclic_substitution';p=Path('/home/jing/m7-lean-cyclic-substitution-formalization');p.mkdir(exist_ok=True);(b/'lean').mkdir(parents=True,exist_ok=True)
d=repo/'pipelines/quantum_formalize/examples/m7/domain';f=d/'lean/M6Cyclic.lean';h=hashlib.sha256(f.read_bytes()).hexdigest();assert h==json.loads((d/'MANIFEST.json').read_text())['lean/M6Cyclic.lean'];shutil.copy2(f,p/f.name);shutil.copy2(f,b/'lean'/f.name)
source='''import M6Cyclic

namespace M7.CyclicSubstitution
noncomputable def rho (N : ℕ) : M6.Cyclic.CycleRing N :=
  AdjoinRoot.root (M6.Cyclic.modulus N)
noncomputable def point {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) : M6.Cyclic.CycleRing N :=
  rho N ^ (u : ZMod N).val
def RootCondition {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) : Prop :=
  (M6.Cyclic.modulus N).eval₂ (AdjoinRoot.of (M6.Cyclic.modulus N)) (point u) = 0
noncomputable def hom {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) (h : RootCondition u) :
    M6.Cyclic.CycleRing N →+* M6.Cyclic.CycleRing N :=
  AdjoinRoot.lift (AdjoinRoot.of (M6.Cyclic.modulus N)) (point u) h
end M7.CyclicSubstitution
'''
(p/'M7CyclicSubstitution.lean').write_text(source);(b/'lean/M7CyclicSubstitution.lean').write_text(source)
base=Path('/home/jing/m7-lean-canonical-block-formalization')
for n in ['lake-manifest.json','lean-toolchain']:shutil.copy2(base/n,p/n);shutil.copy2(base/n,b/n)
s=(base/'lakefile.toml').read_text().replace('M7CanonicalBlock','M7CyclicSubstitution')+'\n[[lean_lib]]\nname = "M6Cyclic"\n';(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
f='∀ (N : ℕ) [NeZero N], ';rho='M7.CyclicSubstitution.rho N';point='M7.CyclicSubstitution.point'
items=[
('root_power',[],f+rho+' ^ N = 1'),
('power_mod',['root_power'],f+'∀ k : ℕ, '+rho+' ^ k = '+rho+' ^ (k % N)'),
('point_root',['root_power'],f+'∀ u : (ZMod N)ˣ, M7.CyclicSubstitution.RootCondition u'),
('point_one',['power_mod'],f+point+' (1 : (ZMod N)ˣ) = '+rho),
('point_mul',['power_mod'],f+'∀ u v : (ZMod N)ˣ, '+point+' u ^ (v : ZMod N).val = '+point+' (v*u)'),
('point_inverse',['point_mul','point_one'],f+'∀ u : (ZMod N)ˣ, '+point+' u ^ ((u⁻¹ : (ZMod N)ˣ) : ZMod N).val = '+rho),
('hom_root',[],f+'∀ (u : (ZMod N)ˣ) (h : M7.CyclicSubstitution.RootCondition u), M7.CyclicSubstitution.hom u h ('+rho+') = '+point+' u'),
('hom_polynomial',[],f+'∀ (u : (ZMod N)ˣ) (h : M7.CyclicSubstitution.RootCondition u) (p : M6.Cyclic.BinaryPolynomial), M7.CyclicSubstitution.hom u h (M6.Cyclic.image N p) = p.eval₂ (AdjoinRoot.of (M6.Cyclic.modulus N)) ('+point+' u)')]
g={'title':'M7 actual cyclic quotient substitution foundation, including even N and N=1','nodes':[{'id':i,'dependencies':deps,'spec':{'name':'M7.CyclicSubstitution.'+i,'statement':s,'imports':['M7CyclicSubstitution'],'context':'','queries':['addition commutativity'],'guidance':'Use actual AdjoinRoot(X^N+1) over ZMod2. root_power follows eval₂_root and characteristic2; pow_mod follows k=k%N+N*(k/N); point_mul uses ZMod.val_mul and commutativity. Includes N=1: unit.val can be0, but rho=1. AdjoinRoot.lift_root/lift_mk prove hom interfaces. No odd-N, squarefree or field quotient assumption. Return tactic lines only.\n'+source}}for i,deps,s in items]}
(b/'graph.json').write_text(json.dumps(g,indent=2)+'\n');(p/'Preflight.lean').write_text('import M7CyclicSubstitution\n'+''.join('def target_'+str(j)+' : Prop := '+s+'\n'for j,(_,_,s)in enumerate(items)))
(b/'IMPORT_PROVENANCE.json').write_text(json.dumps({'source':'../domain/lean/M6Cyclic.lean','sha256':h,'verified_against_canonical_manifest':True,'proof_imports':[]},indent=2)+'\n')
(b/'SCOPE.md').write_text('# Cyclic quotient substitution foundation\n\nEight exact targets establish the actual root period and unit-power identities, prove each unit power is a root of the full modulus, and expose the quotient lift on the root and arbitrary polynomials. `hom` takes its well-definedness proof as a dependent argument only at this intermediate stage; `point_root` proves that obligation universally. The next adapter must supply this accepted proof, and prove inverse/composition before claiming a ring equivalence. Literal full-gcd signature transport and degree preservation remain downstream. No full M7 acceptance is claimed.\n')
print('prepared8 targets with verified actual M6 cyclic definitions')
