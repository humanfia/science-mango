from pathlib import Path
import json,hashlib,shutil
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');src=repo/'pipelines/quantum_formalize/examples/m7/cyclic_substitution';b=repo/'pipelines/quantum_formalize/examples/m7/quotient_auto';p=Path('/home/jing/m7-lean-quotient-auto-formalization');p.mkdir(exist_ok=True);(b/'lean').mkdir(parents=True,exist_ok=True);manifest=json.loads((src/'experiment/MANIFEST.json').read_text());env=json.loads((src/'experiment/environment.json').read_text())
for n,h in manifest.items():assert hashlib.sha256((src/'experiment'/n).read_bytes()).hexdigest()==h,n
for name in ['M6Cyclic','M7CyclicSubstitution']:
 f=src/'lean'/(name+'.lean');assert hashlib.sha256(f.read_bytes()).hexdigest()==env[f.name];shutil.copy2(f,p/f.name);shutil.copy2(f,b/'lean'/f.name)
a=src/'experiment/AcceptedExperiment.lean';shutil.copy2(a,p/'M7CyclicSubstitutionAccepted.lean');shutil.copy2(a,b/'lean/M7CyclicSubstitutionAccepted.lean')
source='''import M7CyclicSubstitutionAccepted

namespace M7.QuotientAuto
noncomputable def substitution {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) :
    M6.Cyclic.CycleRing N →+* M6.Cyclic.CycleRing N :=
  M7.CyclicSubstitution.hom u (M7.CyclicSubstitution.point_root N u)
end M7.QuotientAuto
'''
(p/'M7QuotientAuto.lean').write_text(source);(b/'lean/M7QuotientAuto.lean').write_text(source)
for n in ['lake-manifest.json','lean-toolchain']:shutil.copy2(src/n,p/n);shutil.copy2(src/n,b/n)
s=(src/'lakefile.toml').read_text().replace('name = "M7CyclicSubstitution"\nversion','name = "M7QuotientAuto"\nversion').replace('defaultTargets = ["M7CyclicSubstitution"]','defaultTargets = ["M7QuotientAuto"]')+'\n[[lean_lib]]\nname = "M7CyclicSubstitutionAccepted"\n\n[[lean_lib]]\nname = "M7QuotientAuto"\n';(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
f='∀ (N : ℕ) [NeZero N], ';su='M7.QuotientAuto.substitution';rho='M7.CyclicSubstitution.rho N';ring='M6.Cyclic.CycleRing N';of='AdjoinRoot.of (M6.Cyclic.modulus N)'
items=[
('substitution_root',[],f+'∀ u : (ZMod N)ˣ, '+su+' u ('+rho+') = M7.CyclicSubstitution.point u'),
('substitution_scalars',[],f+'∀ (u : (ZMod N)ˣ) (r : ZMod 2), '+su+' u (('+of+') r) = ('+of+') r'),
('substitution_one',['substitution_root','substitution_scalars'],f+su+' (1 : (ZMod N)ˣ) = RingHom.id ('+ring+')'),
('substitution_comp',['substitution_root','substitution_scalars'],f+'∀ u v : (ZMod N)ˣ, ('+su+' v).comp ('+su+' u) = '+su+' (v*u)'),
('substitution_left_inverse',['substitution_comp','substitution_one'],f+'∀ (u : (ZMod N)ˣ) (x : '+ring+'), '+su+' (u⁻¹) ('+su+' u x) = x'),
('substitution_right_inverse',['substitution_comp','substitution_one'],f+'∀ (u : (ZMod N)ˣ) (x : '+ring+'), '+su+' u ('+su+' (u⁻¹) x) = x'),
('substitution_bijective',['substitution_left_inverse','substitution_right_inverse'],f+'∀ u : (ZMod N)ˣ, Function.Bijective ('+su+' u)'),
('polynomial_substitution',[],f+'∀ (u : (ZMod N)ˣ) (p : M6.Cyclic.BinaryPolynomial), M6.Cyclic.image N (p.comp (Polynomial.X ^ (u : ZMod N).val)) = '+su+' u (M6.Cyclic.image N p)')]
g={'title':'M7 actual quotient unit substitutions: composition, inverses and polynomial action','nodes':[{'id':i,'dependencies':deps,'spec':{'name':'M7.QuotientAuto.'+i,'statement':s,'imports':['M7QuotientAuto'],'context':'','queries':['algebra'],'guidance':'substitution supplies the accepted point_root proof itself: no free well-definedness assumption. AdjoinRoot.ringHom_ext checks coefficients via comp(of) and root; hom_root/hom_polynomial and point_one/point_mul/point_inverse are accepted. AdjoinRoot.lift_of takes the root-condition proof explicitly (other arguments implicit). For composition use map_pow and point_mul, with commutativity of units. Polynomial composition evaluates at rho^u.val; preserve quotient ring type instead of globally unfolding modulus under its type. Covers N=1 and nonreduced even-N quotient. Return tactic lines only.\n'+source}}for i,deps,s in items]};(b/'graph.json').write_text(json.dumps(g,indent=2)+'\n');(p/'Preflight.lean').write_text('import M7QuotientAuto\n'+''.join('def target_'+str(j)+' : Prop := '+s+'\n'for j,(_,_,s)in enumerate(items)));(b/'IMPORT_PROVENANCE.json').write_text(json.dumps({'parent':'../cyclic_substitution','verified_canonical_files':len(manifest),'all_sources_match_accepted_environment':True,'accepted_source_sha256':hashlib.sha256(a.read_bytes()).hexdigest()},indent=2)+'\n');(b/'SCOPE.md').write_text('# Actual quotient automorphism laws\n\nEight targets prove concrete unit substitution fixes scalars, composes and has its actual inverse, and agrees with polynomial substitution. Well-definedness is supplied by the accepted universal point_root theorem. RingEquiv packaging and the full signature/degree interface are downstream. No full M7 acceptance is claimed.\n');print('prepared8 concrete quotient substitution targets')
