from pathlib import Path
import json,hashlib,shutil
repo=Path('/home/jing/science-mango-quantum-harness-publish-20260914');root=repo/'pipelines/quantum_formalize/examples/m7';b=root/'affine_polynomial';p=Path('/home/jing/m7-lean-affine-polynomial-formalization');p.mkdir(exist_ok=True);(b/'lean').mkdir(parents=True,exist_ok=True);verified={}
for module,names in [('group',['M7Action','M7ActionAccepted']),('supports',['M7Supports']),('cyclic_substitution',['M6Cyclic','M7CyclicSubstitution'])]:
 src=root/module;env=json.loads((src/'experiment/environment.json').read_text())
 for name in names:
  f=src/'lean'/(name+'.lean');h=hashlib.sha256(f.read_bytes()).hexdigest();assert h==env[f.name];verified[module+'/'+f.name]=h;shutil.copy2(f,p/f.name);shutil.copy2(f,b/'lean'/f.name)
src=root/'cyclic_substitution';a=src/'experiment/AcceptedExperiment.lean';m=json.loads((src/'experiment/MANIFEST.json').read_text());assert hashlib.sha256(a.read_bytes()).hexdigest()==m['AcceptedExperiment.lean'];shutil.copy2(a,p/'M7CyclicSubstitutionAccepted.lean');shutil.copy2(a,b/'lean/M7CyclicSubstitutionAccepted.lean');verified['cyclic_substitution/AcceptedExperiment.lean']=hashlib.sha256(a.read_bytes()).hexdigest()
f=root/'quotient_auto/lean/M7QuotientAuto.lean';h=hashlib.sha256(f.read_bytes()).hexdigest();pf=json.loads((root/'quotient_auto/PREFLIGHT.json').read_text());assert h==pf['source_sha256'] and pf['accepted'];shutil.copy2(f,p/f.name);shutil.copy2(f,b/'lean'/f.name);verified['quotient_auto/definition_only']=h
source='''import M7ActionAccepted
import M7Supports
import M7QuotientAuto

namespace M7.AffinePolynomial
noncomputable def image {N : ℕ} (A : M7.Supports.Support N) : M6.Cyclic.CycleRing N :=
  M6.Cyclic.image N (M7.Supports.polynomial A)
noncomputable def shifted {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) (s : ZMod N)
    (A : M7.Supports.Support N) : M7.Supports.Support N := A.image (M7.Action.affine u s)
end M7.AffinePolynomial
''';(p/'M7AffinePolynomial.lean').write_text(source);(b/'lean/M7AffinePolynomial.lean').write_text(source);base=root/'canonical_block'
for n in ['lake-manifest.json','lean-toolchain']:shutil.copy2(base/n,p/n);shutil.copy2(base/n,b/n)
s=(base/'lakefile.toml').read_text().replace('M7CanonicalBlock','M7AffinePolynomial')+''.join('\n[[lean_lib]]\nname = '+json.dumps(f.stem)+'\n'for f in sorted(p.glob('*.lean'))if f.stem!='M7AffinePolynomial');(p/'lakefile.toml').write_text(s);shutil.copy2(p/'lakefile.toml',b/'lakefile.toml');(p/'.lake').mkdir(exist_ok=True)
if not(p/'.lake/packages').exists():(p/'.lake/packages').symlink_to('/home/jing/lean-1st-proof/.lake/packages',target_is_directory=True)
f='∀ (N : ℕ) [NeZero N], ';rho='M7.CyclicSubstitution.rho N';pt='M7.CyclicSubstitution.point';im='M7.AffinePolynomial.image';su='M7.QuotientAuto.substitution';S='M7.Supports.Support N'
items=[
('support_sum',[],f+'∀ A : '+S+', '+im+' A = ∑ i ∈ A, '+rho+' ^ i.val'),
('substitution_support_sum',['support_sum'],f+'∀ (u : (ZMod N)ˣ) (A : '+S+'), '+su+' u ('+im+' A) = ∑ i ∈ A, '+pt+' u ^ i.val'),
('rho_add_val',[],f+'∀ x y : ZMod N, '+rho+' ^ (x+y).val = '+rho+' ^ x.val * '+rho+' ^ y.val'),
('rho_mul_val',[],f+'∀ (u : (ZMod N)ˣ) (x : ZMod N), '+rho+' ^ ((u : ZMod N)*x).val = '+pt+' u ^ x.val'),
('image_affine',['support_sum','substitution_support_sum','rho_add_val','rho_mul_val'],f+'∀ (u : (ZMod N)ˣ) (s : ZMod N) (A : '+S+'), '+im+' (M7.AffinePolynomial.shifted u s A) = '+rho+' ^ s.val * '+su+' u ('+im+' A)'),
('rho_power_unit',[],f+'∀ s : ZMod N, IsUnit ('+rho+' ^ s.val)'),
('action_images',['image_affine'],f+'∀ (g : M7.Action.Record N) (c : M7.Action.Recipe N), '+im+' (M7.Action.act g c).1 = '+rho+' ^ g.leftShift.val * '+su+' g.unit ('+im+' (if g.exchange then c.2 else c.1)) ∧ '+im+' (M7.Action.act g c).2 = '+rho+' ^ g.rightShift.val * '+su+' g.unit ('+im+' (if g.exchange then c.1 else c.2))')]
g={'title':'M7 literal affine support action as unit multiplication and actual quotient substitution','nodes':[{'id':i,'dependencies':deps,'spec':{'name':'M7.AffinePolynomial.'+i,'statement':s,'imports':['M7AffinePolynomial'],'context':'','queries':['algebra'],'guidance':'All imported proof obligations are accepted. Only the frozen substitution definition is imported from quotient_auto, not its pending laws: unfold it and use accepted CyclicSubstitution.hom_root with point_root. support_sum follows map_sum and AdjoinRoot.mk_X. Use accepted power_mod with ZMod.val_add/val_mul for powers of residue values. affine_bijective justifies Finset.sum_image, so no cancellations/duplicate supports are assumed. rho is a unit since rho^N=1 and N>0, hence all shift powers are units. Covers even N and N=1. Return tactic lines only.\n'+source}}for i,deps,s in items]};(b/'graph.json').write_text(json.dumps(g,indent=2)+'\n');(p/'Preflight.lean').write_text('import M7AffinePolynomial\n'+''.join('def target_'+str(j)+' : Prop := '+s+'\n'for j,(_,_,s)in enumerate(items)));(b/'IMPORT_PROVENANCE.json').write_text(json.dumps({'verified_import_hashes':verified,'pending_proof_imports':[],'quotient_auto_import':'Frozen definition only; its RootCondition is supplied by accepted point_root, not a pending theorem'},indent=2)+'\n');(b/'SCOPE.md').write_text('# Literal affine action on support polynomials\n\nSeven targets prove that actual affine support images map in the actual cyclic quotient to shift units times concrete unit substitution. This supplies the literal-support interface for the full-signature ideal transport. Only accepted proofs and the already compiled frozen substitution definition are imported. Full signature equality and degree preservation remain downstream.\n');print('prepared7 exact affine support-polynomial targets')
